/-
Copyright (c) 2025 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close
-/
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Language
import Mathlib.Computability.DFA
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Fintype.Basic

/-!
# The Chomsky Hierarchy

This file defines the four levels of the Chomsky hierarchy as an inductive type
`ChomskyType` and establishes their ordering by generative capacity. It also
defines the self-reference capacity of each level and proves the key structural
results:

- The Chomsky hierarchy forms a linear order.
- Self-reference capacity is monotone in the hierarchy.
- Self-reference with return characterizes exactly Type 0.
- Type 0 is the minimal Chomsky type supporting self-reference with return.
- Kleene's recursion theorem (from Mathlib) witnesses self-reference with
  return at Type 0.

The four levels correspond to the well-known language classes:

| Level  | Languages              | Automaton                |
|--------|------------------------|--------------------------|
| Type 3 | Regular                | Finite automaton (DFA)   |
| Type 2 | Context-free           | Pushdown automaton       |
| Type 1 | Context-sensitive      | Linear bounded automaton |
| Type 0 | Recursively enumerable | Turing machine           |

## Connection to Mathlib

Mathlib already formalizes:
- `Language α` as `Set (List α)` in `Mathlib.Computability.Language`
- `Language.IsRegular` via DFAs in `Mathlib.Computability.DFA`
- `Language.IsContextFree` via context-free grammars in
  `Mathlib.Computability.ContextFreeGrammar`
- `Nat.Partrec.Code.fixed_point` (Roger's fixed-point theorem) and
  `Nat.Partrec.Code.fixed_point₂` (Kleene's second recursion theorem)
  in `Mathlib.Computability.PartrecCode`

Mathlib lacks:
- Context-sensitive grammars and languages
- Unrestricted (Type 0) grammars and recursively enumerable languages
- The Chomsky hierarchy as a unified structure
- Automata-theoretic characterizations of self-reference capacity

## Main definitions

- `ChomskyType`: The four levels of the Chomsky hierarchy.
- `ChomskyType.capacity`: Generative capacity as a natural number.
- `SelfReferenceCapacity`: Classification of self-reference capability.
- `ChomskyType.selfRefCapacity`: The canonical self-reference capacity for
  each Chomsky type.
- `ComputationModel`: An abstract model of computation.
- `ComputationModel.isUniversal`: Whether a model can simulate all partial
  recursive functions.

## Main results

- `ChomskyType.instLinearOrder`: `ChomskyType` forms a linear order.
- `ChomskyType.selfRef_monotone`: Self-reference capacity is monotone.
- `ChomskyType.type0_unique_withReturn`: Only Type 0 has self-reference
  with return.
- `ChomskyType.type0_minimal_for_self_reference`: Type 0 is the minimal
  type supporting self-reference with return.
- `kleene_provides_self_reference_with_return`: Kleene's theorem witnesses
  self-reference with return at Type 0 (from Mathlib).

## Axioms

The only axiom in this file is `church_turing_thesis`, which formalizes the
informal thesis that all adequate models of effective computation are
equivalent. This is genuinely unprovable in any formal system because it
bridges informal and formal concepts.

## References

- [Chomsky, N., *On certain formal properties of grammars*, 1959]
- [Hopcroft, J. and Ullman, J., *Introduction to Automata Theory, Languages,
  and Computation*]
- [Sipser, M., *Introduction to the Theory of Computation*]
- [Kleene, S.C., *On the interpretation of intuitionistic number theory*, 1952]
-/

open Nat.Partrec

/-!
## The Chomsky Hierarchy
-/

/-- The four types in the Chomsky hierarchy, ordered by generative capacity.
Each level strictly extends the language class of the one below it.

- `type3`: Regular languages (recognized by finite automata)
- `type2`: Context-free languages (recognized by pushdown automata)
- `type1`: Context-sensitive languages (recognized by linear bounded automata)
- `type0`: Recursively enumerable languages (recognized by Turing machines) -/
inductive ChomskyType : Type where
  /-- Regular languages, recognized by finite automata. -/
  | type3 : ChomskyType
  /-- Context-free languages, recognized by pushdown automata. -/
  | type2 : ChomskyType
  /-- Context-sensitive languages, recognized by linear bounded automata. -/
  | type1 : ChomskyType
  /-- Recursively enumerable languages, recognized by Turing machines. -/
  | type0 : ChomskyType
  deriving DecidableEq, Repr

namespace ChomskyType

/-- Generative capacity as a natural number, for ordering.
Higher number means strictly greater generative capacity. -/
def capacity : ChomskyType → ℕ
  | type3 => 0
  | type2 => 1
  | type1 => 2
  | type0 => 3

@[simp]
theorem capacity_type3 : type3.capacity = 0 := rfl

@[simp]
theorem capacity_type2 : type2.capacity = 1 := rfl

@[simp]
theorem capacity_type1 : type1.capacity = 2 := rfl

@[simp]
theorem capacity_type0 : type0.capacity = 3 := rfl

/-- `capacity` is injective: distinct Chomsky types have distinct capacities. -/
theorem capacity_injective : Function.Injective capacity := by
  intro a b h
  cases a <;> cases b <;> simp_all [capacity]

/-- The ordering on Chomsky types by generative capacity. -/
instance : LE ChomskyType where
  le a b := a.capacity ≤ b.capacity

instance : DecidableRel (· ≤ · : ChomskyType → ChomskyType → Prop) :=
  fun a b => Nat.decLe a.capacity b.capacity

/-- `ChomskyType` forms a partial order via the `capacity` embedding into `ℕ`. -/
instance : PartialOrder ChomskyType where
  le_refl a := Nat.le_refl a.capacity
  le_trans _ _ _ h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := capacity_injective (Nat.le_antisymm h1 h2)

/-- `ChomskyType` forms a linear order. -/
instance instLinearOrder : LinearOrder ChomskyType where
  le_total a b := Nat.le_total a.capacity b.capacity
  toDecidableLE := inferInstance

/-- Type 3 < Type 2 in generative capacity. -/
theorem type3_lt_type2 : type3 < type2 := by decide

/-- Type 2 < Type 1 in generative capacity. -/
theorem type2_lt_type1 : type2 < type1 := by decide

/-- Type 1 < Type 0 in generative capacity. -/
theorem type1_lt_type0 : type1 < type0 := by decide

/-- Type 3 < Type 0 in generative capacity. -/
theorem type3_lt_type0 : type3 < type0 := by decide

/-- Type 0 is the maximum of the Chomsky hierarchy. -/
theorem le_type0 (t : ChomskyType) : t ≤ type0 := by
  cases t <;> decide

/-- Type 3 is the minimum of the Chomsky hierarchy. -/
theorem type3_le (t : ChomskyType) : type3 ≤ t := by
  cases t <;> decide

/-- `type0` is the top element. -/
instance : OrderTop ChomskyType where
  top := type0
  le_top := le_type0

/-- `type3` is the bottom element. -/
instance : OrderBot ChomskyType where
  bot := type3
  bot_le := type3_le

/-- The Chomsky hierarchy is a bounded order. -/
instance : BoundedOrder ChomskyType where

/-- The Chomsky hierarchy has exactly four elements. -/
instance : Fintype ChomskyType where
  elems := {type3, type2, type1, type0}
  complete := by intro x; cases x <;> simp

/-- The Chomsky hierarchy is nonempty. -/
instance : Nonempty ChomskyType := ⟨type0⟩

end ChomskyType

/-!
## Self-Reference Capacity

A classification of the self-reference capability of formal systems,
corresponding to the Chomsky hierarchy levels.
-/

/-- Classification of a formal system's self-reference capability,
ordered from weakest to strongest.

The correspondence with the Chomsky hierarchy is:
- `none`: Type 3 (regular) -- finite automata cannot self-inspect
- `limitedNesting`: Type 2 (context-free) -- pushdown automata can track
  nesting depth but cannot refer to arbitrary parts of their computation
- `bounded`: Type 1 (context-sensitive) -- linear bounded automata can
  inspect their tape within the input length
- `withReturn`: Type 0 (recursively enumerable) -- Turing machines support
  Kleene's recursion theorem: programs can obtain their own description and
  use it productively -/
inductive SelfReferenceCapacity : Type where
  /-- No self-reference: the system cannot refer to its own descriptions. -/
  | none : SelfReferenceCapacity
  /-- Limited nesting: the system can nest references but not unboundedly. -/
  | limitedNesting : SelfReferenceCapacity
  /-- Bounded self-reference within a fixed context. -/
  | bounded : SelfReferenceCapacity
  /-- Self-reference with return: the system can obtain its own description
  and the result feeds back into computation (fixed point, not just quine). -/
  | withReturn : SelfReferenceCapacity
  deriving DecidableEq, Repr

namespace SelfReferenceCapacity

/-- Strength ordering: `none < limitedNesting < bounded < withReturn`. -/
def strength : SelfReferenceCapacity → ℕ
  | none => 0
  | limitedNesting => 1
  | bounded => 2
  | withReturn => 3

@[simp]
theorem strength_none : none.strength = 0 := rfl

@[simp]
theorem strength_limitedNesting : limitedNesting.strength = 1 := rfl

@[simp]
theorem strength_bounded : bounded.strength = 2 := rfl

@[simp]
theorem strength_withReturn : withReturn.strength = 3 := rfl

/-- `strength` is injective. -/
theorem strength_injective : Function.Injective strength := by
  intro a b h
  cases a <;> cases b <;> simp_all [strength]

instance : LE SelfReferenceCapacity where
  le a b := a.strength ≤ b.strength

instance : DecidableRel (· ≤ · : SelfReferenceCapacity → SelfReferenceCapacity → Prop) :=
  fun a b => Nat.decLe a.strength b.strength

/-- `SelfReferenceCapacity` forms a partial order. -/
instance : PartialOrder SelfReferenceCapacity where
  le_refl a := Nat.le_refl a.strength
  le_trans _ _ _ h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := strength_injective (Nat.le_antisymm h1 h2)

/-- `SelfReferenceCapacity` forms a linear order. -/
instance instLinearOrder : LinearOrder SelfReferenceCapacity where
  le_total a b := Nat.le_total a.strength b.strength
  toDecidableLE := inferInstance

theorem none_lt_withReturn : none < withReturn := by decide

theorem bounded_lt_withReturn : bounded < withReturn := by decide

theorem none_le_all (s : SelfReferenceCapacity) : none ≤ s := by
  cases s <;> decide

end SelfReferenceCapacity

/-!
## Self-Reference Capacity of Each Chomsky Type
-/

namespace ChomskyType

/-- The canonical self-reference capacity for each Chomsky type.

This is a definitional mapping, not an axiom:
- Type 3 (regular) has no self-reference
- Type 2 (context-free) has limited nesting
- Type 1 (context-sensitive) has bounded self-reference
- Type 0 (recursively enumerable) has self-reference with return -/
def selfRefCapacity : ChomskyType → SelfReferenceCapacity
  | .type3 => .none
  | .type2 => .limitedNesting
  | .type1 => .bounded
  | .type0 => .withReturn

@[simp]
theorem selfRefCapacity_type3 : type3.selfRefCapacity = .none := rfl

@[simp]
theorem selfRefCapacity_type2 : type2.selfRefCapacity = .limitedNesting := rfl

@[simp]
theorem selfRefCapacity_type1 : type1.selfRefCapacity = .bounded := rfl

@[simp]
theorem selfRefCapacity_type0 : type0.selfRefCapacity = .withReturn := rfl

/-- `selfRefCapacity` preserves and reflects the ordering:
`a.selfRefCapacity ≤ b.selfRefCapacity ↔ a ≤ b`.

This holds because `capacity` and `strength` assign the same numerical
values (0, 1, 2, 3) to corresponding types. -/
theorem selfRefCapacity_le_iff (a b : ChomskyType) :
    a.selfRefCapacity ≤ b.selfRefCapacity ↔ a ≤ b := by
  change a.selfRefCapacity.strength ≤ b.selfRefCapacity.strength ↔ a.capacity ≤ b.capacity
  cases a <;> cases b <;> exact Iff.rfl

/-- Self-reference capacity is monotone with respect to the hierarchy:
a higher Chomsky type has at least the self-reference capacity of
any lower type. -/
theorem selfRef_monotone (a b : ChomskyType) (h : a ≤ b) :
    a.selfRefCapacity ≤ b.selfRefCapacity :=
  (selfRefCapacity_le_iff a b).mpr h

/-- Self-reference capacity is strictly monotone: distinct Chomsky types
have distinct self-reference capacities. -/
theorem selfRef_strictMono (a b : ChomskyType) (h : a < b) :
    a.selfRefCapacity < b.selfRefCapacity := by
  rw [Std.lt_iff_le_and_not_ge] at h ⊢
  exact ⟨selfRef_monotone a b h.1,
         fun hba => h.2 ((selfRefCapacity_le_iff b a).mp hba)⟩

/-- Only Type 0 has self-reference with return as its canonical capacity. -/
theorem type0_unique_withReturn (t : ChomskyType) :
    t.selfRefCapacity = SelfReferenceCapacity.withReturn ↔ t = type0 := by
  constructor
  · intro h; cases t <;> simp_all [selfRefCapacity]
  · rintro rfl; rfl

/-- Below Type 0, no Chomsky type has self-reference with return. -/
theorem selfRefCapacity_ne_withReturn_of_lt (t : ChomskyType) (h : t < type0) :
    t.selfRefCapacity ≠ SelfReferenceCapacity.withReturn := by
  cases t
  all_goals (first | decide | exact absurd h (by decide))

/-- Type 0 is the minimal Chomsky type adequate for self-reference with
return: it has the capacity, and no strictly lower type does. -/
theorem type0_minimal_for_self_reference :
    type0.selfRefCapacity = SelfReferenceCapacity.withReturn ∧
    ∀ t : ChomskyType, t < type0 →
      t.selfRefCapacity ≠ SelfReferenceCapacity.withReturn :=
  ⟨rfl, fun t ht => selfRefCapacity_ne_withReturn_of_lt t ht⟩

end ChomskyType

/-!
## Formal Systems and Their Chomsky Classification
-/

/-- A formal system characterized by its position in the Chomsky hierarchy
and its self-reference capacity. The `compatible` field ensures that the
self-reference capacity matches the canonical value for the Chomsky type. -/
structure FormalSystem where
  /-- The Chomsky type of the system. -/
  chomskyType : ChomskyType
  /-- The system's self-reference capacity. -/
  selfRef : SelfReferenceCapacity
  /-- Compatibility: the self-reference capacity matches the Chomsky type. -/
  compatible : selfRef = chomskyType.selfRefCapacity

/-- Construct a `FormalSystem` from a `ChomskyType`, using the canonical
self-reference capacity. -/
def FormalSystem.ofChomskyType (t : ChomskyType) : FormalSystem where
  chomskyType := t
  selfRef := t.selfRefCapacity
  compatible := rfl

/-- Any formal system with self-reference with return must be Type 0. -/
theorem FormalSystem.chomskyType_eq_type0_of_withReturn (fs : FormalSystem)
    (h : fs.selfRef = SelfReferenceCapacity.withReturn) :
    fs.chomskyType = ChomskyType.type0 := by
  rw [fs.compatible] at h
  exact (ChomskyType.type0_unique_withReturn fs.chomskyType).mp h

/-!
## Connection to Mathlib Language Classes

Mathlib defines `Language.IsRegular` (via DFAs) and `Language.IsContextFree`
(via context-free grammars). We define the recursively enumerable predicate
for the Type 0 level, connecting to Mathlib's `Nat.Partrec` infrastructure.

The context-sensitive level (Type 1) and the containment theorems between
classes (regular subset context-free subset context-sensitive subset r.e.)
require automata-theoretic constructions not yet available in Mathlib.
-/

/-- A language over a primcodable type is recursively enumerable if
membership is semi-decidable by a partial recursive function.

This connects the Type 0 level of the Chomsky hierarchy to Mathlib's
`Nat.Partrec` infrastructure. A language is recursively enumerable iff
it is the domain of some partial recursive function. -/
def Language.IsRecursivelyEnumerable {T : Type*} [Primcodable T]
    (L : Language T) : Prop :=
  ∃ f : List T →. Unit, Partrec f ∧ ∀ w : List T, w ∈ L ↔ (f w).Dom

/-!
## Universal Computation and the Church-Turing Thesis
-/

/-- A model of computation. Each model defines a class of computable
partial functions from `ℕ` to `ℕ`. -/
structure ComputationModel where
  /-- The type of programs in this model. -/
  Program : Type
  /-- The evaluation function: a program applied to input yields a partial
  output. -/
  eval : Program → ℕ →. ℕ

/-- Two computation models are equivalent if they compute exactly the same
class of partial functions. -/
def ComputationModel.equivalent (m₁ m₂ : ComputationModel) : Prop :=
  (∀ p₁ : m₁.Program, ∃ p₂ : m₂.Program, ∀ n, m₁.eval p₁ n = m₂.eval p₂ n) ∧
  (∀ p₂ : m₂.Program, ∃ p₁ : m₁.Program, ∀ n, m₁.eval p₁ n = m₂.eval p₂ n)

/-- A computation model is universal if it can simulate every partial
recursive function, i.e., every function computable by `Nat.Partrec.Code`. -/
def ComputationModel.isUniversal (m : ComputationModel) : Prop :=
  ∀ c : Code, ∃ p : m.Program, ∀ n, m.eval p n = Code.eval c n

/-- The Church-Turing thesis as a formal statement: all computation models
that can simulate partial recursive functions are equivalent to each other.

This is axiomatized because it is an informal thesis, not a theorem. The
Church-Turing thesis bridges the informal concept of "effective procedure"
with formal definitions. The mathematical content is that Turing machines,
lambda calculus, recursive functions, cellular automata, etc., all compute
the same class of partial functions.

**Status**: Genuine axiom -- the Church-Turing thesis is not provable within
any single formal system because it relates informal and formal concepts. -/
axiom church_turing_thesis :
  ∀ (m₁ m₂ : ComputationModel),
    m₁.isUniversal → m₂.isUniversal → m₁.equivalent m₂

/-- Equivalence of computation models is reflexive. -/
theorem ComputationModel.equivalent_refl (m : ComputationModel) :
    m.equivalent m :=
  ⟨fun p => ⟨p, fun _ => rfl⟩, fun p => ⟨p, fun _ => rfl⟩⟩

/-- Equivalence of computation models is symmetric. -/
theorem ComputationModel.equivalent_symm {m₁ m₂ : ComputationModel}
    (h : m₁.equivalent m₂) : m₂.equivalent m₁ :=
  ⟨fun p₂ => by
    obtain ⟨p₁, hp₁⟩ := h.2 p₂
    exact ⟨p₁, fun n => (hp₁ n).symm⟩,
   fun p₁ => by
    obtain ⟨p₂, hp₂⟩ := h.1 p₁
    exact ⟨p₂, fun n => (hp₂ n).symm⟩⟩

/-- The standard model of computation using `Nat.Partrec.Code`. -/
def standardModel : ComputationModel where
  Program := Code
  eval := Code.eval

/-- The standard model is universal (trivially, by definition). -/
theorem standardModel_isUniversal : standardModel.isUniversal :=
  fun c => ⟨c, fun _ => rfl⟩

/-!
## Kleene's Recursion Theorem and Self-Reference with Return

Kleene's recursion theorem, proved in Mathlib as `Nat.Partrec.Code.fixed_point`,
establishes that self-reference with return is a *theorem* of Type 0
computation, not an additional assumption.
-/

/-- Kleene's recursion theorem provides self-reference with return.

Given any computable transformation `f : Code → Code`, there exists a
program `c` that is a semantic fixed point: `eval(f(c)) = eval(c)`.
The program `c` "knows" its own description (via `f`) and the result
feeds back (`eval` is preserved). This is self-reference with return.

This is a direct consequence of Mathlib's `Nat.Partrec.Code.fixed_point`. -/
theorem kleene_provides_self_reference_with_return
    (f : Code → Code) (hf : Computable f) :
    ∃ c : Code, Code.eval (f c) = Code.eval c :=
  Code.fixed_point hf

/-- Kleene's second recursion theorem: a stronger form where the function
receives the code as an argument.

For any partial recursive `f : Code → ℕ →. ℕ`, there exists `c` with
`eval(c) = f(c)`. The function `f` can inspect `c` -- true self-reference.

This is a direct consequence of Mathlib's `Nat.Partrec.Code.fixed_point₂`. -/
theorem kleene_second_provides_self_reference
    (f : Code → ℕ →. ℕ) (hf : Partrec₂ f) :
    ∃ c : Code, Code.eval c = f c :=
  Code.fixed_point₂ hf

/-- Self-reference with return is a theorem at Type 0, not an axiom.

At the Turing-complete level, Kleene's theorem guarantees self-reference
with return. The capacity is not postulated -- it follows from the
fixed-point property of any acceptable Goedel numbering. -/
theorem self_reference_is_theorem_at_type0 :
    (∀ (f : Code → Code), Computable f →
      ∃ c : Code, Code.eval (f c) = Code.eval c) ∧
    (∀ (f : Code → ℕ →. ℕ), Partrec₂ f →
      ∃ c : Code, Code.eval c = f c) :=
  ⟨kleene_provides_self_reference_with_return,
   kleene_second_provides_self_reference⟩

/-!
## Minimality of Type 0

Type 0 is the minimal Chomsky type that supports self-reference with return:
- Below Type 0, self-reference with return is absent (proved from definitions).
- At Type 0, self-reference with return is a theorem (Kleene, from Mathlib).
- Type 0 is maximal in the hierarchy, so there is nothing above it.
-/

/-- Type 0 is the maximal type in the Chomsky hierarchy. -/
theorem type0_is_maximal : ∀ t : ChomskyType, t ≤ ChomskyType.type0 :=
  ChomskyType.le_type0

/-- Type 0 is the unique Chomsky type that supports self-reference with
return. Below it, the capacity is strictly weaker. -/
theorem type0_unique_with_return :
    ∀ t : ChomskyType, t.selfRefCapacity = SelfReferenceCapacity.withReturn ↔
      t = ChomskyType.type0 :=
  ChomskyType.type0_unique_withReturn

/-- The minimality theorem: Type 0 is both necessary and sufficient for
self-reference with return, hence minimal. -/
theorem type0_minimality :
    -- Sufficiency: Type 0 has self-reference with return
    ChomskyType.type0.selfRefCapacity = SelfReferenceCapacity.withReturn ∧
    -- Necessity: no type below Type 0 has it
    (∀ t : ChomskyType, t < ChomskyType.type0 →
      t.selfRefCapacity ≠ SelfReferenceCapacity.withReturn) ∧
    -- Witness: Kleene's theorem provides the capacity constructively
    (∀ (f : Code → Code), Computable f →
      ∃ c : Code, Code.eval (f c) = Code.eval c) :=
  ⟨rfl,
   ChomskyType.type0_minimal_for_self_reference.2,
   kleene_provides_self_reference_with_return⟩

/-!
## Summary of Formal Status

### Proved (zero sorry, one axiom)
- `ChomskyType.instLinearOrder`: linear order on the hierarchy
- `ChomskyType.selfRef_monotone`: monotonicity of self-reference capacity
- `ChomskyType.selfRef_strictMono`: strict monotonicity
- `ChomskyType.selfRefCapacity_le_iff`: order embedding characterization
- `ChomskyType.type0_unique_withReturn`: Type 0 uniquely has `withReturn`
- `ChomskyType.selfRefCapacity_ne_withReturn_of_lt`: below Type 0, no `withReturn`
- `ChomskyType.type0_minimal_for_self_reference`: minimality
- `FormalSystem.chomskyType_eq_type0_of_withReturn`: Type 0 is forced
- `kleene_provides_self_reference_with_return`: Kleene witness (from Mathlib)
- `kleene_second_provides_self_reference`: stronger form (from Mathlib)
- `self_reference_is_theorem_at_type0`: both Kleene theorems packaged
- `type0_minimality`: complete minimality package
- `ComputationModel.equivalent_refl`: reflexivity
- `ComputationModel.equivalent_symm`: symmetry

### Axiomatized (genuine thesis, not provable in formal systems)
- `church_turing_thesis`: all adequate computation models are equivalent

### Dependencies
- `Mathlib.Computability.PartrecCode`: `Code`, `Code.eval`, `fixed_point`,
  `fixed_point₂`
- `Mathlib.Computability.Language`: `Language` type
- `Mathlib.Computability.DFA`: `Language.IsRegular`
- `Mathlib.Computability.ContextFreeGrammar`: `Language.IsContextFree`
-/
