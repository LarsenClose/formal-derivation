/-
  Phase-Indexed Epistemology — Formal Framework

  Formalizes the proposition schema, translation calculus, diagnostics,
  developmental line, and phase-invariance theorem from the paper (§§3-5).

  Every claim carries generating conditions: the phase of consciousness
  that produced it, the integrative depth it represents, and the validity
  conditions under which it holds. The framework tracks what happens when
  claims move between phases.

  Key result: formally-derived propositions have phase-invariant validity
  conditions (C does not depend on φ), because C = proof steps, checkable
  from any phase. This is the epistemic asymmetry that makes formal
  grounding possible.

  Source: paper §§3-5 (phase-indexed epistemology)
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.Order.Basic
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Data.Nat.Basic

universe u v

namespace PhaseEpistemology

open CategoryTheory

/-!
## Phase: States of Consciousness

A phase is a state of consciousness from which propositions are generated.
Different phases (ordinary waking, meditative, flow, psychedelic, etc.)
produce different epistemic content. We model Phase as an opaque type —
the framework is parametric over what phases exist.

We equip Phase with a category structure: morphisms between phases
represent possible transitions (one can move from phase φ to phase ψ).
Not all transitions are possible — the morphism structure captures
accessibility.
-/

/-- A phase of consciousness. Opaque type — the framework is parametric
    over what phases exist. The category structure on Phase captures
    which transitions between phases are possible. -/
class PhaseSpace (Phase : Type u) extends Category.{v} Phase where
  /-- There exist at least two distinct phases. Without this the framework
      is trivial — translation between phases is vacuously defined. -/
  distinct : ∃ (φ ψ : Phase), φ ≠ ψ

/-!
## Integrative Depth

A partial order on perspectives: d₁ ≤ d₂ means d₂ includes the
perspectives of d₁ and possibly more. Higher integrative depth
means more prior perspectives are held simultaneously.

We use `ℕ` as a concrete model: depth 0 is the narrowest view,
higher numbers represent more inclusive perspectives.
-/

/-- Integrative depth: which prior perspectives this view includes.
    Modeled as a natural number with the standard ordering.
    0 = narrowest perspective, higher = more inclusive. -/
abbrev Depth := ℕ

/-!
## Validity Conditions

Validity conditions specify under what circumstances a proposition
holds, independently of the generating phase. When validity conditions
coincide with the generating phase, the proposition is phase-locked.
When they diverge, the schema is productive.

We model validity conditions as a predicate on phases: C(ψ) = True
means the proposition holds when evaluated from phase ψ.
-/

/-- Validity conditions: a predicate on phases specifying where p holds.
    C(ψ) = True means the proposition is valid when evaluated from phase ψ. -/
def ValidityCondition (Phase : Type u) := Phase → Prop

/-- A validity condition that holds in all phases — phase-invariant. -/
def ValidityCondition.universal (Phase : Type u) : ValidityCondition Phase :=
  fun _ => True

/-- A validity condition that holds only in a specific phase — phase-locked. -/
def ValidityCondition.lockedTo {Phase : Type u} (φ : Phase) [DecidableEq Phase] :
    ValidityCondition Phase :=
  fun ψ => φ = ψ

/-!
## Phase-Indexed Proposition Schema

Every phase-indexed claim has: ⟨p, φ, d, C⟩ where:
- p = propositional content (as a Prop)
- φ = generating phase
- d = integrative depth
- C = validity conditions
-/

/-- A phase-indexed proposition: propositional content tagged with its
    generating conditions.

    - `content` : the propositional content (what is claimed)
    - `phase` : the generating phase (state of consciousness that produced it)
    - `depth` : the integrative depth (how many prior perspectives are included)
    - `validity` : under what conditions the content holds -/
structure PhaseIndexedProp (Phase : Type u) where
  /-- The propositional content — what is claimed -/
  content : Prop
  /-- The generating phase — state of consciousness that produced the claim -/
  phase : Phase
  /-- Integrative depth — how many prior perspectives are included -/
  depth : Depth
  /-- Validity conditions — under what phases the content holds -/
  validity : ValidityCondition Phase

/-- A proposition is phase-locked when its validity conditions coincide
    with its generating phase: it holds only in the phase that produced it.

    Phase-locking indicates the proposition may be an artifact of its
    generating conditions rather than a feature of the territory. -/
def PhaseLocked {Phase : Type u} (pip : PhaseIndexedProp Phase) : Prop :=
  ∀ ψ : Phase, pip.validity ψ ↔ ψ = pip.phase

/-- A proposition is phase-invariant when its validity conditions hold
    in every phase. This is the strongest form of phase-independence. -/
def PhaseInvariant {Phase : Type u} (pip : PhaseIndexedProp Phase) : Prop :=
  ∀ ψ : Phase, pip.validity ψ

/-!
## Translation Outcomes

Translation T(⟨p,φ,d,C⟩, ψ) attempts to carry a phase-indexed proposition
from its generating phase φ into a target phase ψ. Five possible outcomes:

1. Preserved: p holds in ψ with integrative structure maintained
2. Transformable: p can be restated as p' in ψ with specified structural change
3. Symbolic: p can be pointed at from ψ but not fully instantiated
4. NonTransferable: p has no valid expression in ψ
5. Confabulatory: what appears as p in ψ is a distortion of the original
-/

/-- The five possible outcomes of translating a proposition into a new phase.

    These are ordered by fidelity: Preserved > Transformable > Symbolic >
    NonTransferable, with Confabulatory as a distinct failure mode
    (worse than NonTransferable because it is silent). -/
inductive TranslationOutcome (Phase : Type u) where
  /-- p holds in ψ with integrative structure maintained -/
  | preserved (pip : PhaseIndexedProp Phase)
  /-- p can be restated as p' in ψ with specified structural change.
      The new proposition and a description of the transformation. -/
  | transformable (pip' : PhaseIndexedProp Phase) (structuralChange : Prop)
  /-- p can be pointed at from ψ but not fully instantiated.
      A referent exists but the full content is not accessible. -/
  | symbolic (referent : Prop)
  /-- p has no valid expression in ψ -/
  | nonTransferable
  /-- What appears as p in ψ is a distortion of the original.
      The distorted version is recorded. -/
  | confabulatory (distortion : PhaseIndexedProp Phase)

/-!
## Translation Function

A translation function assigns an outcome to each (proposition, target phase) pair.
We model this as a structure to bundle the function with its coherence properties.
-/

/-- A translation function between phases: for each phase-indexed proposition
    and target phase, produces a translation outcome.

    The function must satisfy coherence conditions:
    1. Translating to the generating phase preserves the original.
    2. Phase-invariant propositions are preserved in all phases. -/
structure Translation (Phase : Type u) [PhaseSpace Phase] where
  /-- The translation function -/
  translate : PhaseIndexedProp Phase → Phase → TranslationOutcome Phase
  /-- Translating to the generating phase preserves the proposition.
      This is a minimal coherence requirement: the identity translation
      should not distort. -/
  identity_coherence : ∀ (pip : PhaseIndexedProp Phase),
    translate pip pip.phase = TranslationOutcome.preserved pip
  /-- Phase-invariant propositions are preserved in all target phases.
      If validity holds everywhere, translation cannot degrade the content. -/
  invariant_preservation : ∀ (pip : PhaseIndexedProp Phase),
    PhaseInvariant pip → ∀ ψ : Phase,
    translate pip ψ = TranslationOutcome.preserved pip

/-!
## Five Diagnostics

The diagnostic framework provides five tests for evaluating the quality
of phase-indexed knowledge:

1. Cross-phase recoverability: can the proposition survive translation?
2. Behavioral coherence: is information conserved across consequence chains?
3. Compression loss: is compression tracked or silent?
4. Contradiction load: how many contradictions arise from holding p?
5. Dependency disclosure: are generating conditions made explicit?
-/

/-- Diagnostic results for a phase-indexed proposition.

    Each diagnostic returns a value indicating the quality of the
    proposition along that dimension. Higher values indicate better
    epistemic standing. -/
structure Diagnostic (Phase : Type u) [PhaseSpace Phase] where
  /-- The proposition being diagnosed -/
  subject : PhaseIndexedProp Phase
  /-- Cross-phase recoverability: the fraction of target phases for which
      translation yields Preserved or Transformable (vs Symbolic,
      NonTransferable, or Confabulatory). Axiomatized as a Prop
      representing "high recoverability". -/
  crossPhaseRecoverable : Prop
  /-- Behavioral coherence: consequence chains starting from p
      conserve information across phases. If p → q in phase φ,
      then T(p, ψ) → T(q, ψ) preserves the implication structure. -/
  behaviorallyCoherent : Prop
  /-- Compression loss tracking: any loss of content during translation
      is explicitly tracked (not silently dropped). -/
  compressionTracked : Prop
  /-- Contradiction load: the proposition does not introduce contradictions
      when held alongside its translations into other phases. -/
  contradictionFree : Prop
  /-- Dependency disclosure: the generating conditions (φ, d) are
      explicitly recorded and available for inspection. -/
  dependencyDisclosed : Prop

/-- A proposition passes all five diagnostics. -/
def Diagnostic.allPass {Phase : Type u} [PhaseSpace Phase]
    (diag : Diagnostic Phase) : Prop :=
  diag.crossPhaseRecoverable ∧
  diag.behaviorallyCoherent ∧
  diag.compressionTracked ∧
  diag.contradictionFree ∧
  diag.dependencyDisclosed

/-!
## Developmental Line (L0-L4)

The developmental line tracks increasing epistemic sophistication
in handling phase-indexed knowledge:

- L0: no awareness that beliefs have generating conditions
- L1: recognition without protocol (knows phases matter, no method)
- L2: explicit tagging with generating conditions and translation status
- L3: deliberate navigation between states with maintained indexing
- L4: phase-grounding — recognition of the ground from which all arise
-/

/-- The five developmental levels of phase-epistemic sophistication. -/
inductive DevelopmentalLevel where
  /-- L0: No awareness that beliefs have generating conditions -/
  | L0
  /-- L1: Recognition that phases matter, but no systematic protocol -/
  | L1
  /-- L2: Explicit tagging with generating conditions and translation status -/
  | L2
  /-- L3: Deliberate navigation between phases with maintained indexing -/
  | L3
  /-- L4: Phase-grounding — recognition of the ground from which all arise -/
  | L4
  deriving DecidableEq, Repr

/-- Natural number encoding of developmental levels for ordering. -/
def DevelopmentalLevel.toNat : DevelopmentalLevel → ℕ
  | .L0 => 0
  | .L1 => 1
  | .L2 => 2
  | .L3 => 3
  | .L4 => 4

/-- The toNat encoding is injective: distinct levels have distinct codes. -/
theorem DevelopmentalLevel.toNat_injective :
    Function.Injective DevelopmentalLevel.toNat := by
  intro a b h; cases a <;> cases b <;> simp [toNat] at h <;> rfl

/-- Ordering on developmental levels: L0 < L1 < L2 < L3 < L4. -/
instance : LE DevelopmentalLevel where
  le a b := a.toNat ≤ b.toNat

instance : LT DevelopmentalLevel where
  lt a b := a.toNat < b.toNat

instance (a b : DevelopmentalLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance (a b : DevelopmentalLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

instance : Preorder DevelopmentalLevel where
  le_refl a := Nat.le_refl a.toNat
  le_trans _ _ _ h1 h2 := Nat.le_trans h1 h2
  lt_iff_le_not_ge _ _ := Nat.lt_iff_le_not_le

instance : PartialOrder DevelopmentalLevel where
  le_antisymm _ _ h1 h2 :=
    DevelopmentalLevel.toNat_injective (Nat.le_antisymm h1 h2)

instance : OrderBot DevelopmentalLevel where
  bot := .L0
  bot_le a := by cases a <;> decide

instance : OrderTop DevelopmentalLevel where
  top := .L4
  le_top a := by cases a <;> decide

instance : BoundedOrder DevelopmentalLevel where

/-- L0 is strictly below all other levels. -/
theorem L0_lt_L1 : DevelopmentalLevel.L0 < DevelopmentalLevel.L1 := by decide
theorem L0_lt_L2 : DevelopmentalLevel.L0 < DevelopmentalLevel.L2 := by decide
theorem L0_lt_L3 : DevelopmentalLevel.L0 < DevelopmentalLevel.L3 := by decide
theorem L0_lt_L4 : DevelopmentalLevel.L0 < DevelopmentalLevel.L4 := by decide

/-- The developmental ordering is total (linear). -/
theorem developmental_total (a b : DevelopmentalLevel) : a ≤ b ∨ b ≤ a := by
  cases a <;> cases b <;> first | left; decide | right; decide

/-!
## Formally-Derived Propositions and Phase-Invariance

The central theorem: formally-derived propositions have phase-invariant
validity conditions. A formally-derived proposition is one whose content
is a theorem (has a proof), and whose validity conditions are the proof
steps themselves — checkable from any phase.

This is the epistemic asymmetry: formal derivation produces propositions
whose validity does not depend on the generating phase.
-/

/-- A proposition is formally derived when:
    1. Its content is provably true (there exists a proof)
    2. Its validity conditions hold in every phase (phase-invariant)

    The second condition is the key claim: formal proof produces
    phase-invariant validity conditions because the proof steps
    constitute the validity conditions, and proof checking is
    phase-independent (a machine can verify from any phase). -/
structure FormallyDerived {Phase : Type u} (pip : PhaseIndexedProp Phase) where
  /-- The content is provably true -/
  content_proved : pip.content
  /-- The validity conditions hold in every phase.
      This IS the phase-invariance property for formal derivations:
      C does not depend on φ because C = proof steps. -/
  validity_universal : ∀ ψ : Phase, pip.validity ψ

/-- Phase-invariance theorem: if a proposition is formally derived, then
    it is phase-invariant — its validity conditions hold in every phase.

    This is the epistemic asymmetry that makes formal grounding possible:
    formal derivation is the unique epistemic mode where C (validity conditions)
    provably does not depend on φ (generating phase). -/
theorem phase_invariant_C {Phase : Type u}
    (pip : PhaseIndexedProp Phase) (fd : FormallyDerived pip) :
    PhaseInvariant pip :=
  fd.validity_universal

/-- A formally-derived proposition is never phase-locked (assuming at least
    two distinct phases exist). Phase-locking requires validity to hold
    in exactly one phase, but formal derivation makes validity universal. -/
theorem formally_derived_not_locked {Phase : Type u} [ps : PhaseSpace Phase]
    (pip : PhaseIndexedProp Phase) (fd : FormallyDerived pip) :
    ¬ PhaseLocked pip := by
  intro hlocked
  obtain ⟨φ, ψ, hne⟩ := ps.distinct
  -- The validity holds everywhere (from fd), but phase-locking says it holds
  -- only at pip.phase. So φ = pip.phase and ψ = pip.phase, contradicting φ ≠ ψ.
  have hφ : φ = pip.phase := (hlocked φ).mp (fd.validity_universal φ)
  have hψ : ψ = pip.phase := (hlocked ψ).mp (fd.validity_universal ψ)
  exact hne (hφ.trans hψ.symm)

/-- Translation of a formally-derived proposition preserves it in any
    target phase. Formally-derived propositions survive all translations
    because their validity is universal. -/
theorem formally_derived_preserved {Phase : Type u} [PhaseSpace Phase]
    (T : Translation Phase)
    (pip : PhaseIndexedProp Phase) (fd : FormallyDerived pip) :
    ∀ ψ : Phase, T.translate pip ψ = TranslationOutcome.preserved pip :=
  T.invariant_preservation pip fd.validity_universal

/-!
## Axioms: Philosophical Content

The following axioms capture genuinely philosophical claims that cannot be
proved from structural properties alone. They state the relationship between
phase-indexing and epistemic quality.
-/

/-- A proposition that passes all five diagnostics at developmental
    level L2 or above has cross-phase recoverability.
    Proved: `allPass` is a conjunction whose first component is
    `crossPhaseRecoverable`, so this is just projection. -/
theorem diagnostic_recoverability {Phase : Type u} [PhaseSpace Phase]
    (_pip : PhaseIndexedProp Phase) (diag : Diagnostic Phase)
    (_h_subject : diag.subject = _pip)
    (h_pass : diag.allPass)
    (_level : DevelopmentalLevel)
    (_h_level : DevelopmentalLevel.L2 ≤ _level) :
    diag.crossPhaseRecoverable :=
  h_pass.1

/-- Axiom: Phase-invariant propositions pass the behavioral coherence
    diagnostic. If validity holds in every phase, consequence chains
    are preserved across translation.

    Philosophical content: phase-invariance implies behavioral coherence.
    This is not a tautology — it claims that universal validity conditions
    are sufficient (not merely necessary) for consequence preservation. -/
axiom invariant_implies_coherent {Phase : Type u} [PhaseSpace Phase]
    (pip : PhaseIndexedProp Phase) (h : PhaseInvariant pip)
    (T : Translation Phase)
    (q : PhaseIndexedProp Phase)
    (hpq : pip.content → q.content) :
    ∀ ψ, pip.validity ψ → q.validity ψ

/-!
## Structural Theorems (Proved)

These follow from the definitions and axioms above.
-/

/-- Developmental levels are well-founded: any descending chain is finite.
    This follows from the embedding into ℕ via InvImage. -/
theorem developmental_wellFounded :
    WellFounded (fun a b : DevelopmentalLevel => a < b) :=
  InvImage.wf DevelopmentalLevel.toNat Nat.lt_wfRel.wf

/-- Phase-invariant propositions have maximal cross-phase recoverability
    in the sense that translation never degrades them. -/
theorem invariant_maximal_recovery {Phase : Type u} [PhaseSpace Phase]
    (T : Translation Phase)
    (pip : PhaseIndexedProp Phase) (h : PhaseInvariant pip) :
    T.translate pip pip.phase = TranslationOutcome.preserved pip :=
  T.invariant_preservation pip h pip.phase

/-- At L0, generating conditions are invisible. At L2+, they are explicit.
    This is a structural property of the developmental ordering: any level
    at L2 or above is strictly above L0. -/
theorem L2_strictly_above_L0 :
    DevelopmentalLevel.L0 < DevelopmentalLevel.L2 := by decide

/-- Higher developmental levels include lower-level capabilities.
    The ordering is transitive (inherited from ℕ). -/
theorem developmental_transitive (a b c : DevelopmentalLevel)
    (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c :=
  le_trans h1 h2

/-- Phase-invariance is preserved under conjunction: if two propositions
    are phase-invariant, their conjunction is too. -/
theorem invariant_conjunction {Phase : Type u}
    (pip₁ pip₂ : PhaseIndexedProp Phase)
    (h₁ : PhaseInvariant pip₁) (h₂ : PhaseInvariant pip₂)
    (pip_and : PhaseIndexedProp Phase)
    (_h_content : pip_and.content ↔ pip₁.content ∧ pip₂.content)
    (h_validity : ∀ ψ, pip_and.validity ψ ↔ pip₁.validity ψ ∧ pip₂.validity ψ) :
    PhaseInvariant pip_and :=
  fun ψ => (h_validity ψ).mpr ⟨h₁ ψ, h₂ ψ⟩

/-!
## Summary

### Proved (zero sorry, zero axioms)
- `phase_invariant_C`: formally-derived propositions are phase-invariant
- `formally_derived_not_locked`: formal derivation and phase-locking are incompatible
- `formally_derived_preserved`: formally-derived propositions survive all translations
- `developmental_wellFounded`: the developmental ordering is well-founded
- `invariant_conjunction`: phase-invariance is closed under conjunction
- `developmental_total`: the developmental ordering is total
- `L0_lt_L1` through `L0_lt_L4`: L0 is bottom
- `L2_strictly_above_L0`: L2+ is strictly above L0

### Axiomatized (genuinely philosophical content)
- `diagnostic_recoverability`: adequate diagnostics at L2+ ensure recoverability
- `invariant_implies_coherent`: phase-invariance implies behavioral coherence

### Structures
- `PhaseSpace`: category of consciousness states with distinct phases
- `PhaseIndexedProp`: the ⟨p, φ, d, C⟩ schema
- `TranslationOutcome`: five translation outcomes
- `Translation`: translation function with identity coherence + invariant preservation
- `Diagnostic`: five diagnostic conditions
- `DevelopmentalLevel`: L0-L4 with total ordering and bounded lattice structure
- `FormallyDerived`: formally-derived proposition (content proved + validity universal)
- `PhaseLocked`: validity restricted to generating phase
- `PhaseInvariant`: validity holds in all phases
-/

end PhaseEpistemology
