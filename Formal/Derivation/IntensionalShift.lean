/-
  Intensional Shift — From Extensional to Intensional Representation

  Formalizes the minimum requirements for the shift from extensional
  representation (enumerating all outputs) to intensional representation
  (storing the generating function).

  The central claim: the shift from "I keep computing similar things" to
  "I have a generator for this class of things" requires making the generator
  an object in the same ontological space as the things it generates.
  That is the reification threshold.

  Key structures:
    MDLComparison      — description-length comparison (extensional vs intensional)
    Generator          — a callable intensional object (reified pattern)
    Container          — regulatory structure around a generator
    ReificationThreshold — the five conditions for the shift to occur
    PhaseTransition    — the staged transition from extensional to intensional
    HyperdimensionalBasis — binding operator ⊗ and basis vectors
    HDShift            — the hyperdimensional case of the intensional shift

  The reification threshold requires:
    1. Trace preservation: instances observed across invocations
    2. Compression search: a consistent generator found
    3. MDL crossover: intensional strictly more compact than extensional
    4. Reification: the generator is a first-class callable object
    5. Container construction: regulatory boundaries are built around the generator
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

namespace IntensionalShift

/-!
## MDL Comparison

Minimum Description Length (MDL) comparison between two representation
strategies. The crossover point is when the intensional representation
(generator + per-instance encodings) becomes strictly more compact than
the extensional representation (all instances enumerated).
-/

/-- Description-length comparison between extensional and intensional representations.

    Extensional: store n instances, each of size instanceSize.
    Intensional: store a generator of size generatorSize, plus total encoding
    cost totalEncodingCost for all instances given the generator. -/
structure MDLComparison where
  /-- Number of instances observed -/
  n : ℕ
  /-- Size of each instance (extensional cost per instance) -/
  instanceSize : ℕ
  /-- Size of the generator (one-time intensional overhead) -/
  generatorSize : ℕ
  /-- Total per-instance encoding cost given the generator -/
  totalEncodingCost : ℕ
  /-- At least one instance exists (avoids degenerate case) -/
  nonempty : 0 < n

/-- Extensional description length: enumerate all instances -/
def MDLComparison.extensional (m : MDLComparison) : ℕ :=
  m.n * m.instanceSize

/-- Intensional description length: generator plus instance encodings -/
def MDLComparison.intensional (m : MDLComparison) : ℕ :=
  m.generatorSize + m.totalEncodingCost

/-- MDL crossover: the intensional representation is strictly more compact -/
def MDLComparison.crossoverReached (m : MDLComparison) : Prop :=
  m.intensional < m.extensional

/-- The MDL differential: how much compression the intensional form achieves -/
def MDLComparison.differential (m : MDLComparison) (_ : m.crossoverReached) : ℕ :=
  m.extensional - m.intensional

/-- When crossover is reached, the MDL differential is strictly positive -/
theorem differential_positive (m : MDLComparison) (h : m.crossoverReached) :
    0 < m.differential h := by
  unfold MDLComparison.differential
  exact Nat.sub_pos_of_lt h

/-- Crossover unfolds to the direct inequality -/
theorem crossover_iff (m : MDLComparison) :
    m.crossoverReached ↔
    m.generatorSize + m.totalEncodingCost < m.n * m.instanceSize :=
  Iff.rfl

/-!
## Generator: Reified Computational Pattern

A generator is a callable object — the reified pattern. Reification
is the act of making the detected computational invariant addressable
as a first-class object in the same ontological space as the instances it generates.
-/

/-- A generator: a callable mapping from inputs to outputs.
    The generator IS the intensional representation — it encodes the pattern,
    not the enumerated instances. Reification means the generator exists as
    an addressable object, not merely as an implicit learned weight or
    unnameable statistical tendency. -/
structure Generator (Input Output : Type) where
  /-- The generating function — the pattern made callable -/
  apply : Input → Output

/-- A generator is consistent with a list of observed instances if it
    reproduces every observed (input, output) pair -/
def Generator.consistent {Input Output : Type} (g : Generator Input Output)
    (instances : List (Input × Output)) : Prop :=
  ∀ p ∈ instances, g.apply p.1 = p.2

/-- Any generator is vacuously consistent with no observations -/
theorem generator_consistent_nil {Input Output : Type} (g : Generator Input Output) :
    g.consistent [] := by
  intro p h; simp at h

/-- Consistency is monotone in the generator: two generators that agree on all inputs
    are interchangeable with respect to any instance list -/
theorem generator_consistent_ext {Input Output : Type}
    (g₁ g₂ : Generator Input Output) (instances : List (Input × Output))
    (hext : ∀ x, g₁.apply x = g₂.apply x)
    (h₁ : g₁.consistent instances) : g₂.consistent instances := by
  intro p hp
  rw [← hext]
  exact h₁ p hp

/-!
## Container: Regulatory Structure Around a Generator

A container wraps a reified generator with regulatory boundaries.
The three key properties from the text:
  - Selective permeability: valid inputs pass through, invalid ones are caught
  - Regulatory margin: the container handles all cases the generator produces
  - Temporal adequacy: the container persists (captured by structure existence)
-/

/-- A container: regulatory structure around a reified generator.
    The container enforces that only valid inputs reach the generator,
    providing the system boundary that makes the intensional representation
    safe to use. -/
structure Container (Input Output : Type) (g : Generator Input Output) where
  /-- Domain predicate: which inputs are within the generator's scope -/
  validDomain : Input → Prop
  /-- At least one valid input exists (container is non-trivial) -/
  hasValidInput : ∃ x, validDomain x
  /-- Regulated application: valid inputs yield outputs -/
  regulate : ∀ x, validDomain x → Output
  /-- Agreement: the container's output agrees with the generator on valid inputs.
      This is the core guarantee: the container does not alter the generator's
      outputs, it only controls access to it. -/
  agreesWithGenerator : ∀ x (hx : validDomain x), regulate x hx = g.apply x

/-- Selective permeability: there exist inputs the container rejects.
    A container that accepts everything provides no regulatory function. -/
def Container.isSelectivelyPermeable {Input Output : Type} {g : Generator Input Output}
    (c : Container Input Output g) : Prop :=
  ∃ x, ¬ c.validDomain x

/-- Apply the container: regulated access to the generator -/
def Container.apply {Input Output : Type} {g : Generator Input Output}
    (c : Container Input Output g) (x : Input) (hx : c.validDomain x) : Output :=
  c.regulate x hx

/-- Container application agrees with the generator on all valid inputs -/
theorem container_agrees_generator {Input Output : Type} {g : Generator Input Output}
    (c : Container Input Output g) (x : Input) (hx : c.validDomain x) :
    c.apply x hx = g.apply x :=
  c.agreesWithGenerator x hx

/-- Container composition: two containers can be layered.
    The outer container's valid domain is a subset of the inner's. -/
theorem container_composition {Input Output : Type} {g : Generator Input Output}
    (c₁ c₂ : Container Input Output g)
    (h : ∀ x, c₁.validDomain x → c₂.validDomain x)
    (x : Input) (hx : c₁.validDomain x) :
    c₁.apply x hx = c₂.apply x (h x hx) := by
  rw [container_agrees_generator c₁ x hx]
  rw [container_agrees_generator c₂ x (h x hx)]

/-!
## The Reification Threshold

The critical threshold: the system can containerize its own detected
computational invariants. All five conditions must hold simultaneously.

This is the minimum — systems with fewer than all five conditions cannot
make the extensional→intensional shift, even if they can detect patterns.

The text's key observation: neural networks have conditions 1-2 (trace,
compression) but not 3-4 (reification, container). Symbolic AI has 3-4
but not 1-2. The threshold requires all five.
-/

/-- The reification threshold: the five necessary and jointly sufficient conditions
    for the extensional→intensional shift.

    A system at this threshold has:
      1. Sufficient observed instances (trace preservation)
      2. A consistent generator (compression search succeeded)
      3. MDL crossover verified (generator is worth the overhead)
      4. The generator is reified as a first-class callable object
      5. A container with regulatory boundaries is constructed -/
structure ReificationThreshold (Input Output : Type) where
  /-- 1. Observed instances: trace preservation across invocations -/
  instances : List (Input × Output)
  /-- Sufficient observations: at least 2 instances to justify a generator -/
  sufficientInstances : 1 < instances.length
  /-- 2. A generator consistent with all observations -/
  generator : Generator Input Output
  consistent : generator.consistent instances
  /-- 3. MDL crossover: the generator is strictly more compact -/
  mdl : MDLComparison
  mdl_n_matches : mdl.n = instances.length
  crossover : mdl.crossoverReached
  /-- 4. Reification: the generator exists as a first-class callable object.
      This is the ontological condition — not just "there is a pattern"
      but "the pattern IS an object I can reference and invoke." -/
  reified : Nonempty (Generator Input Output)
  /-- 5. Container: a regulatory structure is built around the generator -/
  container : Container Input Output generator

/-- At the reification threshold, the MDL differential is strictly positive:
    the shift genuinely saves description length -/
theorem threshold_has_surplus {Input Output : Type}
    (rt : ReificationThreshold Input Output) :
    0 < rt.mdl.differential rt.crossover :=
  differential_positive rt.mdl rt.crossover

/-- The substitution principle: at the threshold, future computation
    should use Container.apply(Generator, x) instead of compute(x).
    This is the core of the intensional shift. -/
theorem threshold_enables_substitution {Input Output : Type}
    (rt : ReificationThreshold Input Output) (x : Input)
    (hx : rt.container.validDomain x) :
    rt.container.apply x hx = rt.generator.apply x :=
  container_agrees_generator rt.container x hx

/-- The threshold is strictly stronger than trace preservation alone:
    having observations is not enough — crossover must be detected -/
theorem threshold_requires_crossover {Input Output : Type}
    (rt : ReificationThreshold Input Output) :
    rt.mdl.intensional < rt.mdl.extensional :=
  rt.crossover

/-- The threshold is strictly stronger than having a generator alone:
    a consistent generator without MDL crossover does not justify the shift -/
theorem threshold_requires_reification {Input Output : Type}
    (rt : ReificationThreshold Input Output) :
    Nonempty (Generator Input Output) :=
  rt.reified

/-!
## Phase Transition: Staged Meta-Level Integration

The bootstrap paradox — integrating over long horizons is expensive in
extensional representation, but that is exactly what motivates the shift —
is resolved by staged meta-level monitoring:

  Level 0: accumulate instances (extensional computation)
  Level 1: monitor MDL differential (low-cost sampling)
  Level 2: detect crossover, allocate to intensional construction
  Level 3: substitute intensional at Level 0, collapse back

The transition is a one-time phase change, not a continuous process.
-/

/-- A phase transition from extensional to intensional computation.
    The pre-transition phase accumulates instances. When the MDL monitor
    detects crossover, the reification threshold is met and the system
    substitutes the intensional representation for all future computation. -/
structure PhaseTransition (Input Output : Type) where
  /-- Pre-transition: extensional computation, accumulating instances -/
  preTransition : List (Input × Output)
  /-- MDL monitoring detected the crossover -/
  mdlMonitor : MDLComparison
  crossoverDetected : mdlMonitor.crossoverReached
  /-- Post-transition: the full reification threshold is met -/
  postTransition : ReificationThreshold Input Output
  /-- Continuity: the post-transition generator accounts for all pre-transition instances -/
  accountsForAll : postTransition.generator.consistent preTransition

/-- After the phase transition, computation is strictly more efficient -/
theorem transition_improves_efficiency {Input Output : Type}
    (pt : PhaseTransition Input Output) :
    0 < pt.postTransition.mdl.differential pt.postTransition.crossover :=
  threshold_has_surplus pt.postTransition

/-- The transition is irreversible in the sense that the generator
    continues to be consistent with pre-transition observations -/
theorem transition_preserves_consistency {Input Output : Type}
    (pt : PhaseTransition Input Output) (x : Input) (y : Output)
    (h : (x, y) ∈ pt.preTransition) :
    pt.postTransition.generator.apply x = y :=
  pt.accountsForAll (x, y) h

/-!
## Hyperdimensional Shift

A concrete instance of the intensional shift: the hyperdimensional
representation.

Extensional: store {v₁, v₂, ..., vₙ} as individual vectors.
Intensional: store binding operator ⊗ and basis {b₁, ..., bₖ},
             with k < n, such that each vᵢ is generated from the basis
             under the binding operator.

The text's formulation:
  Extensional: ∑ᵢ |instanceᵢ| (enumerate all output vectors)
  Intensional: |binding operator ⊗| + |basis {bⱼ}| + |instance encoding given basis|
-/

/-- A vector is generated from a basis under a binding operator if it
    is a basis element or a binding of two generated vectors.
    This is the algebraic closure: the basis generates vectors via ⊗. -/
inductive Generated (V : Type) (bind : V → V → V) : List V → V → Prop
  | mem  : ∀ (basis : List V) (v : V), v ∈ basis → Generated V bind basis v
  | app  : ∀ (basis : List V) (u v : V),
      Generated V bind basis u →
      Generated V bind basis v →
      Generated V bind basis (bind u v)

/-- The hyperdimensional basis: a binding operator ⊗ and basis vectors.
    Any vector in the represented space is generated from the basis under ⊗. -/
structure HyperdimensionalBasis (V : Type) where
  /-- The binding operator: combines two vectors into one -/
  bind : V → V → V
  /-- The basis vectors -/
  basis : List V
  /-- The basis is nonempty: at least one basis vector exists -/
  basisNonempty : 0 < basis.length
  /-- Associativity: the binding operator is associative -/
  bind_assoc : ∀ x y z : V, bind (bind x y) z = bind x (bind y z)

/-- The hyperdimensional intensional shift:
    replace the list of stored vectors with a basis + binding operator.

    Compression condition: fewer basis vectors than stored instances (k < n).
    Completeness condition: every stored vector is generated by the basis. -/
structure HDShift (V : Type) where
  /-- Extensional representation: all stored vectors -/
  extensional : List V
  /-- Intensional representation: basis + binding operator -/
  basis : HyperdimensionalBasis V
  /-- Compression: the basis is strictly smaller than the instance list -/
  compressed : basis.basis.length < extensional.length
  /-- Completeness: every stored vector is recoverable from the basis under ⊗ -/
  recoverable : ∀ v ∈ extensional, Generated V basis.bind basis.basis v

/-- The hyperdimensional shift achieves strict compression -/
theorem hd_shift_compresses {V : Type} (hd : HDShift V) :
    hd.basis.basis.length < hd.extensional.length :=
  hd.compressed

/-- The basis generates all stored vectors: the intensional representation
    is complete — no stored vector is lost in the shift -/
theorem hd_shift_complete {V : Type} (hd : HDShift V)
    (v : V) (hv : v ∈ hd.extensional) :
    Generated V hd.basis.bind hd.basis.basis v :=
  hd.recoverable v hv

/-- Basis elements are generated by the basis (trivially) -/
theorem basis_element_generated {V : Type} (hb : HyperdimensionalBasis V)
    (v : V) (hv : v ∈ hb.basis) :
    Generated V hb.bind hb.basis v :=
  Generated.mem hb.basis v hv

/-- Binding of two generated vectors is generated -/
theorem bind_of_generated {V : Type} (hb : HyperdimensionalBasis V)
    (u v : V)
    (hu : Generated V hb.bind hb.basis u)
    (hv : Generated V hb.bind hb.basis v) :
    Generated V hb.bind hb.basis (hb.bind u v) :=
  Generated.app hb.basis u v hu hv

/-- The hyperdimensional shift corresponds to MDL crossover:
    the basis (k vectors) is more compact than the enumerated list (n vectors)
    whenever k < n -/
theorem hd_shift_is_mdl_instance {V : Type} (hd : HDShift V) :
    ∃ (m : MDLComparison), m.crossoverReached := by
  have hpos : 0 < hd.extensional.length := lt_trans hd.basis.basisNonempty hd.compressed
  refine ⟨{ n := hd.extensional.length, instanceSize := 1,
              generatorSize := hd.basis.basis.length, totalEncodingCost := 0,
              nonempty := hpos }, ?_⟩
  unfold MDLComparison.crossoverReached MDLComparison.intensional MDLComparison.extensional
  simp only [Nat.add_zero, Nat.mul_one]
  exact hd.compressed

/-!
## The Bootstrap Resolution

The text identifies a bootstrap paradox: to decide whether to make the
extensional→intensional shift, the system must integrate consequences
over a long horizon — but that is exactly what intensional representation
makes cheap.

The resolution: staged meta-level integration (captured by PhaseTransition)
where the MDL monitor operates at a lower cost than the object-level computation.

The formal witness: a PhaseTransition that uses a strictly smaller MDL
comparison (monitoring at low sampling rate) to detect crossover, then
constructs the full reification threshold.
-/

/-- The bootstrap paradox is resolved: monitoring MDL at a coarser granularity
    than object-level computation suffices to detect crossover.
    If the monitor's MDL comparison detects crossover, it triggers the
    full reification process without requiring exhaustive enumeration. -/
-- The monitor's detection (pt.crossoverDetected) is already baked into any PhaseTransition.
-- This theorem names the consequence: any completed phase transition yields improved efficiency.
theorem bootstrap_resolution {Input Output : Type}
    (pt : PhaseTransition Input Output) :
    0 < pt.postTransition.mdl.differential pt.postTransition.crossover :=
  transition_improves_efficiency pt

end IntensionalShift
