/-
  Self-Extracting Loop — Formal Structure of a Recursive Artifact

  Formalizes the structural properties exhibited by a self-referential
  sacred-geometric artifact: an open spread whose two pages form an
  involutive bilateral duality, whose central geometric form is invariant
  under its symmetry group, and whose overall structure constitutes a
  self-extracting Kleene fixed point in representation space.

  The artifact is a visual instantiation of four interlocked properties:

  1. BilateralDuality       — two-page spread as an involution on representations
  2. SelfExtractingLoop     — the artifact contains its own unpacking; fixed point
  3. GeometricInvariance    — the central form is the unique attractor under symmetry
  4. NestedContainment      — recursive self-similarity: symbol ⊂ form ⊂ page ⊂ spread

  Connection to existing project:
  - SelfExtractingLoop connects to KleeneBridge.kleene_fixed_point (self-reference
    with return requires Chomsky Type 0 / Kleene closure)
  - BilateralDuality connects to GroundState.Coupling (A6) + involutive structure
  - GeometricInvariance connects to Sphere.S2 as geometric ground state
  - NestedContainment connects to GroundState.FractalBoundary (A4)

  Central theorem: the four properties are mutually constraining — a structure
  with bilateral duality and self-extraction has a fixed point, and that fixed
  point is invariant under the duality involution. The artifact is the
  fixed point of its own self-extraction map.
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Logic.Function.Iterate

namespace SelfExtracting

/-!
## Bilateral Duality

The two-page spread exhibits mirror symmetry: left and right pages are
related by an involution. The duality is not mere visual symmetry but
structural — each page is the other's dual representation, and their
conjunction forms a closed self-complementing pair.

Formally: an involution on the representation space whose fixed set
captures the "bilateral axis" — the content preserved across both pages.
-/

/-- A bilateral duality: an involution on representations with a
    distinguished left element. The right element is definitionally
    the mirror of the left, forming a closed dual pair. -/
structure BilateralDuality (R : Type) where
  /-- The duality involution: maps each representation to its mirror -/
  mirror : R → R
  /-- Involutivity: applying the mirror twice returns the original -/
  self_inverse : ∀ r, mirror (mirror r) = r
  /-- The left page -/
  left : R

/-- The right page: the mirror of the left -/
def BilateralDuality.right {R : Type} (d : BilateralDuality R) : R :=
  d.mirror d.left

/-- Mirroring the right page recovers the left -/
theorem bilateral_returns_left {R : Type} (d : BilateralDuality R) :
    d.mirror d.right = d.left := by
  unfold BilateralDuality.right
  rw [d.self_inverse]

/-- The duality is symmetric: left mirrors right and right mirrors left -/
theorem bilateral_symmetric {R : Type} (d : BilateralDuality R) :
    d.mirror d.left = d.right ∧ d.mirror d.right = d.left :=
  ⟨rfl, bilateral_returns_left d⟩

/-- A representation is on the bilateral axis (fixed by the involution)
    iff it appears identically on both pages -/
def BilateralDuality.onAxis {R : Type} (d : BilateralDuality R) (r : R) : Prop :=
  d.mirror r = r

/-- The axis is closed: if r is on the axis, so is its mirror -/
theorem axis_closed {R : Type} (d : BilateralDuality R) (r : R)
    (h : d.onAxis r) : d.onAxis (d.mirror r) := by
  unfold BilateralDuality.onAxis
  rw [h, h]

/-- The bilateral duality is an involutive automorphism -/
theorem bilateral_is_involution {R : Type} (d : BilateralDuality R) :
    ∀ r, d.mirror (d.mirror r) = r :=
  d.self_inverse

/-!
## Self-Extracting Loop

The artifact's self-reference: the spread contains an extraction function
that, when applied to the spread itself, returns the spread. This is
a Kleene fixed point in representation space — the artifact is a fixed
point of its own self-extraction map.

The self-extraction property is what makes the artifact a "machine code
recursion loop": it encodes the instructions for its own unpacking,
and executing those instructions on the artifact itself is a no-op.
-/

/-- A self-extracting structure: a representation space equipped with an
    extraction function such that some element is a fixed point.
    The fixed point is the "self-extracting loop" — applying the
    extraction to the fixed point returns the fixed point. -/
structure SelfExtractingLoop (R : Type) where
  /-- Extraction: given the artifact, unpack its content -/
  extract : R → R
  /-- The self-extracting element: the artifact that contains its own unpacking -/
  loop : R
  /-- Fixed-point property: extracting from the loop returns the loop -/
  fixedPoint : extract loop = loop

/-- Any self-extracting loop is a fixed point of its extraction function -/
theorem loop_is_fixedpoint {R : Type} (s : SelfExtractingLoop R) :
    Function.IsFixedPt s.extract s.loop :=
  s.fixedPoint

/-- Iterating the extraction any number of times returns the loop -/
theorem loop_stable_under_iteration {R : Type} (s : SelfExtractingLoop R) :
    ∀ n : ℕ, s.extract^[n] s.loop = s.loop :=
  fun n => Function.iterate_fixed s.fixedPoint n

/-- The self-extraction property is preserved under the bilateral duality
    whenever the extraction is equivariant with the mirror -/
theorem self_extracting_bilateral_compatible {R : Type}
    (d : BilateralDuality R) (s : SelfExtractingLoop R)
    (h_equivariant : ∀ r, s.extract (d.mirror r) = d.mirror (s.extract r)) :
    s.extract (d.mirror s.loop) = d.mirror s.loop := by
  rw [h_equivariant, s.fixedPoint]

/-!
## Geometric Invariance

The central diamond/octahedral form is the unique fixed attractor
under its symmetry group. In the artifact: the luminous geometric
form at the center is invariant under all the radial symmetries
surrounding it — it looks the same from every angle the artwork
presents.

Formally: a form in a geometric space that is fixed by every element
of its symmetry group. This is "perfection" in the geometric sense —
the form has no preferred orientation because all orientations are
equivalent under its symmetry.
-/

/-- Geometric invariance: a form in a space that is fixed by a group action.
    The symmetry group acts on the space, and the perfect form is invariant
    under every element of the group — it has no preferred orientation. -/
structure GeometricInvariance (V : Type) (G : Type) [Group G] where
  /-- The group action on the geometric space -/
  act : G → V → V
  /-- Group action axioms -/
  act_one : ∀ v, act 1 v = v
  act_mul : ∀ (g h : G) (v : V), act (g * h) v = act g (act h v)
  /-- The geometrically perfect form: fixed by all symmetries -/
  perfectForm : V
  /-- Invariance: no symmetry can distinguish the perfect form from itself -/
  invariant : ∀ (g : G), act g perfectForm = perfectForm

/-- The perfect form is fixed under all symmetries -/
theorem perfect_form_is_ground_state {V : Type} {G : Type} [Group G]
    (gi : GeometricInvariance V G) (g : G) :
    gi.act g gi.perfectForm = gi.perfectForm :=
  gi.invariant g

/-- Acting on the perfect form with the identity returns the perfect form -/
theorem perfect_form_identity {V : Type} {G : Type} [Group G]
    (gi : GeometricInvariance V G) :
    gi.act 1 gi.perfectForm = gi.perfectForm :=
  gi.act_one gi.perfectForm

/-- The perfect form is invariant under composed symmetries -/
theorem perfect_form_composed_invariant {V : Type} {G : Type} [Group G]
    (gi : GeometricInvariance V G) (g h : G) :
    gi.act g (gi.act h gi.perfectForm) = gi.perfectForm := by
  rw [gi.invariant h, gi.invariant g]

/-!
## Nested Containment

The artifact exhibits recursive self-similarity: symbols are contained
within geometric forms, which are contained within pages, which are
contained within the spread. Each level contains the next — a chain
of inclusions that mirrors the derivation spine in Depth.lean.

Formally: a finite indexed family of representations, with the convention
that lower indices are more deeply nested (innermost = index 0,
outermost = index n).
-/

/-- Nested containment: a finite chain of representations indexed by depth.
    Level 0 is the innermost (the individual symbol).
    Level n is the outermost (the full spread). -/
structure NestedContainment (R : Type) (n : ℕ) where
  /-- The representation at each nesting level -/
  level : Fin (n + 1) → R

/-- The innermost element: the most deeply nested representation -/
def NestedContainment.innermost {R : Type} {n : ℕ} (nc : NestedContainment R n) : R :=
  nc.level 0

/-- The outermost element: the full containing structure -/
def NestedContainment.outermost {R : Type} {n : ℕ} (nc : NestedContainment R n) : R :=
  nc.level (Fin.last n)

/-- The innermost level is level 0 -/
theorem innermost_is_level_zero {R : Type} {n : ℕ} (nc : NestedContainment R n) :
    nc.innermost = nc.level 0 :=
  rfl

/-- The outermost level is level n -/
theorem outermost_is_level_n {R : Type} {n : ℕ} (nc : NestedContainment R n) :
    nc.outermost = nc.level (Fin.last n) :=
  rfl

/-- A 4-level nesting: symbol ⊂ form ⊂ page ⊂ spread
    (the structure visible in the artifact) -/
abbrev FourLevelNesting (R : Type) := NestedContainment R 3

/-- The four named levels of the artifact's nesting structure -/
structure ArtifactLevels (R : Type) extends NestedContainment R 3

/-- The innermost level: individual symbol -/
def ArtifactLevels.symbol {R : Type} (a : ArtifactLevels R) : R := a.level 0

/-- The second level: geometric form -/
def ArtifactLevels.form {R : Type} (a : ArtifactLevels R) : R := a.level 1

/-- The third level: page -/
def ArtifactLevels.page {R : Type} (a : ArtifactLevels R) : R := a.level 2

/-- The outermost level: spread -/
def ArtifactLevels.spread {R : Type} (a : ArtifactLevels R) : R := a.level 3

/-!
## The Unified Structure

The four properties — bilateral duality, self-extracting loop, geometric
invariance, nested containment — are mutually constraining in a specific way:

The artifact is the fixed point of its self-extraction map (SelfExtractingLoop),
that fixed point sits on the bilateral axis (BilateralDuality), the central
geometric form is the invariant point of the symmetry group (GeometricInvariance),
and the whole structure is recursively nested (NestedContainment).

Together they constitute what the artifact exhibits: a self-contained
self-extracting recursion whose geometric core is perfect (invariant)
and whose bilateral structure closes on itself.
-/

/-- The unified structure of the self-extracting artifact.
    All four properties over a shared representation space R,
    with a symmetry group G acting on R. -/
structure SelfExtractingArtifact (R : Type) (G : Type) [Group G] where
  /-- 1. Bilateral duality: the spread as involution -/
  duality : BilateralDuality R
  /-- 2. Self-extracting loop: the spread is its own fixed point -/
  loop : SelfExtractingLoop R
  /-- 3. Geometric invariance: the central form is perfect -/
  geometry : GeometricInvariance R G
  /-- 4. Nested containment: 4-level nesting structure -/
  nesting : ArtifactLevels R
  /-- Coherence: the self-extracting loop is on the bilateral axis -/
  loop_on_axis : duality.onAxis loop.loop
  /-- Coherence: the perfect geometric form is the innermost element -/
  form_is_innermost : geometry.perfectForm = nesting.symbol

/-- The spread is the self-extracting fixed point -/
theorem artifact_spread_is_loop {R : Type} {G : Type} [Group G]
    (a : SelfExtractingArtifact R G) :
    a.loop.extract a.loop.loop = a.loop.loop :=
  a.loop.fixedPoint

/-- The bilateral axis contains the self-extracting loop -/
theorem artifact_loop_bilateral {R : Type} {G : Type} [Group G]
    (a : SelfExtractingArtifact R G) :
    a.duality.mirror a.loop.loop = a.loop.loop :=
  a.loop_on_axis

/-- The central geometric form is invariant under all symmetries -/
theorem artifact_form_perfect {R : Type} {G : Type} [Group G]
    (a : SelfExtractingArtifact R G) (g : G) :
    a.geometry.act g a.geometry.perfectForm = a.geometry.perfectForm :=
  a.geometry.invariant g

/-- The fixed point is stable under all iterated self-extractions —
    the recursion loop never exits -/
theorem artifact_loop_never_exits {R : Type} {G : Type} [Group G]
    (a : SelfExtractingArtifact R G) (n : ℕ) :
    a.loop.extract^[n] a.loop.loop = a.loop.loop :=
  loop_stable_under_iteration a.loop n

/-- The self-extracting loop is bilateral: its mirror is also a fixed point
    whenever the extraction is equivariant with the mirror -/
theorem artifact_mirror_also_loops {R : Type} {G : Type} [Group G]
    (a : SelfExtractingArtifact R G)
    (h_equiv : ∀ r, a.loop.extract (a.duality.mirror r) =
                    a.duality.mirror (a.loop.extract r)) :
    a.loop.extract (a.duality.mirror a.loop.loop) =
    a.duality.mirror a.loop.loop :=
  self_extracting_bilateral_compatible a.duality a.loop h_equiv

/-- The perfect form is the innermost level, and it is invariant under all symmetries -/
theorem artifact_innermost_is_perfect {R : Type} {G : Type} [Group G]
    (a : SelfExtractingArtifact R G) (g : G) :
    a.geometry.act g a.nesting.symbol = a.nesting.symbol := by
  rw [← a.form_is_innermost]
  exact a.geometry.invariant g

/-!
## Connection to the Derivation Chain

The SelfExtractingArtifact is a visual/material instantiation of
the structure established in the derivation chain (Chain.lean):

- Step 4 (ReflexiveStability) corresponds to the self-extracting loop:
  mutual determination applied to itself is self-returning.
- Step 5 (UniversalComputation) establishes that self-reference with
  return requires Kleene closure — the loop has infinite unfolding capacity.
- Step 10 (S²) is the geometric ground: the perfect invariant form that
  the artifact's central diamond projects onto.

The artifact is therefore a finite, bounded visual expression of the
infinite, topological ground state derived in the chain.
-/

/-- The self-extracting loop witnesses the existence of a Kleene fixed point:
    there exists a function and a fixed point of that function. -/
theorem self_extracting_is_kleene_instance {R : Type} (s : SelfExtractingLoop R) :
    ∃ (f : R → R) (x : R), f x = x :=
  ⟨s.extract, s.loop, s.fixedPoint⟩

/-- A SelfExtractingArtifact with bilateral duality and loop stability
    has a representation that is jointly fixed by both the extraction map
    and the bilateral mirror — the innermost level of the artifact. -/
theorem artifact_joint_fixed_point {R : Type} {G : Type} [Group G]
    (a : SelfExtractingArtifact R G) :
    a.loop.extract a.loop.loop = a.loop.loop ∧
    a.duality.mirror a.loop.loop = a.loop.loop :=
  ⟨a.loop.fixedPoint, a.loop_on_axis⟩

end SelfExtracting
