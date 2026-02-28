/-
  Tier 1 — The Sphere: Bridge to Ground State

  Part I constructs A1–A3 on the actual sphere type ↥(Metric.sphere 0 1).
  The z-coordinate induces a preorder on S², breaking the full O(3) symmetry
  to a height ordering. This symmetry-breaking is honest: any observation of S²
  requires choosing a frame, and the z-axis is as good as any (by transitivity).

  Part II retains finite categorical models (following Consistency.lean) as a
  fully-proved combinatorial consistency check.

  A1 (Locality) ← O(3) transitivity (any point serves as "here")
  A2 (Closure)  ← geodesic closure (equator points close; equator → pole does not)
  A3 (Opacity)  ← sphere enclosure (S² embeds into S² ⊕ {center}; center unreachable)

  Source: ~/ideal/ground_state/SPHERE.md
-/

import Formal.GroundState.Axioms
import Formal.Sphere.Geometry
import Formal.Sphere.Geodesics
import Formal.Sphere.Symmetry
import Mathlib.CategoryTheory.Category.Preorder

namespace Sphere

open CategoryTheory GroundState

/-! # Part I: Geometric Bridge — Axioms on ↥S²

  S² has maximal continuous symmetry (O(3) acts transitively), so any
  categorical ordering must break symmetry. The z-coordinate provides a
  height function z : S² → [-1, 1], inducing a preorder on ↥S²:
    p ≤ q iff z(p) ≤ z(q)

  This is an explicit choice of frame. O(3) transitivity (A1_geometric_witness)
  guarantees that any other axis gives an isomorphic construction.

  Resistance encountered:
  - S² is too symmetric for nonClosing on the full isometry group: any two
    points can be mapped to each other. Breaking symmetry (choosing z) is
    necessary and honest.
  - PiLp/WithLp machinery makes component extraction verbose. The key lemma
    zCoord_le_one requires decomposing the inner product into a Fin 3 sum.
-/

noncomputable section

/-! ## Sphere points and z-coordinate ordering -/

/-- Subtype of points on the unit 2-sphere -/
abbrev S2Pt := ↥S2

/-- z-coordinate: the height function on S².
    Extracts the third component via WithLp.equiv (identity on terms,
    but needed for Lean to see through the PiLp wrapper). -/
def zCoord (p : S2Pt) : ℝ :=
  ((WithLp.equiv 2 (Fin 3 → ℝ)) p.1) (2 : Fin 3)

/-- Preorder on S² induced by z-coordinate.
    Uses Preorder.lift so that (p ≤ q) is definitionally (zCoord p ≤ zCoord q). -/
instance S2Pt.preorder : Preorder S2Pt := Preorder.lift zCoord

/-- North pole: (0, 0, 1) ∈ S² -/
def northPole : S2Pt :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1, by simp [S2, EuclideanSpace.norm_single]⟩

/-- Equator point X: (1, 0, 0) ∈ S² -/
def equatorPtX : S2Pt :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by simp [S2, EuclideanSpace.norm_single]⟩

/-- Equator point Y: (0, 1, 0) ∈ S² -/
def equatorPtY : S2Pt :=
  ⟨EuclideanSpace.single (1 : Fin 3) 1, by simp [S2, EuclideanSpace.norm_single]⟩

/-! ## z-coordinate computations

  EuclideanSpace.single creates basis vectors. Unfolding requires a two-stage
  simp: first `simp only [EuclideanSpace.single]` to normalize, then `simp` to
  evaluate. A bare `simp [EuclideanSpace.single, ...]` loops due to interaction
  between `EuclideanSpace.toLp_single` and `EuclideanSpace.single`. -/

lemma zCoord_northPole : zCoord northPole = 1 := by
  unfold zCoord northPole; simp only [EuclideanSpace.single]; simp

lemma zCoord_equatorPtX : zCoord equatorPtX = 0 := by
  unfold zCoord equatorPtX; simp only [EuclideanSpace.single]; simp

lemma zCoord_equatorPtY : zCoord equatorPtY = 0 := by
  unfold zCoord equatorPtY; simp only [EuclideanSpace.single]; simp

lemma eqX_le_eqY : equatorPtX ≤ equatorPtY := by
  change zCoord equatorPtX ≤ zCoord equatorPtY
  rw [zCoord_equatorPtX, zCoord_equatorPtY]

lemma eqY_le_eqX : equatorPtY ≤ equatorPtX := by
  change zCoord equatorPtY ≤ zCoord equatorPtX
  rw [zCoord_equatorPtY, zCoord_equatorPtX]

lemma eq_le_north : equatorPtX ≤ northPole := by
  change zCoord equatorPtX ≤ zCoord northPole
  rw [zCoord_equatorPtX, zCoord_northPole]; norm_num

lemma not_north_le_eq : ¬ (northPole ≤ equatorPtX) := by
  change ¬ (zCoord northPole ≤ zCoord equatorPtX)
  rw [zCoord_northPole, zCoord_equatorPtX]; norm_num

/-- Each component of a unit sphere point has absolute value ≤ 1.
    Proof: ‖p‖² = p₀² + p₁² + p₂² = 1 (inner product decomposition over Fin 3),
    so p₂² ≤ 1, hence |p₂| ≤ 1, hence p₂ ≤ 1. -/
lemma zCoord_le_one (p : S2Pt) : zCoord p ≤ 1 := by
  have hmem := p.property; rw [mem_S2_iff] at hmem
  suffices h : zCoord p ^ 2 ≤ 1 by nlinarith [sq_abs (zCoord p)]
  have h_norm_sq : @inner ℝ E3 _ p.val p.val = 1 := by
    rw [real_inner_self_eq_norm_sq]; rw [hmem]; norm_num
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h_norm_sq
  simp only [Fin.sum_univ_three] at h_norm_sq
  have hzc : zCoord p = (↑p : E3).ofLp (2 : Fin 3) := rfl
  rw [hzc, sq]
  linarith [mul_self_nonneg ((↑p : E3).ofLp (0 : Fin 3)),
            mul_self_nonneg ((↑p : E3).ofLp (1 : Fin 3))]

/-! ## A1: Locality on ↥S² -/

/-- Geometric witness: O(3) transitivity means any point on S² can be mapped
    to any other by an isometry. This justifies choosing any point as "here". -/
theorem A1_geometric_witness :
    ∀ (p q : E3), p ∈ S2 → q ∈ S2 → ∃ A : O3, O3_act A p = q :=
  O3_transitive

/-- A1 on the actual sphere: north pole as distinguished point.
    O(3) transitivity guarantees any other choice gives an isomorphic result. -/
def geoLocality : Locality S2Pt where
  here := northPole

/-! ## A2: Closure on ↥S² -/

/-- Geometric witness: every great circle returns to its starting point.
    This is the proved periodicity of greatCircleParam. -/
theorem A2_geometric_witness :
    ∀ (u w : E3) (t₀ : ℝ),
      greatCircleParam u w (t₀ + 2 * Real.pi) = greatCircleParam u w t₀ :=
  greatCircle_returns

/-- A2 on the actual sphere: two equator points at the same z-height (z = 0)
    form a closing pair — each ≤ the other. The pair equator → north pole
    does not close: z = 0 < z = 1, and 1 ≰ 0. -/
def geoClosure : Closure S2Pt where
  X := equatorPtX
  Y := equatorPtY
  forward := homOfLE eqX_le_eqY
  back := homOfLE eqY_le_eqX
  nonClosing := ⟨equatorPtX, northPole, homOfLE eq_le_north,
    ⟨fun g => absurd (leOfHom g) not_north_le_eq⟩⟩

/-! ## A3: Opacity on ↥S² ⊕ {center} -/

/-- Geometric witness: the origin (interior of the ball) is not on the sphere.
    ‖0‖ = 0 ≠ 1. -/
theorem A3_geometric_witness : (0 : E3) ∉ S2 := by
  rw [mem_S2_iff]; simp

/-- Extended spatial context: sphere surface plus a center point.
    Models the fact that E³ contains points not on S². -/
abbrev SphereContext := S2Pt ⊕ PUnit

/-- z-coordinate on the extended context.
    Center maps to 2, placing it strictly above all sphere points (whose z ≤ 1).
    This makes center unreachable from the surface in the preorder. -/
def zCoordCtx : SphereContext → ℝ
  | .inl p => zCoord p
  | .inr _ => 2

/-- Preorder on the extended context via z-coordinate. -/
instance SphereContext.preorder : Preorder SphereContext := Preorder.lift zCoordCtx

/-- Embedding functor: sphere surface into spatial context. -/
def surfToCtx : S2Pt ⥤ SphereContext where
  obj := Sum.inl
  map f := homOfLE (by
    change zCoordCtx (.inl _) ≤ zCoordCtx (.inl _)
    show zCoord _ ≤ zCoord _; exact leOfHom f)

/-- A3 on the actual sphere: S² embeds fully and faithfully into S² ⊕ {center}.
    The center (at z = 2) is strictly above all sphere points (z ≤ 1), so:
    - No sphere point is isomorphic to center (no morphism from z = 2 to z ≤ 1)
    - No retraction exists (would require mapping center back to some z ≤ 1) -/
def geoOpacity : Opacity S2Pt SphereContext where
  ι := surfToCtx
  faithful := ⟨fun _ => Subsingleton.elim _ _⟩
  full := ⟨fun {X Y} f => by
    refine ⟨homOfLE ?_, Subsingleton.elim _ _⟩
    have h : zCoordCtx (.inl X) ≤ zCoordCtx (.inl Y) := leOfHom f
    simp only [zCoordCtx] at h; exact h⟩
  opaque_object := .inr PUnit.unit
  not_in_image := fun X => by
    intro ⟨iso⟩
    have h := leOfHom iso.inv
    change zCoordCtx (.inr PUnit.unit) ≤ zCoordCtx (.inl X) at h
    simp only [zCoordCtx] at h
    linarith [zCoord_le_one X]
  no_retraction := fun R => by
    intro ⟨iso⟩
    have h := leOfHom (iso.app (.inr PUnit.unit)).inv
    change zCoordCtx (.inr PUnit.unit) ≤ zCoordCtx (surfToCtx.obj (R.obj (.inr PUnit.unit))) at h
    simp only [zCoordCtx, surfToCtx] at h
    linarith [zCoord_le_one (R.obj (.inr PUnit.unit))]

end

/-! # Part II: Combinatorial Consistency Check

  Finite categorical models following the pattern of GroundState/Consistency.lean.
  These are fully proved (no sorry, no axioms beyond propositional logic) and serve
  as a redundancy layer: even if the geometric bridge above has logical dependencies
  on axioms (O3_transitive, etc.), these finite models demonstrate satisfiability of
  A1–A3 from pure combinatorics. -/

section CombinatorialCheck

/-! ## A1 combinatorial: two-point total preorder -/

inductive SphPt | north | south deriving DecidableEq

instance : LE SphPt where le _ _ := True

instance : Preorder SphPt where
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

instance (a b : SphPt) : Decidable (a ≤ b) := isTrue trivial

def sphereLocality : Locality SphPt where
  here := .north

/-! ## A2 combinatorial: closing pair with non-closing edge -/

inductive GeoObj | start | antipode | edge deriving DecidableEq

instance : LE GeoObj where
  le a b := match a, b with
    | .start, .start | .start, .antipode | .start, .edge
    | .antipode, .start | .antipode, .antipode | .antipode, .edge
    | .edge, .edge => True
    | _, _ => False

instance : Preorder GeoObj where
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]

instance (a b : GeoObj) : Decidable (a ≤ b) := by
  cases a <;> cases b <;> simp [LE.le] <;> exact inferInstance

def sphereClosure : Closure GeoObj where
  X := .start
  Y := .antipode
  forward := homOfLE (by trivial : GeoObj.start ≤ .antipode)
  back := homOfLE (by trivial : GeoObj.antipode ≤ .start)
  nonClosing := ⟨.start, .edge,
    homOfLE (by trivial : GeoObj.start ≤ .edge),
    ⟨fun g => absurd (leOfHom g) (by decide)⟩⟩

/-! ## A3 combinatorial: surface/space with opaque center -/

inductive SurfPt | north | south | equator deriving DecidableEq
inductive SpacePt | north | south | equator | center deriving DecidableEq

instance : LE SurfPt where le _ _ := True

instance : Preorder SurfPt where
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

instance (a b : SurfPt) : Decidable (a ≤ b) := isTrue trivial

instance : LE SpacePt where
  le a b := match a, b with
    | .north, .north | .north, .south | .north, .equator
    | .south, .north | .south, .south | .south, .equator
    | .equator, .north | .equator, .south | .equator, .equator
    | .center, .center => True
    | _, _ => False

instance : Preorder SpacePt where
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]

instance (a b : SpacePt) : Decidable (a ≤ b) := by
  cases a <;> cases b <;> simp [LE.le] <;> exact inferInstance

def embedSurf : SurfPt → SpacePt
  | .north => .north | .south => .south | .equator => .equator

def surfToSpace : SurfPt ⥤ SpacePt where
  obj := embedSurf
  map {X Y} f := homOfLE (by
    have h := leOfHom f
    cases X <;> cases Y <;> simp_all [embedSurf, LE.le])

def sphereOpacity : Opacity SurfPt SpacePt where
  ι := surfToSpace
  faithful := ⟨fun _ => Subsingleton.elim _ _⟩
  full := ⟨fun {X Y} f => by
    refine ⟨homOfLE ?_, Subsingleton.elim _ _⟩
    have := leOfHom f
    cases X <;> cases Y <;> first | trivial | exact this⟩
  opaque_object := .center
  not_in_image := fun X => by
    intro ⟨iso⟩
    have := leOfHom iso.hom
    cases X <;> simp [embedSurf, surfToSpace, LE.le] at this
  no_retraction := fun R => by
    intro ⟨iso⟩
    have h_inv := leOfHom (iso.app SpacePt.center).inv
    have : ∀ s : SurfPt, ¬ (SpacePt.center ≤ embedSurf s) := by
      intro s; cases s <;> decide
    exact this _ h_inv

end CombinatorialCheck

/-! # Bridge Summary

  **Geometric bridge** (Part I): A1, A2, A3 constructed on ↥(Metric.sphere 0 1)
  with z-coordinate preorder. Zero sorry. Depends on sphere theorems from
  Geometry.lean, Geodesics.lean, Symmetry.lean (deleting those files breaks
  compilation via geometric witnesses).

  **Combinatorial check** (Part II): A1, A2, A3 on finite inductive types.
  Zero sorry, zero axioms. Follows Consistency.lean pattern.

  **What resists** (documented in Status.lean):
  - S² is too symmetric for nonClosing: O(3) acts transitively, so in the full
    isometry group every point maps to every other. Breaking symmetry (choosing
    z-axis) is necessary. This is the main structural finding of Tier 1.
  - PiLp/WithLp abstraction barrier: extracting components from EuclideanSpace
    requires explicit WithLp.equiv coercions. The zCoord_le_one proof navigates
    this by decomposing the inner product into a Fin 3 sum.
  - A4–A7 not attempted. These require richer categorical structure (endofunctor
    inexhaustibility, presheaves, adjunctions) that does not arise naturally from
    S² geometry alone.
-/

end Sphere
