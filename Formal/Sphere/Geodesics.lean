/-
  Tier 1 — The Sphere: Geodesics

  Great circles on S², their parametrization, periodicity, and closure.
  Geodesic identification axiomatized (Mathlib gap: no Riemannian geodesics).

  Source: ~/ideal/ground_state/SPHERE.md
-/

import Formal.Sphere.Geometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace Sphere

noncomputable section

/-! ## Great circles -/

/-- A great circle: intersection of S² with the plane orthogonal to unit normal v -/
def GreatCircle (v : E3) (_hv : ‖v‖ = 1) : Set E3 :=
  {p ∈ S2 | @inner ℝ E3 _ v p = 0}

/-- Parametrize a great circle by angle using an orthonormal pair (u, w) -/
def greatCircleParam (u w : E3) : ℝ → E3 :=
  fun t => Real.cos t • u + Real.sin t • w

/-! ## Provable properties -/

/-- The parametrization of an orthonormal pair stays on S² -/
theorem greatCircleParam_mem_S2 (u w : E3)
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (ort : @inner ℝ E3 _ u w = 0) (t : ℝ) :
    greatCircleParam u w t ∈ S2 := by
  rw [mem_S2_iff]
  change ‖Real.cos t • u + Real.sin t • w‖ = 1
  have hsq : ‖Real.cos t • u + Real.sin t • w‖ ^ 2 = 1 := by
    rw [norm_add_sq_real]
    simp [norm_smul, hu, hw, inner_smul_left, inner_smul_right, ort]
  nlinarith [norm_nonneg (Real.cos t • u + Real.sin t • w)]

/-- Great circles are periodic with period 2π -/
theorem greatCircleParam_periodic (u w : E3) (t : ℝ) :
    greatCircleParam u w (t + 2 * Real.pi) = greatCircleParam u w t := by
  simp [greatCircleParam, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Geodesic closure: every great circle returns to its starting point.
    This is the geometric content of A2 (Closure). -/
theorem greatCircle_returns (u w : E3) (t₀ : ℝ) :
    greatCircleParam u w (t₀ + 2 * Real.pi) = greatCircleParam u w t₀ :=
  greatCircleParam_periodic u w t₀

/-- At t = 0, the parametrization gives u -/
theorem greatCircleParam_zero (u w : E3) :
    greatCircleParam u w 0 = u := by
  simp [greatCircleParam, Real.cos_zero, Real.sin_zero]

/-- At t = π, the parametrization gives the antipodal point -u -/
theorem greatCircleParam_pi (u w : E3) :
    greatCircleParam u w Real.pi = -u := by
  simp [greatCircleParam, Real.cos_pi, Real.sin_pi]

/-! ## Axiomatized properties (Mathlib gaps) -/

/-- Great circles are the geodesics of the round metric on S².
    Stated as: for any two non-antipodal points, the unique great circle
    through them realizes the shortest path. Mathlib has no Riemannian
    geodesic formalization. -/
axiom greatCircles_are_geodesics :
  ∀ (p q : E3), p ∈ S2 → q ∈ S2 → p ≠ q → p + q ≠ 0 →
    ∃ (v : E3) (hv : ‖v‖ = 1),
      p ∈ GreatCircle v hv ∧ q ∈ GreatCircle v hv

/-- If v is orthogonal to both p and q, it lies in the orthogonal complement
    of span{p, q}. Helper for greatCircle_unique. -/
private lemma mem_orthogonal_span_pair (p q v : E3)
    (hvp : @inner ℝ E3 _ v p = 0) (hvq : @inner ℝ E3 _ v q = 0) :
    v ∈ (Submodule.span ℝ (Set.range ![p, q]))ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [real_inner_comm]; exact hvq
    · rw [real_inner_comm]; exact hvp
  | zero => simp
  | add x y _ _ ihx ihy => simp [inner_add_left, ihx, ihy]
  | smul a x _ ih => simp [inner_smul_left, ih]

/-- Two non-antipodal points determine a unique great circle.
    Proof: both normal vectors lie in the 1-dimensional orthogonal complement
    of span{p, q} in ℝ³, so they are proportional. Scaling preserves the
    zero-set of the inner product, giving set equality. -/
theorem greatCircle_unique :
  ∀ (p q : E3), p ∈ S2 → q ∈ S2 → p ≠ q → p + q ≠ 0 →
    ∀ (v₁ v₂ : E3) (hv₁ : ‖v₁‖ = 1) (hv₂ : ‖v₂‖ = 1),
      p ∈ GreatCircle v₁ hv₁ → q ∈ GreatCircle v₁ hv₁ →
      p ∈ GreatCircle v₂ hv₂ → q ∈ GreatCircle v₂ hv₂ →
      GreatCircle v₁ hv₁ = GreatCircle v₂ hv₂ := by
  intro p q hp hq hpq hpqa v₁ v₂ hv₁ hv₂ hpv₁ hqv₁ hpv₂ hqv₂
  -- Extract inner product conditions from GreatCircle membership
  have hip1 : @inner ℝ E3 _ v₁ p = 0 := hpv₁.2
  have hiq1 : @inner ℝ E3 _ v₁ q = 0 := hqv₁.2
  have hip2 : @inner ℝ E3 _ v₂ p = 0 := hpv₂.2
  have hiq2 : @inner ℝ E3 _ v₂ q = 0 := hqv₂.2
  -- p, q are linearly independent (non-antipodal distinct unit vectors)
  have hli : LinearIndependent ℝ ![p, q] := by
    rw [linearIndependent_fin2]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
    refine ⟨?_, ?_⟩
    · intro h
      have : ‖q‖ = 1 := by simpa [S2] using hq
      rw [h, norm_zero] at this; norm_num at this
    · intro a ha
      have hpn : ‖p‖ = 1 := by simpa [S2] using hp
      have hqn : ‖q‖ = 1 := by simpa [S2] using hq
      have hnorm : ‖a • q‖ = ‖p‖ := congr_arg (‖·‖) ha
      rw [norm_smul, hqn, mul_one, hpn] at hnorm
      have ha1 : a = 1 ∨ a = -1 :=
        (abs_eq (by norm_num : (1 : ℝ) ≥ 0)).mp (by rwa [Real.norm_eq_abs] at hnorm)
      rcases ha1 with rfl | rfl
      · rw [one_smul] at ha; exact hpq ha.symm
      · rw [neg_one_smul] at ha; exact hpqa (by rw [← ha, neg_add_cancel])
  -- Orthogonal complement of span{p, q} has finrank 1 in ℝ³
  let K := Submodule.span ℝ (Set.range ![p, q])
  have hfKperp : Module.finrank ℝ ↥Kᗮ = 1 := by
    have h1 : Module.finrank ℝ ↥K = 2 := by
      rw [finrank_span_eq_card hli]; simp [Fintype.card_fin]
    have h2 := Submodule.finrank_add_finrank_orthogonal K
    have h3 : Module.finrank ℝ E3 = 3 := finrank_euclideanSpace_fin
    omega
  -- Both normal vectors lie in the 1-dimensional K^perp
  have hv₁K : v₁ ∈ Kᗮ := mem_orthogonal_span_pair p q v₁ hip1 hiq1
  have hv₂K : v₂ ∈ Kᗮ := mem_orthogonal_span_pair p q v₂ hip2 hiq2
  -- v₁ ≠ 0 (unit vector), so it spans K^perp
  have hv₁ne : v₁ ≠ 0 := by intro h; rw [h, norm_zero] at hv₁; norm_num at hv₁
  have hv₁ne' : (⟨v₁, hv₁K⟩ : ↥Kᗮ) ≠ 0 := by
    intro h; exact hv₁ne (Subtype.ext_iff.mp h)
  -- v₂ = c • v₁ for some scalar c (dimension 1)
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨v₁, hv₁K⟩ hv₁ne').mp hfKperp ⟨v₂, hv₂K⟩
  have hcval : c • v₁ = v₂ := by simpa using congr_arg Subtype.val hc
  -- c ≠ 0 since v₂ is a unit vector
  have hv₂ne : v₂ ≠ 0 := by intro h; rw [h, norm_zero] at hv₂; norm_num at hv₂
  have hcne : c ≠ 0 := by
    intro h; rw [h, zero_smul] at hcval; exact hv₂ne hcval.symm
  -- Set extensionality: inner v₁ w = 0 ↔ inner v₂ w = 0
  -- because inner (c • v₁) w = c * inner v₁ w and c ≠ 0
  ext w
  simp only [GreatCircle, Set.mem_sep_iff]
  constructor
  · rintro ⟨hw, hi⟩
    exact ⟨hw, by rw [← hcval, inner_smul_left]; simp [hi]⟩
  · rintro ⟨hw, hi⟩
    refine ⟨hw, ?_⟩
    rw [← hcval, inner_smul_left] at hi
    cases mul_eq_zero.mp hi with
    | inl h => exact absurd (RCLike.ofReal_eq_zero.mp h) hcne
    | inr h => exact h

end

end Sphere
