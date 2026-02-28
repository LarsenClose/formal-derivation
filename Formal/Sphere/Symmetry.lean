/-
  Tier 1 — The Sphere: Symmetry

  O(3) action on E³ and S², norm and distance preservation.
  Transitivity proved via Householder reflection.

  Source: ~/ideal/ground_state/SPHERE.md
-/

import Formal.Sphere.Geometry
import Mathlib.LinearAlgebra.UnitaryGroup

namespace Sphere

noncomputable section

/-! ## The orthogonal group -/

/-- O(3): the orthogonal group of 3×3 real matrices -/
abbrev O3 := Matrix.orthogonalGroup (Fin 3) ℝ

/-- Action of O(3) on E³ via matrix-vector multiplication.
    Requires WithLp.equiv coercion: EuclideanSpace is PiLp 2, not Fin 3 → ℝ. -/
def O3_act (A : O3) (v : E3) : E3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm
    (A.1.mulVec ((WithLp.equiv 2 (Fin 3 → ℝ)) v))

/-! ## Provable properties -/

/-- O(3) preserves the dot product (from AᵀA = I) -/
theorem O3_dotProduct_preserves (A : O3) (u w : Fin 3 → ℝ) :
    dotProduct (A.1.mulVec u) (A.1.mulVec w) = dotProduct u w := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]
  have h := Matrix.UnitaryGroup.star_mul_self A
  rw [Matrix.star_eq_conjTranspose] at h
  change A.1.transpose * A.1 = 1 at h
  rw [h, Matrix.vecMul_one]

/-- O(3) preserves the inner product on E³ -/
theorem O3_preserves_inner (A : O3) (u v : E3) :
    @inner ℝ E3 _ (O3_act A u) (O3_act A v) = @inner ℝ E3 _ u v := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [O3_act, WithLp.equiv_symm_apply]
  exact O3_dotProduct_preserves A _ _

/-- O(3) preserves the norm on E³ -/
theorem O3_preserves_norm (A : O3) (v : E3) : ‖O3_act A v‖ = ‖v‖ := by
  have h := O3_preserves_inner A v v
  have lhs :=
    @real_inner_self_eq_norm_sq E3 _ _ (O3_act A v)
  have rhs := @real_inner_self_eq_norm_sq E3 _ _ v
  nlinarith [norm_nonneg (O3_act A v), norm_nonneg v]

/-- O(3) maps S² to S² -/
theorem O3_maps_S2 (A : O3) (v : E3) (hv : v ∈ S2) :
    O3_act A v ∈ S2 := by
  rw [mem_S2_iff] at hv ⊢
  rw [O3_preserves_norm]; exact hv

/-- O(3) acts by isometries on E³: dist (A•p) (A•q) = dist p q -/
theorem O3_isometry (A : O3) (p q : E3) :
    dist (O3_act A p) (O3_act A q) = dist p q := by
  simp only [dist_eq_norm]
  -- Need: O3_act A p - O3_act A q = O3_act A (p - q)
  -- O3_act is linear, so this follows
  have hlin : O3_act A p - O3_act A q = O3_act A (p - q) := by
    simp only [O3_act]; ext i; simp [WithLp.equiv_symm_apply, Matrix.mulVec]
  rw [hlin, O3_preserves_norm]

/-! ## Transitivity -/

/-- Convert a linear isometry equivalence on E³ to a matrix in M₃(ℝ),
    by conjugating with the WithLp equivalence. -/
private def isoToMat (f : E3 ≃ₗᵢ[ℝ] E3) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix'
    ((WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).toLinearMap.comp
      (f.toLinearEquiv.toLinearMap.comp
        (WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)).symm.toLinearMap))

private theorem isoToMat_mulVec (f : E3 ≃ₗᵢ[ℝ] E3) (v : Fin 3 → ℝ) :
    (isoToMat f).mulVec v =
      (WithLp.equiv 2 (Fin 3 → ℝ))
        (f ((WithLp.equiv 2 (Fin 3 → ℝ)).symm v)) := by
  simp only [isoToMat]; rw [LinearMap.toMatrix'_mulVec]; rfl

private theorem isoToMat_mem_O3 (f : E3 ≃ₗᵢ[ℝ] E3) :
    isoToMat f ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff']
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  have key : (∑ x, isoToMat f x i * isoToMat f x j) =
      dotProduct ((isoToMat f).mulVec (Pi.single i 1))
        ((isoToMat f).mulVec (Pi.single j 1)) := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply,
      Finset.sum_ite_eq']
  rw [key, isoToMat_mulVec, isoToMat_mulVec]
  have inner_eq_dot : ∀ a b : E3, @inner ℝ E3 _ a b =
      dotProduct ((WithLp.equiv 2 (Fin 3 → ℝ)) a)
        ((WithLp.equiv 2 (Fin 3 → ℝ)) b) := by
    intro a b
    simp [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      dotProduct]
    congr 1; ext k; ring
  rw [← inner_eq_dot, f.inner_map_map, inner_eq_dot]
  simp [dotProduct, Finset.mem_univ, eq_comm]

private theorem isoToMat_O3_act (f : E3 ≃ₗᵢ[ℝ] E3) (v : E3) :
    O3_act ⟨isoToMat f, isoToMat_mem_O3 f⟩ v = f v := by
  simp only [O3_act, isoToMat_mulVec]
  simp [WithLp.equiv]

/-- O(3) acts transitively on S²: for any two points on the unit sphere,
    there exists an orthogonal matrix mapping one to the other.
    Proved via Householder reflection: the reflection in the hyperplane
    (p − q)ᗮ maps p to q whenever ‖p‖ = ‖q‖. -/
theorem O3_transitive :
    ∀ (p q : E3), p ∈ S2 → q ∈ S2 →
      ∃ A : O3, O3_act A p = q := by
  intro p q hp hq
  rw [mem_S2_iff] at hp hq
  set f := Submodule.reflection (ℝ ∙ (p - q))ᗮ
  have hf : f p = q := Submodule.reflection_sub (by rw [hp, hq])
  exact ⟨⟨isoToMat f, isoToMat_mem_O3 f⟩,
    by rw [isoToMat_O3_act, hf]⟩

end

end Sphere
