/-
  Tier 2 — Schwarzschild Spacetime: Lorentz Signature

  Pseudo-Riemannian / Lorentzian geometry axiomatized for ℝ⁴.
  Mathlib has Riemannian manifolds but NO pseudo-Riemannian metrics,
  NO Lorentz signature, NO Christoffel symbols, NO curvature tensors.
  We axiomatize the minimal structure needed for Schwarzschild.

  Contents:
  - LorentzSignature: the (-,+,+,+) signature pattern
  - PseudoMetricTensor: symmetric bilinear form with Lorentz signature
  - Minkowski metric as a concrete instance
  - Basic properties: nondegeneracy, signature preservation

  Source: ~/ideal/ground_state/SCHWARZSCHILD.md
-/

import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace Schwarzschild

noncomputable section

/-! ## Spacetime coordinates -/

/-- Four-dimensional real vector space for spacetime coordinates -/
abbrev R4 := Fin 4 → ℝ

/-- Standard basis vector in ℝ⁴ -/
def e (i : Fin 4) : R4 := Pi.single i 1

/-! ## Lorentz signature -/

/-- The Lorentz signature assigns a sign to each coordinate axis.
    Convention: (-,+,+,+) with index 0 = time. -/
def lorentzSign : Fin 4 → ℝ
  | ⟨0, _⟩ => -1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1

theorem lorentzSign_zero : lorentzSign ⟨0, by omega⟩ = -1 := rfl
theorem lorentzSign_one : lorentzSign ⟨1, by omega⟩ = 1 := rfl
theorem lorentzSign_two : lorentzSign ⟨2, by omega⟩ = 1 := rfl
theorem lorentzSign_three : lorentzSign ⟨3, by omega⟩ = 1 := rfl

/-- Every Lorentz sign is ±1 -/
theorem lorentzSign_sq (i : Fin 4) : lorentzSign i ^ 2 = 1 := by
  fin_cases i <;> simp [lorentzSign]

/-- No Lorentz sign is zero — the signature is nondegenerate -/
theorem lorentzSign_ne_zero (i : Fin 4) : lorentzSign i ≠ 0 := by
  fin_cases i <;> simp [lorentzSign]

/-! ## Pseudo-metric tensor (bilinear form with Lorentz signature)

  Mathlib's inner product spaces require positive-definiteness.
  A pseudo-Riemannian metric is an indefinite symmetric bilinear form.
  We define this directly as a function ℝ⁴ → ℝ⁴ → ℝ with the required
  algebraic properties axiomatized where Mathlib cannot provide them.
-/

/-- A diagonal pseudo-metric tensor on ℝ⁴ with given diagonal entries.
    η(u, v) = Σᵢ gᵢᵢ · uᵢ · vᵢ -/
def diagMetric (g : Fin 4 → ℝ) (u v : R4) : ℝ :=
  ∑ i : Fin 4, g i * u i * v i

/-- The Minkowski metric: η = diag(-1, +1, +1, +1) -/
def minkowskiMetric : R4 → R4 → ℝ := diagMetric lorentzSign

/-! ## Algebraic properties of diagMetric -/

/-- diagMetric is symmetric -/
theorem diagMetric_symm (g : Fin 4 → ℝ) (u v : R4) :
    diagMetric g u v = diagMetric g v u := by
  simp only [diagMetric]
  congr 1; ext i; ring

/-- diagMetric is linear in the first argument -/
theorem diagMetric_add_left (g : Fin 4 → ℝ) (u₁ u₂ v : R4) :
    diagMetric g (u₁ + u₂) v = diagMetric g u₁ v + diagMetric g u₂ v := by
  simp only [diagMetric, Pi.add_apply, ← Finset.sum_add_distrib]
  congr 1; ext i; ring

/-- diagMetric is homogeneous in the first argument -/
theorem diagMetric_smul_left (g : Fin 4 → ℝ) (c : ℝ) (u v : R4) :
    diagMetric g (c • u) v = c * diagMetric g u v := by
  simp only [diagMetric, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  congr 1; ext i; ring

/-- diagMetric is linear in the second argument -/
theorem diagMetric_add_right (g : Fin 4 → ℝ) (u v₁ v₂ : R4) :
    diagMetric g u (v₁ + v₂) = diagMetric g u v₁ + diagMetric g u v₂ := by
  rw [diagMetric_symm, diagMetric_add_left, diagMetric_symm g v₁, diagMetric_symm g v₂]

/-- diagMetric is homogeneous in the second argument -/
theorem diagMetric_smul_right (g : Fin 4 → ℝ) (c : ℝ) (u v : R4) :
    diagMetric g u (c • v) = c * diagMetric g u v := by
  rw [diagMetric_symm, diagMetric_smul_left, diagMetric_symm]

/-! ## Nondegeneracy -/

/-- Evaluating diagMetric against a basis vector extracts the j-th component -/
private theorem diagMetric_basis (g : Fin 4 → ℝ) (u : R4) (j : Fin 4) :
    diagMetric g u (e j) = g j * u j := by
  simp only [diagMetric, e]
  rw [Fin.sum_univ_four]
  simp only [Pi.single_apply]
  fin_cases j <;> simp

/-- A diagonal metric with all nonzero entries is nondegenerate:
    if η(u, v) = 0 for all v, then u = 0 -/
theorem diagMetric_nondegenerate (g : Fin 4 → ℝ) (hg : ∀ i, g i ≠ 0)
    (u : R4) (hu : ∀ v : R4, diagMetric g u v = 0) : u = 0 := by
  ext j
  have h := hu (e j)
  rw [diagMetric_basis] at h
  simp only [Pi.zero_apply]
  exact (mul_eq_zero.mp h).resolve_left (hg j)

/-- The Minkowski metric is nondegenerate -/
theorem minkowski_nondegenerate (u : R4) (hu : ∀ v : R4, minkowskiMetric u v = 0) :
    u = 0 :=
  diagMetric_nondegenerate lorentzSign lorentzSign_ne_zero u hu

/-! ## Minkowski metric on basis vectors -/

/-- Minkowski inner product of basis vectors: η(eᵢ, eⱼ) = ηᵢ · δᵢⱼ -/
theorem minkowski_basis (i j : Fin 4) :
    minkowskiMetric (e i) (e j) = if i = j then lorentzSign i else 0 := by
  simp only [minkowskiMetric]
  rw [diagMetric_basis]
  simp only [e, Pi.single_apply]
  split
  · case isTrue h => subst h; simp
  · case isFalse h =>
    rw [if_neg (Ne.symm h), mul_zero]

/-- η(e₀, e₀) = -1 (timelike) -/
theorem minkowski_e0_e0 : minkowskiMetric (e 0) (e 0) = -1 := by
  rw [minkowski_basis]; simp [lorentzSign]

/-- η(e₁, e₁) = +1 (spacelike) -/
theorem minkowski_e1_e1 : minkowskiMetric (e 1) (e 1) = 1 := by
  rw [minkowski_basis]; simp [lorentzSign]

/-- η(e₂, e₂) = +1 (spacelike) -/
theorem minkowski_e2_e2 : minkowskiMetric (e 2) (e 2) = 1 := by
  rw [minkowski_basis]; simp [lorentzSign]

/-- η(e₃, e₃) = +1 (spacelike) -/
theorem minkowski_e3_e3 : minkowskiMetric (e 3) (e 3) = 1 := by
  rw [minkowski_basis]; simp [lorentzSign]

/-! ## Signature characterization

  The signature of the Minkowski metric is (1, 3): one negative eigenvalue,
  three positive eigenvalues. We prove this by exhibiting the signs on the
  standard basis. Since ℝ comparisons are not decidable, we prove these
  by explicit computation rather than `decide`.
-/

/-- The number of negative diagonal entries is 1 -/
theorem lorentzSign_neg_count :
    (Finset.univ.filter (fun i : Fin 4 => lorentzSign i < 0)).card = 1 := by
  convert_to ({(⟨0, by omega⟩ : Fin 4)} : Finset (Fin 4)).card = 1
  · congr 1; ext i; fin_cases i <;> simp [lorentzSign]
  · simp

/-- The number of positive diagonal entries is 3 -/
theorem lorentzSign_pos_count :
    (Finset.univ.filter (fun i : Fin 4 => lorentzSign i > 0)).card = 3 := by
  convert_to ({(⟨1, by omega⟩ : Fin 4), ⟨2, by omega⟩, ⟨3, by omega⟩} : Finset (Fin 4)).card = 3
  · congr 1; ext i; fin_cases i <;> simp [lorentzSign]
  · simp

/-! ## Signature preserved under diagonal rescaling

  If g has Lorentz signature and f scales each entry by a positive factor,
  the resulting metric still has Lorentz signature.
-/

/-- Positive rescaling preserves the sign of each diagonal entry -/
theorem diagMetric_rescale_sign (g f : Fin 4 → ℝ) (hf : ∀ i, f i > 0) (i : Fin 4) :
    (f i * g i < 0 ↔ g i < 0) ∧ (f i * g i > 0 ↔ g i > 0) := by
  constructor
  · exact ⟨fun h => by nlinarith [hf i], fun h => mul_neg_of_pos_of_neg (hf i) h⟩
  · exact ⟨fun h => by nlinarith [hf i], fun h => mul_pos (hf i) h⟩

end

end Schwarzschild
