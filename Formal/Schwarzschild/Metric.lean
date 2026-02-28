/-
  Tier 2 — Schwarzschild Spacetime: Metric

  The Schwarzschild metric for a non-rotating, uncharged black hole
  of mass M > 0. Expressed in Schwarzschild coordinates (t, r, θ, φ)
  with signature (-,+,+,+).

  Contents:
  - SchwarzschildSpacetime structure with mass parameter
  - Metric components: g_tt, g_rr, g_θθ, g_φφ
  - Event horizon at r_s = 2M
  - Well-definedness for r > 2M
  - Flat-space limit as r → ∞
  - Connection to S² angular geometry from Tier 1

  Source: ~/ideal/ground_state/SCHWARZSCHILD.md
-/

import Formal.Schwarzschild.Lorentz
import Formal.Sphere.Geometry
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Schwarzschild

noncomputable section

open Real

/-! ## Schwarzschild spacetime parameters -/

/-- A Schwarzschild spacetime is determined by a positive mass parameter M.
    All quantities are in geometrized units (G = c = 1). -/
structure SchwarzschildData where
  /-- Mass of the central body (in geometrized units) -/
  M : ℝ
  /-- Mass is strictly positive -/
  hM : M > 0

/-! ## Schwarzschild radius (event horizon) -/

/-- The Schwarzschild radius: r_s = 2M -/
def schwarzschildRadius (s : SchwarzschildData) : ℝ := 2 * s.M

/-- The Schwarzschild radius is strictly positive -/
theorem schwarzschildRadius_pos (s : SchwarzschildData) :
    schwarzschildRadius s > 0 := by
  unfold schwarzschildRadius; linarith [s.hM]

/-! ## Metric components

  In Schwarzschild coordinates (t, r, θ, φ), the line element is:
    ds² = -(1 - 2M/r) dt² + (1 - 2M/r)⁻¹ dr² + r² dθ² + r² sin²θ dφ²

  We define each diagonal metric component as a function of the
  coordinates and the mass parameter.
-/

/-- The factor (1 - 2M/r) that appears in g_tt and g_rr -/
def schwarzFactor (s : SchwarzschildData) (r : ℝ) : ℝ :=
  1 - 2 * s.M / r

/-- g_tt component: -(1 - 2M/r) -/
def g_tt (s : SchwarzschildData) (r : ℝ) : ℝ :=
  -(schwarzFactor s r)

/-- g_rr component: (1 - 2M/r)⁻¹ -/
def g_rr (s : SchwarzschildData) (r : ℝ) : ℝ :=
  (schwarzFactor s r)⁻¹

/-- g_θθ component: r² -/
def g_θθ (_s : SchwarzschildData) (r : ℝ) : ℝ :=
  r ^ 2

/-- g_φφ component: r² sin²θ -/
def g_φφ (_s : SchwarzschildData) (r θ : ℝ) : ℝ :=
  r ^ 2 * sin θ ^ 2

/-! ## Well-definedness for r > 2M

  The Schwarzschild metric is well-defined (nonsingular) in the exterior
  region r > 2M = r_s. We prove that the Schwarz factor is positive there,
  which ensures g_tt < 0 (timelike) and g_rr > 0 (spacelike), and the
  metric is nondegenerate.
-/

/-- For r > 2M, we have r > 0 -/
theorem r_pos_of_exterior (s : SchwarzschildData) (r : ℝ)
    (hr : r > schwarzschildRadius s) : r > 0 := by
  have := schwarzschildRadius_pos s; linarith

/-- The Schwarz factor is strictly positive in the exterior region -/
theorem schwarzFactor_pos (s : SchwarzschildData) (r : ℝ)
    (hr : r > schwarzschildRadius s) : schwarzFactor s r > 0 := by
  have hr_pos : r > 0 := r_pos_of_exterior s r hr
  unfold schwarzFactor schwarzschildRadius at *
  have hne : r ≠ 0 := ne_of_gt hr_pos
  field_simp
  linarith

/-- g_tt is strictly negative in the exterior (timelike direction) -/
theorem g_tt_neg (s : SchwarzschildData) (r : ℝ)
    (hr : r > schwarzschildRadius s) : g_tt s r < 0 := by
  unfold g_tt; linarith [schwarzFactor_pos s r hr]

/-- g_rr is strictly positive in the exterior (spacelike direction) -/
theorem g_rr_pos (s : SchwarzschildData) (r : ℝ)
    (hr : r > schwarzschildRadius s) : g_rr s r > 0 := by
  unfold g_rr; exact inv_pos.mpr (schwarzFactor_pos s r hr)

/-- g_θθ is strictly positive for r > 0 -/
theorem g_θθ_pos (s : SchwarzschildData) (r : ℝ)
    (hr : r > schwarzschildRadius s) : g_θθ s r > 0 := by
  unfold g_θθ
  exact pow_pos (r_pos_of_exterior s r hr) 2

/-- g_φφ is strictly positive for r > 0 and θ ∉ {0, π} -/
theorem g_φφ_pos (s : SchwarzschildData) (r θ : ℝ)
    (hr : r > schwarzschildRadius s) (hθ : sin θ ≠ 0) :
    g_φφ s r θ > 0 := by
  unfold g_φφ
  apply mul_pos (pow_pos (r_pos_of_exterior s r hr) 2)
  exact sq_pos_of_ne_zero hθ

/-- g_tt · g_rr = -1 in the exterior region (the tt and rr components
    are mutual inverses up to sign) -/
theorem g_tt_mul_g_rr (s : SchwarzschildData) (r : ℝ)
    (hr : r > schwarzschildRadius s) : g_tt s r * g_rr s r = -1 := by
  unfold g_tt g_rr
  have hf := schwarzFactor_pos s r hr
  rw [neg_mul, mul_inv_cancel₀ (ne_of_gt hf)]

/-! ## Metric nondegeneracy

  The determinant of the diagonal metric is
    det(g) = g_tt · g_rr · g_θθ · g_φφ = -r⁴ sin²θ
  which is nonzero for r > 0 and sin θ ≠ 0.
-/

/-- The product of all four diagonal components (metric determinant) -/
def metricDet (s : SchwarzschildData) (r θ : ℝ) : ℝ :=
  g_tt s r * g_rr s r * g_θθ s r * g_φφ s r θ

/-- The metric determinant is nonzero in the exterior with sin θ ≠ 0 -/
theorem metricDet_ne_zero (s : SchwarzschildData) (r θ : ℝ)
    (hr : r > schwarzschildRadius s) (hθ : sin θ ≠ 0) :
    metricDet s r θ ≠ 0 := by
  unfold metricDet
  rw [g_tt_mul_g_rr s r hr]
  unfold g_θθ g_φφ
  intro h
  have hr_pos := r_pos_of_exterior s r hr
  have h1 : r ^ 2 > 0 := pow_pos hr_pos 2
  have h2 : (sin θ) ^ 2 > 0 := sq_pos_of_ne_zero hθ
  have h3 : r ^ 2 * (sin θ) ^ 2 > 0 := mul_pos h1 h2
  nlinarith

/-! ## Flat-space (Minkowski) limit

  As r → ∞, the Schwarzschild metric approaches the Minkowski metric:
  - schwarzFactor s r → 1
  - g_tt s r → -1
  - g_rr s r → 1

  We prove these pointwise convergence statements using Filter.Tendsto.
-/

open Filter Topology

/-- 2M/r tends to 0 as r → ∞ -/
private theorem tendsto_2M_div_r (s : SchwarzschildData) :
    Tendsto (fun r => 2 * s.M / r) atTop (nhds 0) := by
  have : (fun r => 2 * s.M / r) = (fun r => 2 * s.M * r⁻¹) := by ext; ring
  rw [this, show (0 : ℝ) = 2 * s.M * 0 from by ring]
  exact tendsto_inv_atTop_zero.const_mul _

/-- The Schwarz factor tends to 1 as r → ∞ -/
theorem schwarzFactor_tendsto_one (s : SchwarzschildData) :
    Tendsto (schwarzFactor s) atTop (nhds 1) := by
  have h0 := tendsto_2M_div_r s
  have : Tendsto (fun r => 1 - 2 * s.M / r) atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub h0
  simp only [sub_zero] at this
  exact this.congr (fun _ => rfl)

/-- g_tt tends to -1 as r → ∞ (Minkowski time-time component) -/
theorem g_tt_tendsto_neg_one (s : SchwarzschildData) :
    Tendsto (g_tt s) atTop (nhds (-1)) := by
  unfold g_tt
  exact (schwarzFactor_tendsto_one s).neg

/-- g_rr tends to 1 as r → ∞ (Minkowski radial component) -/
theorem g_rr_tendsto_one (s : SchwarzschildData) :
    Tendsto (g_rr s) atTop (nhds 1) := by
  unfold g_rr
  rw [show (1 : ℝ) = (1 : ℝ)⁻¹ from by norm_num]
  exact (schwarzFactor_tendsto_one s).inv₀ one_ne_zero

/-! ## Connection to S² from Tier 1

  The angular part of the Schwarzschild metric is r² dΩ², where
  dΩ² = dθ² + sin²θ dφ² is the round metric on S².

  At fixed (t, r) with r > 2M, the angular sector is a 2-sphere of
  radius r. We connect this to the Tier 1 S² definitions:
  - Gaussian curvature of a sphere of radius r is 1/r²
  - Area of the angular sector is 4πr²
-/

/-- The angular metric factor at radius r: the metric on the r-sphere
    is r² times the unit-sphere metric. This is the coefficient
    relating Schwarzschild angular geometry to Sphere.S2. -/
def angularScaleFactor (_s : SchwarzschildData) (r : ℝ) : ℝ := r ^ 2

/-- The angular scale factor is positive in the exterior -/
theorem angularScaleFactor_pos (s : SchwarzschildData) (r : ℝ)
    (hr : r > schwarzschildRadius s) :
    angularScaleFactor s r > 0 := by
  unfold angularScaleFactor
  exact pow_pos (r_pos_of_exterior s r hr) 2

/-- The Gaussian curvature of the r-sphere matches Tier 1's formula -/
theorem angularSector_curvature (s : SchwarzschildData) (r : ℝ)
    (hr : r > schwarzschildRadius s) :
    Sphere.gaussianCurvature r = 1 / r ^ 2 :=
  Sphere.gaussianCurvature_sphere r (r_pos_of_exterior s r hr)

/-- The area of the angular sector at radius r matches Tier 1's formula -/
theorem angularSector_area (s : SchwarzschildData) (r : ℝ)
    (hr : r > schwarzschildRadius s) :
    Sphere.sphereArea r = 4 * Real.pi * r ^ 2 :=
  Sphere.sphere_area_formula r (r_pos_of_exterior s r hr)

/-! ## Event horizon properties -/

/-- The Schwarz factor vanishes at the horizon -/
theorem schwarzFactor_at_horizon (s : SchwarzschildData) :
    schwarzFactor s (schwarzschildRadius s) = 0 := by
  unfold schwarzFactor schwarzschildRadius
  have hM := s.hM
  have hne : (2 * s.M) ≠ 0 := by linarith
  rw [div_self hne, sub_self]

/-- The Schwarz factor is negative inside the horizon (for 0 < r < 2M) -/
theorem schwarzFactor_neg_interior (s : SchwarzschildData) (r : ℝ)
    (hr_pos : r > 0) (hr_int : r < schwarzschildRadius s) :
    schwarzFactor s r < 0 := by
  unfold schwarzFactor schwarzschildRadius at *
  rw [sub_neg]
  rwa [one_lt_div hr_pos]

/-! ## Schwarzschild metric as a diagonal pseudo-metric

  We assemble the Schwarzschild metric into the diagMetric framework
  from Lorentz.lean. At a given spacetime point (r, θ) in the exterior,
  the diagonal metric components define a Lorentz-signature bilinear form
  on the tangent space ≅ ℝ⁴.
-/

/-- The Schwarzschild diagonal metric components at a point (r, θ) -/
def schwarzDiag (s : SchwarzschildData) (r θ : ℝ) : Fin 4 → ℝ
  | ⟨0, _⟩ => g_tt s r
  | ⟨1, _⟩ => g_rr s r
  | ⟨2, _⟩ => g_θθ s r
  | ⟨3, _⟩ => g_φφ s r θ

/-- The Schwarzschild metric at (r, θ) as a bilinear form on ℝ⁴ -/
def schwarzMetricAt (s : SchwarzschildData) (r θ : ℝ) : R4 → R4 → ℝ :=
  diagMetric (schwarzDiag s r θ)

/-- The Schwarzschild metric is symmetric at every point -/
theorem schwarzMetricAt_symm (s : SchwarzschildData) (r θ : ℝ) (u v : R4) :
    schwarzMetricAt s r θ u v = schwarzMetricAt s r θ v u :=
  diagMetric_symm _ u v

/-- The Schwarzschild metric is nondegenerate in the exterior -/
theorem schwarzMetricAt_nondegenerate (s : SchwarzschildData) (r θ : ℝ)
    (hr : r > schwarzschildRadius s) (hθ : sin θ ≠ 0)
    (u : R4) (hu : ∀ v : R4, schwarzMetricAt s r θ u v = 0) : u = 0 := by
  apply diagMetric_nondegenerate (schwarzDiag s r θ) _ u hu
  intro i
  fin_cases i
  · -- i = 0: g_tt < 0, hence ≠ 0
    simp only [schwarzDiag]; exact ne_of_lt (g_tt_neg s r hr)
  · -- i = 1: g_rr > 0, hence ≠ 0
    simp only [schwarzDiag]; exact ne_of_gt (g_rr_pos s r hr)
  · -- i = 2: g_θθ > 0, hence ≠ 0
    simp only [schwarzDiag]; exact ne_of_gt (g_θθ_pos s r hr)
  · -- i = 3: g_φφ > 0, hence ≠ 0
    simp only [schwarzDiag]; exact ne_of_gt (g_φφ_pos s r θ hr hθ)

/-- The Schwarzschild metric has Lorentz signature in the exterior:
    exactly one negative diagonal entry (g_tt) and three positive ones -/
theorem schwarzDiag_signature (s : SchwarzschildData) (r θ : ℝ)
    (hr : r > schwarzschildRadius s) (hθ : sin θ ≠ 0) :
    (Finset.univ.filter (fun i : Fin 4 => schwarzDiag s r θ i < 0)).card = 1 ∧
    (Finset.univ.filter (fun i : Fin 4 => schwarzDiag s r θ i > 0)).card = 3 := by
  have htt := g_tt_neg s r hr
  have hrr := g_rr_pos s r hr
  have hθθ := g_θθ_pos s r hr
  have hφφ := g_φφ_pos s r θ hr hθ
  constructor
  · -- Exactly one negative entry
    convert_to ({(⟨0, by omega⟩ : Fin 4)} : Finset (Fin 4)).card = 1
    · congr 1
      ext i; fin_cases i <;> (simp [schwarzDiag, *]; try linarith)
    · simp
  · -- Exactly three positive entries
    convert_to ({(⟨1, by omega⟩ : Fin 4), ⟨2, by omega⟩, ⟨3, by omega⟩} : Finset (Fin 4)).card = 3
    · congr 1
      ext i; fin_cases i <;> (simp [schwarzDiag, *]; try linarith)
    · simp

end

end Schwarzschild
