/-
  Tier 1 — The Sphere: Geometry

  S² as the unit sphere in E³, with topological and differential properties.
  Gaussian curvature and Gauss-Bonnet axiomatized (Mathlib gaps).

  Source: ~/ideal/ground_state/SPHERE.md
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.Connected

namespace Sphere

noncomputable section

/-! ## Core definitions -/

/-- Euclidean 3-space -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The unit 2-sphere in ℝ³ -/
def S2 : Set E3 := Metric.sphere 0 1

/-- Required by Mathlib's sphere manifold instance: finrank ℝ E3 = 2 + 1 -/
instance factFinrank : Fact (Module.finrank ℝ E3 = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- Module.rank of E3 exceeds 1, needed for sphere connectivity -/
theorem rank_E3_gt_one : 1 < Module.rank ℝ E3 := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]; norm_num

/-! ## Provable properties from Mathlib -/

/-- Sphere membership: p ∈ S² ↔ ‖p‖ = 1 -/
theorem mem_S2_iff (p : E3) : p ∈ S2 ↔ ‖p‖ = 1 := by
  simp [S2]

/-- S² is nonempty -/
theorem S2_nonempty : Set.Nonempty S2 :=
  ⟨EuclideanSpace.single (0 : Fin 3) 1, by
    simp [S2, EuclideanSpace.norm_single]⟩

/-- S² is compact (finite-dimensional normed space is proper, sphere is closed+bounded) -/
theorem S2_compact : IsCompact S2 :=
  isCompact_sphere 0 1

/-- S² is connected (sphere in dimension ≥ 2) -/
theorem S2_connected : IsConnected S2 :=
  isConnected_sphere rank_E3_gt_one 0 (by norm_num : (0 : ℝ) ≤ 1)

/-- S² is path-connected -/
theorem S2_pathConnected : IsPathConnected S2 :=
  isPathConnected_sphere rank_E3_gt_one 0 (by norm_num : (0 : ℝ) ≤ 1)

/-! ## Axiomatized properties (Mathlib gaps)

  These axioms encode well-known differential-geometric facts about S²
  that cannot be stated in Mathlib due to the absence of:
  - Gaussian/Riemannian curvature
  - Integration on Riemannian manifolds
  - Gauss-Bonnet theorem
-/

/-- Gaussian curvature of a sphere of radius r.
    Mathlib has no Riemannian curvature notion. -/
axiom gaussianCurvature : ℝ → ℝ

/-- Surface area of a sphere of radius r.
    Mathlib has no Riemannian integration. -/
axiom sphereArea : ℝ → ℝ

/-- Constant curvature: K(r) = 1/r² for a sphere of radius r > 0 -/
axiom gaussianCurvature_sphere : ∀ r : ℝ, r > 0 → gaussianCurvature r = 1 / r ^ 2

/-- Gauss-Bonnet for S²: ∫ K dA = 4π (Euler characteristic χ(S²) = 2) -/
axiom gaussBonnet_sphere : ∀ r : ℝ, r > 0 →
  gaussianCurvature r * sphereArea r = 4 * Real.pi

/-- Surface area derived from curvature and Gauss-Bonnet -/
theorem sphere_area_formula : ∀ r : ℝ, r > 0 → sphereArea r = 4 * Real.pi * r ^ 2 := by
  intro r hr
  have hK := gaussianCurvature_sphere r hr
  have hGB := gaussBonnet_sphere r hr
  have hr2 : r ^ 2 > 0 := pow_pos hr 2
  rw [hK] at hGB
  field_simp at hGB
  linarith

end

end Sphere
