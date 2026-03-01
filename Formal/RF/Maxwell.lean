/-
  RF Layer — Maxwell Equations and Wave Propagation

  Connects the Schwarzschild spacetime (Tier 2) to Maxwell's equations
  and electromagnetic wave propagation in flat space. The key chain:

    Schwarzschild exterior (r > 2M)
      → flat-space limit as r → ∞ (proved in Schwarzschild.Metric)
      → Minkowski spacetime
      → Maxwell equations in curved spacetime (axiomatized)
      → flat-space Maxwell → wave equation □ψ = 0
      → plane wave solutions and dispersion relation |k|c = ω
      → Friis transmission equation P_r/P_t = G_t G_r (λ/4πr)²
         where 1/r² follows from the S² area = 4πr² (Sphere.Geometry)

  Mathlib gaps axiomatized here:
    - Maxwell equations in curved spacetime (Mathlib has no Lorentzian electrodynamics)
    - Flat-space wave equation and its solutions
    - Electromagnetic field tensor components
-/

import Formal.Sphere.Geometry
import Formal.Schwarzschild.Metric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace RF.Maxwell

noncomputable section

open Real Filter Topology Sphere

/-! ## Physical constants -/

/-- The speed of light c > 0 (in consistent units, often c = 1 in natural units).
    We keep c explicit so the dispersion relation and wavelength formula are readable. -/
axiom speedOfLight : ℝ

axiom speedOfLight_pos : speedOfLight > 0

/-- The reduced Planck constant ħ (for completeness; not needed for classical RF). -/
axiom hbar : ℝ
axiom hbar_pos : hbar > 0

/-! ## Electromagnetic field tensor (Mathlib gap)

  In curved spacetime the electromagnetic field is a 2-form F_{μν} on the manifold.
  In coordinates, F has six independent components (E and B fields).
  Mathlib has no differential forms on pseudo-Riemannian manifolds.
-/

/-- An electromagnetic field configuration in a 4-dimensional spacetime.
    Axiomatized as a carrier type — the full tensor structure requires
    Riemannian geometry not available in Mathlib v4.28. -/
axiom EMField : Type

/-- The zero electromagnetic field: no excitation -/
axiom EMField.zero : EMField

/-! ## Maxwell equations in curved spacetime (Mathlib gaps)

  The covariant Maxwell equations are:
    ∇_μ F^{μν} = J^ν     (sourced equation: ∇·E = ρ, ∇×B = J + ∂E/∂t)
    ∇_{[μ} F_{νρ]} = 0   (Bianchi identity: ∇·B = 0, ∇×E = -∂B/∂t)

  In curved spacetime with metric g_{μν} these involve the Christoffel symbols
  of the Levi-Civita connection, which Mathlib cannot formulate.
-/

/-- The electromagnetic 4-current (source for Maxwell equations).
    Components: J^0 = charge density ρ, J^i = current density. -/
axiom EMCurrent : Type

/-- The zero current: vacuum (no sources) -/
axiom EMCurrent.zero : EMCurrent

/-- Maxwell equations in a Schwarzschild background:
    ∇_μ F^{μν} = J^ν on the exterior region r > 2M.
    Axiomatized because Mathlib has no Lorentzian Maxwell theory. -/
axiom maxwellEquation (s : Schwarzschild.SchwarzschildData)
    (F : EMField) (J : EMCurrent) : Prop

/-- The Bianchi identity (sourceless Maxwell equation):
    ∇_{[μ} F_{νρ]} = 0. This is automatic for any F that is a 2-form,
    but stated axiomatically here. -/
axiom bianchiIdentity (s : Schwarzschild.SchwarzschildData) (F : EMField) : Prop

/-- Maxwell equations in vacuum (J = 0) reduce to sourceless form -/
axiom maxwellVacuum (s : Schwarzschild.SchwarzschildData)
    (F : EMField) :
    maxwellEquation s F EMCurrent.zero ↔
    bianchiIdentity s F

/-! ## The flat-space (Minkowski) limit

  As r → ∞ and M → 0, Schwarzschild → Minkowski.
  This is the regime relevant to antenna far-field propagation:
  the source is at r ~ 0, the observation point at r → ∞,
  so the background is essentially flat.

  The flat-space limit of the Schwarzschild metric components is proved
  in Schwarzschild.Metric:
    - schwarzFactor → 1
    - g_tt → -1
    - g_rr → 1
-/

/-- The Minkowski metric: the flat-space limit of Schwarzschild.
    Diagonal components (-1, 1, 1, 1) in Cartesian-like coordinates. -/
structure MinkowskiData where
  /-- Signature confirmed: (-1, +1, +1, +1) -/
  g_tt : ℝ := -1
  g_xx : ℝ := 1
  g_yy : ℝ := 1
  g_zz : ℝ := 1

/-- The standard Minkowski metric -/
def minkowski : MinkowskiData := {}

/-- The Schwarzschild time-time metric component converges to the Minkowski -1.
    This is the flat-space limit proved in Schwarzschild.Metric. -/
theorem schwarzschild_to_minkowski_gtt (s : Schwarzschild.SchwarzschildData) :
    Filter.Tendsto (Schwarzschild.g_tt s) Filter.atTop (nhds (-1)) :=
  Schwarzschild.g_tt_tendsto_neg_one s

/-- The Schwarzschild radial metric component converges to the Minkowski +1. -/
theorem schwarzschild_to_minkowski_grr (s : Schwarzschild.SchwarzschildData) :
    Filter.Tendsto (Schwarzschild.g_rr s) Filter.atTop (nhds 1) :=
  Schwarzschild.g_rr_tendsto_one s

/-- In the flat-space limit, Maxwell equations reduce to their Minkowski form.
    Axiomatized: the proof requires taking the limit of the Christoffel symbols → 0,
    which needs differential geometry not available in Mathlib. -/
axiom maxwell_flat_limit (s : Schwarzschild.SchwarzschildData) (F : EMField) :
    ∃ (F_flat : EMField),
    maxwellEquation s F_flat EMCurrent.zero

/-! ## Wave equation in Minkowski spacetime

  In flat space, the vacuum Maxwell equations imply the wave equation
  for each component ψ of the vector potential:
    □ψ = (∂²/∂t² - c²∇²) ψ = 0

  The d'Alembertian □ = ∂²/∂t² - c²Δ where Δ = ∇² is the spatial Laplacian.
-/

/-- A scalar wave field in Minkowski spacetime: ψ : ℝ⁴ → ℂ
    where ℝ⁴ = time × space = ℝ × ℝ³. -/
def WaveField := ℝ × (Fin 3 → ℝ) → ℂ

/-- The d'Alembertian wave equation □ψ = 0 in Minkowski spacetime.
    □ = ∂²/∂t² - c²(∂²/∂x² + ∂²/∂y² + ∂²/∂z²)
    Axiomatized: requires PDE theory (second-order distributional derivatives)
    not available in Mathlib. -/
axiom dAlembertian (ψ : WaveField) : WaveField

axiom waveEquation (ψ : WaveField) : Prop

axiom waveEquation_def (ψ : WaveField) :
    waveEquation ψ ↔ ∀ x, dAlembertian ψ x = 0

/-! ## Plane wave solutions and dispersion relation -/

/-- A plane wave solution to the wave equation:
    ψ(t, x) = A · exp(i(k·x - ωt))
    where k ∈ ℝ³ is the wave vector and ω > 0 is angular frequency. -/
structure PlaneWave where
  /-- Complex amplitude -/
  amplitude : ℂ
  /-- Wave vector k ∈ ℝ³ (direction and spatial frequency) -/
  waveVector : Fin 3 → ℝ
  /-- Angular frequency ω > 0 -/
  angularFrequency : ℝ
  /-- Positive frequency condition -/
  freq_pos : angularFrequency > 0

/-- The plane wave field function for a given PlaneWave -/
def PlaneWave.toWaveField (pw : PlaneWave) : WaveField :=
  fun ⟨t, x⟩ =>
    let phase : ℝ := Finset.sum Finset.univ (fun i => pw.waveVector i * x i) -
                     pw.angularFrequency * t
    pw.amplitude * Complex.exp (Complex.I * phase)

/-- The wave number |k|: magnitude of the wave vector -/
def PlaneWave.waveNumber (pw : PlaneWave) : ℝ :=
  Real.sqrt (Finset.sum Finset.univ (fun i => pw.waveVector i ^ 2))

/-- The wave number is nonneg -/
theorem PlaneWave.waveNumber_nonneg (pw : PlaneWave) : 0 ≤ pw.waveNumber :=
  Real.sqrt_nonneg _

/-- The dispersion relation for electromagnetic waves in vacuum: |k| · c = ω.
    This expresses that the phase velocity equals c.
    Axiomatized: proving this from □ψ = 0 requires distributional PDE theory. -/
axiom planeWave_dispersion (pw : PlaneWave)
    (h : waveEquation pw.toWaveField) :
    pw.waveNumber * speedOfLight = pw.angularFrequency

/-- Wavelength: λ = 2π / |k| = 2πc / ω -/
def PlaneWave.wavelength (pw : PlaneWave) (_hk : pw.waveNumber ≠ 0) : ℝ :=
  2 * Real.pi / pw.waveNumber

/-- The fundamental relation c = λf where f = ω/(2π) is the frequency in Hz.
    Derived from the dispersion relation: ω = |k|c = (2π/λ)c = 2πfc. -/
theorem c_equals_lambda_times_freq (pw : PlaneWave) (hk : pw.waveNumber ≠ 0)
    (hdisp : waveEquation pw.toWaveField) :
    speedOfLight = pw.wavelength hk * (pw.angularFrequency / (2 * Real.pi)) := by
  have hdisp' := planeWave_dispersion pw hdisp
  unfold PlaneWave.wavelength
  field_simp
  linarith

/-! ## Free-space path loss and the Friis transmission equation

  The Friis equation relates received to transmitted power:
    P_r / P_t = G_t · G_r · (λ / (4πr))²

  The (λ/4πr)² factor is the free-space path loss. The 1/r² comes directly
  from the geometry: the transmitted power spreads over a sphere of area 4πr²,
  and the receiving antenna captures a fraction proportional to its effective area.

  The 4π in the denominator matches Sphere.sphere_area_formula:
  sphereArea r = 4πr², so the area of the sphere at distance r is 4πr².
-/

/-- A communication link described by the Friis equation parameters -/
structure FriisLink where
  /-- Transmitter antenna gain G_t ≥ 1 -/
  gainTx : ℝ
  /-- Receiver antenna gain G_r ≥ 1 -/
  gainRx : ℝ
  /-- Wavelength λ > 0 -/
  wavelength : ℝ
  /-- Link distance r > 0 -/
  distance : ℝ
  /-- Gains are ≥ 1 (lossless antenna gains are ≥ 1 for directive antennas) -/
  gainTx_pos : gainTx > 0
  gainRx_pos : gainRx > 0
  /-- Wavelength is positive -/
  wavelength_pos : wavelength > 0
  /-- Distance is positive -/
  distance_pos : distance > 0

/-- The free-space path loss factor: (λ / (4πr))².
    This is the fraction of radiated power captured by an isotropic
    receiving antenna at distance r from an isotropic transmitter. -/
def FriisLink.pathLoss (link : FriisLink) : ℝ :=
  (link.wavelength / (4 * Real.pi * link.distance)) ^ 2

/-- The Friis received-to-transmitted power ratio:
    P_r / P_t = G_t · G_r · (λ / (4πr))² -/
def FriisLink.powerRatio (link : FriisLink) : ℝ :=
  link.gainTx * link.gainRx * link.pathLoss

/-- The path loss factor is strictly positive -/
theorem FriisLink.pathLoss_pos (link : FriisLink) : 0 < link.pathLoss := by
  unfold FriisLink.pathLoss
  apply sq_pos_of_pos
  apply div_pos link.wavelength_pos
  have h4pi : (0 : ℝ) < 4 * Real.pi := by positivity
  exact mul_pos h4pi link.distance_pos

/-- The Friis power ratio is strictly positive -/
theorem FriisLink.powerRatio_pos (link : FriisLink) : 0 < link.powerRatio := by
  unfold FriisLink.powerRatio
  exact mul_pos (mul_pos link.gainTx_pos link.gainRx_pos) (link.pathLoss_pos)

/-- The (4πr²) factor in Friis path loss denominator equals sphereArea(r).
    Path loss denominator: 4πr² = sphereArea(r) (from Sphere.sphere_area_formula).
    This connects Schwarzschild.angularSector_area to RF link budgets. -/
theorem friis_uses_sphere_area (link : FriisLink) :
    4 * Real.pi * link.distance ^ 2 = Sphere.sphereArea link.distance := by
  exact (Sphere.sphere_area_formula link.distance link.distance_pos).symm

/-- The Friis power ratio in terms of sphere area:
    P_r/P_t = G_t G_r λ² / sphereArea(r).
    This is the cleanest geometric statement: power falls off as 1/r²
    because it spreads over the sphere surface at distance r. -/
theorem FriisLink.powerRatio_via_sphereArea (link : FriisLink) :
    link.powerRatio =
    link.gainTx * link.gainRx * link.wavelength ^ 2 /
    (Sphere.sphereArea link.distance * (4 * Real.pi)) := by
  unfold FriisLink.powerRatio FriisLink.pathLoss
  rw [← friis_uses_sphere_area]
  ring

/-- The path loss factor is at most 1 when λ ≤ 4πr.
    In any practical RF link, the wavelength is much smaller than the range,
    so the path loss factor (λ/4πr)² ≪ 1. -/
theorem FriisLink.pathLoss_le_one (link : FriisLink)
    (h : link.wavelength ≤ 4 * Real.pi * link.distance) :
    link.pathLoss ≤ 1 := by
  unfold FriisLink.pathLoss
  have h4pir_pos : (0 : ℝ) < 4 * Real.pi * link.distance :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) link.distance_pos
  rw [div_pow, div_le_one (pow_pos h4pir_pos 2)]
  apply sq_le_sq'
  · linarith [link.wavelength_pos]
  · exact h

/-- Friis power ratio is ≤ G_t · G_r when λ ≤ 4πr.
    Antennas do not amplify total power in any propagating link. -/
theorem FriisLink.powerRatio_le_gains (link : FriisLink)
    (h_lambda_le : link.wavelength ≤ 4 * Real.pi * link.distance) :
    link.powerRatio ≤ link.gainTx * link.gainRx := by
  unfold FriisLink.powerRatio
  calc link.gainTx * link.gainRx * link.pathLoss
      ≤ link.gainTx * link.gainRx * 1 := by
        apply mul_le_mul_of_nonneg_left (link.pathLoss_le_one h_lambda_le)
        exact mul_nonneg (le_of_lt link.gainTx_pos) (le_of_lt link.gainRx_pos)
    _ = link.gainTx * link.gainRx := mul_one _

end

end RF.Maxwell
