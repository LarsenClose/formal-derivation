/-
  Tier 2 — Schwarzschild: Effective Potential

  The effective potential for radial motion in Schwarzschild spacetime,
  circular orbit conditions, ISCO, perihelion precession, and conservation laws.

  In geometric units (c = G = 1):
    V_eff(r) = -M/r + L²/(2r²) - ML²/r³

  The derivative conditions (dV/dr = 0, d²V/dr² = 0) yield the ISCO at r = 6M.
  Perihelion precession and conservation laws are axiomatized (require geodesic
  equation machinery not available in Mathlib).

  Source: Wald, General Relativity, Ch. 6; MTW, Gravitation, Ch. 25
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic

namespace Schwarzschild

noncomputable section

/-! ## Core definitions -/

/-- Parameters for Schwarzschild effective potential.
    M = mass of central body (M > 0)
    L = specific angular momentum of test particle (L ≥ 0)
    Both in geometric units (c = G = 1). -/
structure OrbitalParams where
  M : ℝ
  L : ℝ
  hM : M > 0
  hL : L ≥ 0

/-- Effective potential for radial geodesic motion in Schwarzschild spacetime.
    V_eff(r) = -M/r + L²/(2r²) - ML²/r³
    Valid for r > 0 (exterior to the singularity). -/
def V_eff (p : OrbitalParams) (r : ℝ) : ℝ :=
  -p.M / r + p.L ^ 2 / (2 * r ^ 2) - p.M * p.L ^ 2 / r ^ 3

/-- First derivative of V_eff with respect to r.
    dV/dr = M/r² - L²/r³ + 3ML²/r⁴ -/
def dV_eff (p : OrbitalParams) (r : ℝ) : ℝ :=
  p.M / r ^ 2 - p.L ^ 2 / r ^ 3 + 3 * p.M * p.L ^ 2 / r ^ 4

/-- Second derivative of V_eff with respect to r.
    d²V/dr² = -2M/r³ + 3L²/r⁴ - 12ML²/r⁵ -/
def d2V_eff (p : OrbitalParams) (r : ℝ) : ℝ :=
  -2 * p.M / r ^ 3 + 3 * p.L ^ 2 / r ^ 4 - 12 * p.M * p.L ^ 2 / r ^ 5

/-! ## Circular orbit condition

  Setting dV/dr = 0 and multiplying through by r⁴/M (for r > 0, M > 0):
    r² - (L²/M)r + 3L² = 0
  This quadratic in r gives the radii of circular orbits. -/

/-- The circular orbit equation: dV/dr = 0 is equivalent (for r > 0) to
    M r² - L² r + 3 M L² = 0, obtained by multiplying dV/dr = 0 through by r⁴. -/
theorem circular_orbit_condition (p : OrbitalParams) (r : ℝ) (hr : r > 0) :
    dV_eff p r = 0 ↔ p.M * r ^ 2 - p.L ^ 2 * r + 3 * p.M * p.L ^ 2 = 0 := by
  have hr2 : r ^ 2 > 0 := pow_pos hr 2
  have hr3 : r ^ 3 > 0 := pow_pos hr 3
  have hr4 : r ^ 4 > 0 := pow_pos hr 4
  constructor
  · intro h
    have : dV_eff p r * r ^ 4 = 0 := by rw [h, zero_mul]
    simp only [dV_eff] at this
    field_simp at this
    linarith
  · intro h
    simp only [dV_eff]
    field_simp
    nlinarith

/-! ## ISCO (Innermost Stable Circular Orbit)

  The ISCO satisfies both dV/dr = 0 and d²V/dr² = 0 simultaneously.
  For the Schwarzschild metric, this occurs at r = 6M with L² = 12M².

  We prove this by direct algebraic verification: plugging r = 6M and L² = 12M²
  into both derivative expressions yields zero. -/

/-- ISCO angular momentum squared: L² = 12M² at the ISCO. -/
def ISCO_L_sq (M : ℝ) : ℝ := 12 * M ^ 2

/-- ISCO radius: r_ISCO = 6M. -/
def ISCO_radius (M : ℝ) : ℝ := 6 * M

/-- At r = 6M with L² = 12M², the first derivative vanishes: dV/dr = 0.
    This confirms r = 6M is a circular orbit. -/
theorem ISCO_first_derivative_vanishes (M : ℝ) (hM : M > 0) :
    let r := ISCO_radius M
    let L_sq := ISCO_L_sq M
    M / r ^ 2 - L_sq / r ^ 3 + 3 * M * L_sq / r ^ 4 = 0 := by
  simp only [ISCO_radius, ISCO_L_sq]
  have hM2 : M ^ 2 > 0 := pow_pos hM 2
  have hM4 : M ^ 4 > 0 := pow_pos hM 4
  field_simp
  ring

/-- At r = 6M with L² = 12M², the second derivative vanishes: d²V/dr² = 0.
    Combined with dV/dr = 0, this confirms r = 6M is the marginally stable orbit. -/
theorem ISCO_second_derivative_vanishes (M : ℝ) (hM : M > 0) :
    let r := ISCO_radius M
    let L_sq := ISCO_L_sq M
    ((-2) * M / r ^ 3 + 3 * L_sq / r ^ 4 - 12 * M * L_sq / r ^ 5 = 0) := by
  simp only [ISCO_radius, ISCO_L_sq]
  have hM3 : M ^ 3 > 0 := pow_pos hM 3
  have hM5 : M ^ 5 > 0 := pow_pos hM 5
  field_simp
  ring

/-- The ISCO radius is outside the Schwarzschild radius (r_S = 2M).
    6M > 2M for M > 0. -/
theorem ISCO_outside_horizon (M : ℝ) (hM : M > 0) :
    ISCO_radius M > 2 * M := by
  simp only [ISCO_radius]; linarith

/-- The ISCO radius is positive for M > 0. -/
theorem ISCO_radius_pos (M : ℝ) (hM : M > 0) :
    ISCO_radius M > 0 := by
  simp only [ISCO_radius]; linarith

/-! ## Unstable circular orbits

  The photon sphere at r = 3M is the innermost circular orbit for massless particles.
  For massive particles, circular orbits exist between r = 3M and r = 6M but are
  unstable (d²V/dr² < 0 would need to be shown). We record the photon sphere radius. -/

/-- Photon sphere radius: r = 3M. The innermost unstable circular orbit. -/
def photon_sphere_radius (M : ℝ) : ℝ := 3 * M

/-- The photon sphere is inside the ISCO. -/
theorem photon_sphere_inside_ISCO (M : ℝ) (hM : M > 0) :
    photon_sphere_radius M < ISCO_radius M := by
  simp only [photon_sphere_radius, ISCO_radius]; linarith

/-- The photon sphere is outside the Schwarzschild radius. -/
theorem photon_sphere_outside_horizon (M : ℝ) (hM : M > 0) :
    photon_sphere_radius M > 2 * M := by
  simp only [photon_sphere_radius]; linarith

/-! ## Perihelion precession (axiomatized)

  The precession per orbit in Schwarzschild spacetime is:
    Δφ = 6πM / (a(1 - e²))
  where a = semi-major axis, e = eccentricity.

  Deriving this requires solving the orbit equation (Binet equation) perturbatively,
  which involves integrating the geodesic equation. This is beyond what can be
  proved from the effective potential alone. -/

/-- Semi-major axis and eccentricity of a bound orbit. -/
structure BoundOrbit where
  a : ℝ      -- semi-major axis
  e : ℝ      -- eccentricity
  ha : a > 0
  he_ge : e ≥ 0
  he_lt : e < 1  -- bound orbit requires e < 1

/-- Perihelion precession per orbit in Schwarzschild spacetime.
    Δφ = 6πM / (a(1 - e²))
    Axiomatized: derivation requires perturbative solution of the orbit equation. -/
axiom perihelion_precession : ℝ → BoundOrbit → ℝ

/-- The precession formula: Δφ = 6πM / (a(1 - e²)).
    This is the leading-order GR correction to Keplerian orbits. -/
axiom perihelion_precession_formula :
  ∀ (M : ℝ) (orb : BoundOrbit), M > 0 →
    perihelion_precession M orb = 6 * Real.pi * M / (orb.a * (1 - orb.e ^ 2))

/-- Precession is positive for prograde orbits (M > 0, bound orbit). -/
theorem precession_positive (M : ℝ) (orb : BoundOrbit) (hM : M > 0) :
    perihelion_precession M orb > 0 := by
  rw [perihelion_precession_formula M orb hM]
  apply div_pos
  · have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  · apply mul_pos
    · exact orb.ha
    · have : orb.e ^ 2 < 1 := by nlinarith [orb.he_ge, orb.he_lt]
      linarith

/-! ## Conservation laws (axiomatized)

  Along timelike geodesics in Schwarzschild spacetime:
  - The specific energy E = (1 - 2M/r)(dt/dτ) is conserved (Killing vector ∂_t)
  - The specific angular momentum L = r²(dφ/dτ) is conserved (Killing vector ∂_φ)

  These follow from the existence of Killing vectors, which requires the full
  geodesic equation and Killing's equation on the Schwarzschild metric.
  Axiomatized here. -/

/-- A geodesic in Schwarzschild spacetime, parametrized by proper time.
    Abstractly represented: the full definition requires the metric and
    Christoffel symbols. -/
axiom SchwarzschildGeodesic : ℝ → Type

/-- Specific energy along a geodesic: E = (1 - 2M/r)(dt/dτ). -/
axiom specificEnergy : ∀ (M : ℝ), SchwarzschildGeodesic M → ℝ → ℝ

/-- Specific angular momentum along a geodesic: L = r²(dφ/dτ). -/
axiom specificAngMomentum : ∀ (M : ℝ), SchwarzschildGeodesic M → ℝ → ℝ

/-- Energy conservation: E is constant along geodesics.
    Follows from the timelike Killing vector ∂/∂t of the Schwarzschild metric. -/
axiom energy_conservation :
  ∀ (M : ℝ) (γ : SchwarzschildGeodesic M) (τ₁ τ₂ : ℝ),
    specificEnergy M γ τ₁ = specificEnergy M γ τ₂

/-- Angular momentum conservation: L is constant along geodesics.
    Follows from the axial Killing vector ∂/∂φ of the Schwarzschild metric. -/
axiom angular_momentum_conservation :
  ∀ (M : ℝ) (γ : SchwarzschildGeodesic M) (τ₁ τ₂ : ℝ),
    specificAngMomentum M γ τ₁ = specificAngMomentum M γ τ₂

/-! ## Effective potential from conservation laws

  For a geodesic with constants E and L, the radial equation becomes:
    (1/2)(dr/dτ)² + V_eff(r) = (1/2)(E² - 1)
  This connects the abstract conservation laws to the concrete V_eff. -/

/-- The radial energy equation connects V_eff to the conserved quantities.
    (1/2)(dr/dτ)² = (1/2)(E² - 1) - V_eff(r)
    Axiomatized: requires the full metric + geodesic equation. -/
axiom radial_energy_equation :
  ∀ (p : OrbitalParams) (γ : SchwarzschildGeodesic p.M) (τ : ℝ),
    ∃ (r dr_dτ : ℝ), r > 0 ∧
      (1 / 2) * dr_dτ ^ 2 + V_eff p r =
      (1 / 2) * ((specificEnergy p.M γ τ) ^ 2 - 1)

end

end Schwarzschild
