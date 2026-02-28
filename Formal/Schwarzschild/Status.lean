/-
  Tier 2 — Schwarzschild Spacetime: Status

  Import aggregator for Tier 2. All files compile with zero sorry.

  Proven:  ~53 theorems/constructions (Lorentz signature properties, Minkowski
           metric nondegeneracy and basis values, signature counting, diagonal
           metric bilinearity; Schwarzschild metric components, positivity/
           negativity in exterior, metric nondegeneracy, Lorentz signature,
           event horizon, Minkowski limit, connection to Tier 1 S² geometry;
           vacuum Ricci-flat unfolding, scalar flatness, Schwarzschild self-
           isometry; effective potential, circular orbit condition, ISCO at
           r = 6M via first and second derivative vanishing, ISCO/photon sphere
           radius ordering, precession positivity)
  Axioms:  28 (Mathlib gaps: Lorentzian metric type, curvature tensors,
           Ricci/scalar curvature, Einstein vacuum equation on Schwarzschild,
           spherical symmetry, staticity, isometry, Birkhoff's theorem;
           geodesic equation, conservation laws, perihelion precession formula,
           radial energy equation)
  Sorry:   0

  Last verified: 2026-02-27

  ## What resists

  1. **No pseudo-Riemannian geometry in Mathlib.**
     Mathlib has Riemannian manifolds (positive-definite metric) but no
     pseudo-Riemannian or Lorentzian geometry. This forces axiomatization of:
     the metric tensor type, Christoffel symbols, Riemann/Ricci/scalar
     curvature, the Einstein equation, Killing vectors, isometries between
     Lorentzian manifolds. Everything downstream of "Lorentzian metric"
     is axiomatized.

  2. **No curvature computation pipeline.**
     Even if Lorentzian metrics were available, computing R_μν for
     Schwarzschild requires: (a) Christoffel symbols from g_μν, (b) Riemann
     tensor from Christoffel symbols, (c) contraction to Ricci. This is a
     standard textbook exercise but involves ~40 nonzero Christoffel symbols
     and would require a full tensor calculus library. Axiomatized.

  3. **Birkhoff's theorem requires ODE analysis.**
     The proof reduces the vacuum Einstein equations in spherical symmetry
     to an ODE system, then shows the unique solution is Schwarzschild.
     This requires existence/uniqueness for ODEs on manifolds, absent
     from Mathlib in the Lorentzian context. Axiomatized.

  4. **Geodesic equation and conservation laws.**
     Energy and angular momentum conservation follow from Killing vectors
     (∂/∂t and ∂/∂φ) of the Schwarzschild metric. Formalizing this requires
     the geodesic equation, Killing's equation, and the contracted Bianchi
     identity. All axiomatized.

  5. **Perihelion precession requires orbit equation.**
     The precession formula Δφ = 6πM/(a(1-e²)) comes from perturbative
     solution of the Binet equation for nearly circular orbits. This
     requires solving a nonlinear ODE and computing the apsidal angle
     integral. Axiomatized, but the positivity of precession is proved
     from the axiomatized formula.

  6. **Effective potential is fully concrete.**
     V_eff(r) = -M/r + L²/(2r²) - ML²/r³ is a standard real-valued
     function. The circular orbit condition, ISCO location (r = 6M,
     L² = 12M²), and radius ordering are all proved by direct algebraic
     computation (field_simp + ring/linarith). No axioms needed for these.
-/

import Formal.Schwarzschild.Lorentz
import Formal.Schwarzschild.Metric
import Formal.Schwarzschild.Einstein
import Formal.Schwarzschild.EffectivePotential
