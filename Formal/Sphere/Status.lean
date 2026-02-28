/-
  Tier 1 — The Sphere: Status

  Import aggregator for Tier 1. All files compile with zero sorry.

  Proven:  ~45 theorems/constructions (inner product preservation, norm preservation,
           isometry, sphere membership, compactness, connectivity, path-connectivity,
           great circle parametrization, periodicity, uniqueness, z-coordinate bounds,
           O(3) transitivity via Householder reflection, geodesic uniqueness via
           orthogonal complement dimension argument,
           geometric bridge constructions A1–A3 on ↥S², A4 fractal boundary via
           ℕ-indexed polynomial degree space on the Riemann sphere, extended bridge
           A5–A7 on sphere-derived categories with radiation, coupling, circulation)
  Axioms:  3 (Mathlib gaps: curvature, Gauss-Bonnet, geodesic identification)
  Sorry:   0

  Last verified: 2026-02-28

  ## What resists

  1. **Symmetry-breaking is necessary for A2 (Closure).**
     S² has maximal continuous symmetry: O(3) acts transitively on points. In the
     full isometry group, every point can be mapped to every other, which means
     there is no intrinsic ordering that distinguishes "closing" from "non-closing"
     morphisms. To construct Closure on ↥S², we must break symmetry by choosing a
     frame — here, the z-axis — inducing a height preorder. This is the central
     structural finding: the informal claim "geodesics close" becomes categorical
     only after a choice of observation frame. The z-axis is justified by O(3)
     transitivity (any other axis gives an isomorphic result), but the *choice
     itself* cannot be eliminated.

  2. **PiLp/WithLp abstraction barrier.**
     EuclideanSpace ℝ (Fin 3) is PiLp 2 (Fin 3 → ℝ), which is WithLp 2 (Fin 3 → ℝ).
     While this is definitionally equal to (Fin 3 → ℝ), the norm and inner product
     instances differ from the Pi-type defaults (sup norm vs L2 norm). Extracting
     components requires explicit WithLp.equiv coercions, and simp lemmas for
     EuclideanSpace.single loop when combined with EuclideanSpace.toLp_single.
     The workaround: two-stage simp (first `simp only [EuclideanSpace.single]`,
     then `simp`). The zCoord_le_one proof navigates this by decomposing the inner
     product via PiLp.inner_apply + Fin.sum_univ_three, then using linarith with
     mul_self_nonneg to extract the component bound.

  3. **Mathlib gaps that forced axiomatization (3 remain).**
     - Gaussian curvature: no Riemannian curvature in Mathlib.
     - Gauss-Bonnet: no integration on Riemannian manifolds.
     - Geodesic identification: no Riemannian geodesics. Great circles are *proved*
       to be periodic curves on S², but the statement "these are the geodesics"
       cannot be formalized without a geodesic notion.
     - ~~Geodesic uniqueness~~: NOW PROVED in Geodesics.lean via orthogonal
       complement dimension argument (submodule of codim 1 is unique).
     - ~~O(3) transitivity~~: NOW PROVED in Symmetry.lean via Householder
       reflection (LinearIsometryEquiv constructed explicitly).

  4. **A4 (Fractal Boundary) now bridged to S² via Riemann sphere dynamics.**
     The boundary category D = ℕ models polynomial degree on the Riemann sphere
     Ĉ ≅ S². Endofunctor inexhaustibility is proved via the successor functor:
     for any G : ℕ ⥤ ℕ, the composite G ⋙ succ disagrees with G at object 0
     (G.obj 0 + 1 ≠ G.obj 0). The boundary functor S2Pt ⥤ ℕ is constant (every
     point at base resolution 0) — the fractal structure lives in ℕ, not in the
     map. Julia set theory (the formal link between polynomial degree and
     boundary complexity) is absent from Mathlib, so the connection is
     interpretive. See BridgeA4.lean for details and resistance documentation.

  5. **Opacity models the ball, not the universe.**
     The A3 construction (S² ⊕ {center}) models the sphere enclosing its center:
     the surface cannot "see" the interior point. This faithfully captures
     "‖0‖ = 0 ≠ 1" but does not capture the full informal claim about S² dividing
     E³ into interior and exterior (which would require the Jordan-Brouwer
     separation theorem, absent from Mathlib for manifolds).
-/

import Formal.Sphere.Geometry
import Formal.Sphere.Geodesics
import Formal.Sphere.Symmetry
import Formal.Sphere.Bridge
import Formal.Sphere.BridgeA4
import Formal.Sphere.BridgeExtended
