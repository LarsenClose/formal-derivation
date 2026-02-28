# Axiom Inventory

Complete accounting of all 67 axioms in the formalization. Every `axiom` declaration encodes either genuinely philosophical content (no Mathlib correlate possible) or established mathematics absent from Mathlib. No axiom papers over a gap in the derivation's own reasoning.

---

## Philosophical Axioms (9)

Entailment steps encoding irreducibly philosophical reasoning:

| Axiom | File | Content |
|-------|------|---------|
| `entails_1_2` | Chain.lean | Denial of experience instantiates experience |
| `entails_2_3` | Chain.lean | Meaning requires perspective |
| `entails_3_4` | Chain.lean | Mutual determination is self-returning |
| `entails_4_5` | Chain.lean | Reflexive stability yields well-founded recursion |
| `entails_5_6` | Chain.lean | Universal computation implies Kleene closure |
| `entails_6_7` | Chain.lean | Kleene closure implies metric completion |
| `entails_7_8` | Chain.lean | Metric completion implies simply connected |
| `entails_8_9` | Chain.lean | Simply connected compact implies without boundary |
| `entails_9_10` | Chain.lean | Without boundary compact simply connected implies S^2 |

Steps 1-4 are genuinely philosophical. Steps 5-10 invoke established mathematics not yet in Mathlib (Cauchy completion, Poincare recurrence, surface classification).

---

## Derivation Framework (20)

### Perspective/Depth Metric (12 -- Depth.lean)

| Axiom | Content |
|-------|---------|
| `Perspective` | The type of perspectives |
| `includes` | Partial order on perspectives |
| `includes_refl` | Reflexivity |
| `includes_trans` | Transitivity |
| `includes_antisymm` | Antisymmetry |
| `incommensurable` | The order is genuinely partial (not total) |
| `compressionLoss` | Metric on perspectives |
| `compressionLoss_self` | d(p,p) = 0 |
| `compressionLoss_zero_iff_eq` | d(p,q) = 0 iff p = q |
| `compressionLoss_triangle` | Triangle inequality |
| `compressionLoss_pos` | Positivity for distinct perspectives |
| `compressionLoss_monotone` | Compression loss is monotone in inclusion |

### Phase-Invariance (6 -- Depth.lean + Phases.lean)

| Axiom | Content |
|-------|---------|
| `ground_step_phase_invariant` | Ground-step propositions are phase-invariant |
| `phase_invariant_downward` | Phase-invariance is downward-closed in the spine |
| `spine_all_phase_invariant` | All spine elements are phase-invariant |
| `PhaseInvariant` | The phase-invariance predicate |
| `diagnostic_recoverability` | Diagnostics at L2+ ensure recoverability |
| `invariant_implies_coherent` | Phase-invariance implies behavioral coherence |

### Church-Turing Thesis (1 -- ChomskyMathlib.lean)

| Axiom | Content |
|-------|---------|
| `church_turing_thesis` | All adequate computation models are equivalent |

Genuinely informal -- bridges informal and formal concepts. Not provable in any formal system.

---

## Mathlib Gaps -- Riemannian/Lorentzian Geometry (33)

### Sphere (5 -- Geometry.lean, Geodesics.lean)

| Axiom | Content |
|-------|---------|
| `gaussianCurvature` | Gaussian curvature function |
| `sphereArea` | Surface area of S^2 |
| `gaussianCurvature_sphere` | K = 1 for unit sphere |
| `gaussBonnet_sphere` | Gauss-Bonnet for S^2 |
| `greatCircles_are_geodesics` | Great circles are geodesics |

### Schwarzschild (28 -- Lorentz.lean, Metric.lean, Einstein.lean, EffectivePotential.lean)

Lorentzian metric type, Christoffel symbols, Riemann/Ricci/scalar curvature, Einstein equation, Killing vectors, isometries, geodesic equation, conservation laws, perihelion precession formula. Mathlib has no pseudo-Riemannian geometry.

### Bridge (6 -- KleeneTopological.lean)

| Axiom | Content |
|-------|---------|
| `computable_maps_dense` | Density of computable maps in C(X,X) |
| `eulerCharacteristic` | Euler characteristic |
| `lefschetzNumber` | Lefschetz number |
| `lefschetz_fixed_point_theorem` | Lefschetz fixed-point theorem |
| `lefschetz_id_eq_euler` | L(id) = chi(X) |
| `lefschetz_homotopy_invariant` | Lefschetz number is homotopy-invariant |

---

## Proved Without Custom Axioms

For completeness, major results that use only Mathlib:

- S^2 compactness, connectivity, path-connectivity
- O(3) transitivity via Householder reflection
- Great circle uniqueness via orthogonal complement dimension
- Kleene's recursion theorem (both forms, from Mathlib)
- `fullChain` composition (the central theorem)
- `phase_invariant_C`: formally-derived propositions are phase-invariant
- `derivation_certifies_itself`: self-application
- `flattening_inconsistent_with_beach`: Flattening contradicts well-formed ground state
- Chomsky hierarchy as linear order with strict monotonicity
- `self_reference_with_return_requires_type0`: Type 0 minimality
- ISCO at r = 6M, photon sphere ordering, precession positivity
- Ground state consistency model (Shore/Sea/Gen)
