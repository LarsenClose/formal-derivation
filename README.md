# formal-derivation

[![CI](https://github.com/LarsenClose/formal-derivation/actions/workflows/ci.yml/badge.svg)](https://github.com/LarsenClose/formal-derivation/actions/workflows/ci.yml)

Lean 4 formalization of the derivation chain from *Phase-Indexed Epistemology* (Close, 2026).

**Lean 4.28.0 / Mathlib v4.28.0 -- zero sorry -- 124 axioms (documented) -- 354 theorems**

Paper: [Phase-Indexed Epistemology](https://zenodo.org/records/18812866) (DOI: 10.5281/zenodo.18812866)

---

## What This Proves

A ten-step derivation from an undeniable primitive ("there is") to the geometry of spacetime (S^2), formalized as:

```lean
theorem fullChain (h : Nonempty ThereIs) : Nonempty SphereIsS2
```

The framework then certifies its own central theorem is phase-invariant:

```lean
theorem derivation_certifies_itself (Phase : Type*) [PhaseSpace Phase] (phi_0 : Phase) :
    PhaseInvariant (centralClaim Phase phi_0)
```

---

## Build

```
lake build    # zero errors, zero sorry
```

Requires Lean 4.28.0 (see `lean-toolchain`). Mathlib v4.28.0 is fetched automatically by Lake.

---

## Architecture

```
Formal.lean                              -- root import (all tiers)

Formal/
  GroundState/                           -- Tier 0: 7 axioms as categorical structures
    Axioms.lean                          -- A1-A7 over Mathlib categories
    Consistency.lean                     -- concrete model satisfying all 7
    Derived.lean                         -- identity existence, communication bound
    DerivedAdvanced.lean                 -- circulation monad, inexhaustible radiation

  Sphere/                                -- Tier 1: S^2 geometry
    Geometry.lean                        -- S^2 = Metric.sphere 0 1, compactness, connectivity
    Geodesics.lean                       -- great circles, periodicity, uniqueness
    Symmetry.lean                        -- O(3) action, transitivity (Householder)
    Bridge.lean                          -- A1-A3 on actual S^2
    BridgeA4.lean                        -- A4 via N-indexed resolution
    BridgeExtended.lean                  -- A5-A7 on sphere-derived categories
    Status.lean                          -- import aggregator

  Schwarzschild/                         -- Tier 2: Schwarzschild spacetime
    Lorentz.lean                         -- Lorentzian signature (-,+,+,+), Minkowski metric
    Metric.lean                          -- Schwarzschild metric, horizon, Minkowski limit
    Einstein.lean                        -- vacuum Ricci-flat, Birkhoff, spherical symmetry
    EffectivePotential.lean              -- V_eff, ISCO at r=6M, precession
    Status.lean                          -- import aggregator

  Bridge/                                -- Kleene-Topology Bridge
    KleeneTopological.lean               -- Kleene fixed-point (Mathlib), Lefschetz (axiom)

  Derivation/                            -- Derivation Chain
    Chain.lean                           -- 10-step chain, fullChain theorem
    Phases.lean                          -- phase-indexed propositions, translation, L0-L4
    Depth.lean                           -- perspective partial order, compression loss
    FailureModes.lean                    -- globalization, instrumentalization, flattening
    Chomsky.lean                         -- Chomsky Type 0 argument, Kleene connection
    ChomskyMathlib.lean                  -- Chomsky hierarchy as linear order
    SelfApplication.lean                 -- derivation_certifies_itself
    Resonance.lean                       -- coherent surplus, efflux propagation
    IntensionalShift.lean                -- MDL compression, extensional-to-intensional shift
    SelfExtracting.lean                  -- bilateral duality, Kleene loop, geometric invariance
    Reception.lean                       -- aperture, announcement, diamond-point reception

  Network/                               -- Empirical Bridge
    NetworkWitness.lean                  -- network-to-ground-state witness (7 evidence conditions)
    NetworkResonance.lean                -- structural resonance between network instances

  RF/                                    -- Radio-Frequency Derivation from S^2
    Maxwell.lean                         -- Maxwell equations, wave propagation
    AntennaTheory.lean                   -- antenna patterns, gain, reciprocity
    MIMOChannel.lean                     -- MIMO channel capacity, spatial multiplexing

  Stack/                                 -- Software Stack Derivation
    ComputationalBoundary.lean           -- crypto primitives, Rice limits, distinguishability
    KernelCapability.lean                -- OS layer hierarchy, process isolation, capabilities
    StackDerivation.lean                 -- full derivation from ThereIs to self-hosting stack
```

---

## Proof Inventory

| Tier | Content | Theorems | Axioms | Sorry |
|------|---------|----------|--------|-------|
| 0 -- GroundState | 7 axioms, consistency model, derived theorems | 16 | 0 | 0 |
| 1 -- Sphere | S^2 geometry, geodesics, symmetry, A1-A7 bridge | 24 | 5 | 0 |
| 2 -- Schwarzschild | Lorentzian signature, metric, Einstein, orbits | 54 | 28 | 0 |
| Bridge | Kleene topology, Lefschetz density | 5 | 6 | 0 |
| Derivation | Chain, phases, depth, failure modes, Chomsky, self-application, resonance, intensional shift, self-extracting loop, reception | 166 | 28 | 0 |
| Network | Empirical bridge, structural resonance | 17 | 8 | 0 |
| RF | Maxwell, antenna theory, MIMO channels | 28 | 41 | 0 |
| Stack | Crypto primitives, kernel layers, self-hosting derivation | 44 | 8 | 0 |
| **Total** | **37 files, 10139 lines** | **354** | **124** | **0** |

---

## Key Theorems

- **`fullChain`** : `Nonempty ThereIs -> Nonempty SphereIsS2` -- ten-step derivation
- **`derivation_certifies_itself`** : the framework certifies its own central theorem
- **`flattening_inconsistent_with_beach`** : flattening contradicts well-formed ground state
- **`phase_invariant_C`** : formally-derived propositions have phase-invariant validity
- **`self_reference_with_return_requires_type0`** : self-reference with return requires Chomsky Type 0
- **`O3_transitive`** : O(3) acts transitively on S^2 (Householder reflection)
- **`greatCircle_unique`** : two non-antipodal points determine a unique great circle
- **`ground_state_consistent`** : the seven-axiom system is satisfiable
- **`isco_at_6M`** : innermost stable circular orbit at r = 6M
- **`precession_positive`** : perihelion precession is positive for bound orbits
- **`resonance_chain_propagates`** : computational surplus propagates along resonance chains
- **`artifact_joint_fixed_point`** : self-extracting artifact is fixed under extraction and bilateral mirror
- **`reception_witnesses_thereis`** : reception event witnesses the ground "there is"
- **`hd_shift_is_mdl_instance`** : hyperdimensional shift instantiates MDL compression
- **`measured_network_has_locality`** : measured network data witnesses ground-state locality
- **`self_hosting_closure`** : derivation loop closes through Turing-complete self-verification
- **`semantic_property_has_distinct_witnesses`** : Rice nontriviality implies distinct programs
- **`crypto_creates_depth_boundary`** : cryptographic hardness creates irreversible depth boundary
- **`layer_depth_injective`** : OS abstraction layers have unique depths (strict hierarchy)

---

## Axiom Budget

| Category | Count | Status |
|----------|------:|--------|
| Philosophical entailment | 9 | Correctly axiomatized -- irreducibly philosophical |
| Perspective/depth metric | 12 | Defines the partial order and compression loss |
| Phase-invariance / diagnostics | 8 | Phase-invariance propagation and diagnostic adequacy |
| Church-Turing thesis | 1 | Genuinely informal |
| Riemannian geometry (Sphere) | 5 | Waiting on Mathlib |
| Lorentzian geometry (Schwarzschild) | 28 | Waiting on Mathlib |
| Computable analysis / Lefschetz (Bridge) | 6 | Waiting on Mathlib |
| Empirical bridge (Network) | 8 | Network-to-ground-state witness |
| Electromagnetic theory (RF) | 41 | Maxwell, antenna, MIMO -- waiting on Mathlib |
| Cryptographic hardness (Stack) | 3 | SHA-256, AES-256-GCM, Ed25519 -- standard assumptions |
| Open source / intensional access | 1 | Source availability enables structural examination |
| Kernel enforcement (Stack) | 2 | Process isolation, syscall-only crossing |
| Turing completeness / distinguishability | 2 | Lean is Turing-complete, distinguishability monotone |
| **Total** | **124** | |

Full axiom inventory: [AXIOMS.md](AXIOMS.md)

---

## Citation

```bibtex
@misc{close2026phase,
  author = {Close, Larsen James},
  title  = {Phase-Indexed Epistemology},
  year   = {2026},
  doi    = {10.5281/zenodo.18812866}
}
```

---

## License

CC BY 4.0
