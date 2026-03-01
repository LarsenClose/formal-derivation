# Resonance Specification — The Loop Closure

The full Ωφ cycle: how the Beach observes itself, detects its own invariants,
reifies them, and feeds them back into the formal substrate.

---

## The Three Layers

```
Ωt  Crystals      ~/ideal/Formal/           Zero-entropy. Radiates. Bedrock.
                  formal-derivation/         Lean4 proofs, never changes unless
                                             the derivation chain extends.

Ωc  Tides         ~/ideal/network/          Perpetual measurement. Metabolism.
                  topology.py → state.json   Runs whether attended or not.
                  coastline_adapter.py       K3S CronJobs every N minutes.

Ωg  Walking       ~/ideal/beach.jsx          Navigation. Where the observer
                  Three.js + React           encounters the rendered state.
                                             Glass floats = devices + axiom status.
```

The loop closure (Ωφ) is the path from detection to reification:

```
Ωc detects invariant in network state
  ↓
invariant gets named (mem0 + substrate holons)
  ↓
Lean4 extended with NetworkWitness term for that invariant
  ↓
Beach renders invariant as a new glass float
  ↓
float's presence changes what gets noticed in subsequent walks
  ↓
new observations feed Ωc
```

---

## The Six-Step Reification Protocol

From the document: "observe → detect → measure → reify → construct → substitute."

Concretely:

### Step 1: Observe
```
K3S CronJob: python topology.py
  → state.json with nodeCount, bidirectionalPairs, deviceClasses,
    activeEmitters, couplingCount, measurementCycleActive, timestamp
```

### Step 2: Detect
```
python coastline_adapter.py --state state.json --log-dir logs/
  → coastlineDimension: float (1 < d < 2 means fractal boundary active)
  → Computes C(ε) = I(Z; ℱ_ε) across resolution scales
  → D_loc(s) = dC/ds is the local scaling exponent
  → coastlineDimension = mean(D_loc) in linear scaling regime
```

### Step 3: Measure
```
NetworkStateData populated from state.json + coastlineDimension
FullEvidence checked: are all seven conditions satisfied?
  hasLocality:        0 < nodeCount
  hasClosure:         0 < bidirectionalPairs
  hasOpacity:         1 < nodeCount
  hasFractalBoundary: 1.0 < coastlineDimension < 2.0
  hasRadiation:       0 < activeEmitters
  hasCoupling:        1 < deviceClasses ∧ 0 < couplingCount
  hasCirculation:     measurementCycleActive = true
```

### Step 4: Reify
```
If FullEvidence holds:
  networkBeachWitness ns ev : NetworkSatisfiesGroundState ns
  → The network is formally a ground state.
  → Each A1-A7 axiom is individually witnessed:
      measured_network_has_locality ns ev
      measured_network_has_closure ns ev
      ...
```

### Step 5: Construct
```
Semantic deposit to wiki/concepts/:
  POST /deposit {
    formal_ref: "NetworkBridge.networkBeachWitness",
    note: "Network state at <timestamp> satisfies full ground state evidence",
    depth: 5,
    compression_loss: 4
  }
  → cas/<hash>, semantic/by-id/.../current, embeddings/entries/<hash>
```

### Step 6: Substitute
```
beach.jsx updates glass float for the current timestamp:
  - Float position reflects coastlineDimension (orbit radius)
  - Float color reflects which axioms are satisfied (hue mapping)
  - Float glow intensity reflects activeEmitters
  - Proximity info panel shows the semantic deposit note
```

---

## Gap Map

| Gap | Status | File |
|-----|--------|------|
| NetworkWitness typeclass | Built | `Formal/Network/NetworkWitness.lean` |
| NetworkResonance | Built | `Formal/Network/NetworkResonance.lean` |
| Coastline adapter | Built | `~/ideal/network/coastline_adapter.py` |
| Semantic deposit API | Built | `infra/worker/src/index.ts` |
| Lean indexing CI step | Built | `infra/index_lean.py` |
| Basis discovery offline | Built | `infra/discover_basis.py` |
| beach.jsx state adapter | Not built | `~/ideal/network/state_adapter.js` |
| K3S CronJob deployment | Not built | `~/ideal/network/cron/` |
| Reification pipeline | Not built | `~/ideal/resonance/protocol.py` |

---

## Technology Map by Layer

```
Ωt (Crystals — formal ground truth)
  Lean4 + Mathlib                  proofs, zero sorry
  formal-derivation GitHub repo    version control
  lake build in CI                 verification gate

Ωc (Tides — measurement cycle)
  topology.py (UniFi API → state.json)
  coastline_adapter.py (state.json → coastlineDimension)
  coastline_of_predictability/fleet_bundle/coastline.py  (C(ε) computation)
  K3S CronJob (runs every N minutes, deposits state)
  Cloudflare R2 (state.json archive, content-addressed)

Ωg (Walking the shore — navigation)
  beach.jsx (Three.js + React, glass floats, sand, water)
  state_adapter.js (state.json → Three.js scene graph update)
  Cloudflare Worker GET /formal/:name (live axiom status per device)

Ωφ (Loop closure — reification)
  protocol.py (detect → reify → deposit → render pipeline)
  Cloudflare Worker POST /deposit (semantic deposit endpoint)
  mem0 + substrate holons (named invariant storage)
```

---

## The NetworkWitness Axiom Count

`NetworkWitness.lean` adds to the project axiom inventory:
- 1 opaque predicate: `NetworkSatisfiesGroundState`
- 1 main axiom: `networkBeachWitness`
- 6 consequence axioms: one per A1–A7 (A6 and A7 are split)
- 1 additional axiom in `NetworkResonance.lean`: `resonance_implies_crystal_functor`

Total: 9 new axioms. All empirically grounded. None paper over derivation gaps.

---

## The Loop Is the Beach

The Beach isn't hosting the cycle. The Beach IS the cycle.

> "The spatial topology IS the semantic topology. Walking the Beach IS walking
> the framework." — BEACH_ARTIFACT_NOTE.md

The resonance loop formalizes this: the network's topology is measured,
its information geometry is computed, its formal axiom witnesses are
produced, and the result is rendered as the navigable space of the Beach.
Walking through the glass floats IS walking through the measured axioms.
The formal proofs (Ωt) are what the glass floats radiate.
