---
id: full-chain
formal_ref: DerivationChain.fullChain
title: "The Derivation Chain"
depth: 9
compression_loss: 6
best_guess: true
version: 1
improved_over: null
tags: [chain, derivation, there-is, sphere, s2, computation, topology, geometry, ground-state]
---

# The Derivation Chain

From "there is" to the geometry of spacetime in ten steps.

```
theorem fullChain (h : Nonempty ThereIs) : Nonempty SphereIsS2
```

That is the whole thing. What follows is a translation, not a proof.

---

**Step 1: There is.** Undeniable. The denial instantiates it. Pre-differentiated
unity of apprehending and apprehended. This is the only step that requires nothing
prior. Everything else is consequence.

**Step 2: Recognition yields terms.** To notice "there is" is already to
distinguish a noticing from what is noticed. Meaning requires a perspective;
a perspective requires at least two things to be in relation. Plurality is not
added — it is disclosed by recognition.

**Step 3: Mutual determination.** Each term exists only relative to the others.
No term has intrinsic identity beyond its relational position. The unity and the
multiplicity are co-given.

**Step 4: Reflexive stability.** Mutual determination applied to itself returns
itself. The recursion is well-founded: there is a base case (the primitive).

**Step 5: Universal computation.** Self-reference with return requires Chomsky
Type 0 — unrestricted rewriting, Turing completeness. Kleene's recursion theorem
gives closure under self-reference.

**Step 6: Configuration space.** Discrete elements + edit-distance + Cauchy
completion = compact metric space. The space of all possible states closes.

**Step 7: Recurrent orbits.** Kleene closure on a compact space yields recurrent
behavior (Poincaré recurrence). Orbits return.

**Step 8: Simply connected.** All consequence chains can close = all loops
contractible. π₁ = 0.

**Step 9: Without boundary.** No edge. Every configuration is reachable from
every other. The space has no privileged exterior.

**Step 10: S².** The unique compact, simply-connected surface without boundary.
This is not a choice — it is what the constraints determine.

---

Steps 1–4 are genuinely philosophical. Steps 5–10 invoke mathematics that is
established but not yet in Mathlib (Cauchy completion, Poincaré recurrence,
surface classification). The axiom inventory is in `AXIOMS.md`.

## What this is saying

The geometry of the ground state is not a physical postulate. It is what
self-reference with return, completed into a compact space with trivial fundamental
group, necessarily is. The sphere is not chosen because it looks right. It is
derived because the constraints leave nowhere else to go.

## What gets lost

The steps look sequential here. In the formal content they are nested — each step
carries all prior steps as structure, not just as predecessors in a chain. The
`DerivationSpine` in `Depth.lean` formalizes this: each step strictly includes
all previous ones. The word "then" in the English description is a compression of
"and carrying all of the above." `compression_loss: 6` for that collapse.
