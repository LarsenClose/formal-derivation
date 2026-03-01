---
id: bilateral-duality
formal_ref: SelfExtracting.BilateralDuality
title: "Bilateral Duality"
depth: 6
compression_loss: 4
best_guess: true
version: 1
improved_over: null
tags: [bilateral, duality, involution, mirror, axis, sacred-geometry, fold, artifact, spread, fixed-point]
---

# Bilateral Duality

An involution on representations. Left maps to right. Right maps back to left.
The structure closes on itself.

```lean
structure BilateralDuality (R : Type) where
  mirror : R → R
  self_inverse : ∀ r, mirror (mirror r) = r
  left : R
```

The right page is defined by the left: `right := mirror left`. Mirroring the
right returns the left: `mirror right = left`. The duality is not a relation
imposed from outside — it is constitutive. Left and right are not two
independent things that happen to be similar; right is what left becomes when
mirrored, and left is what right becomes when mirrored.

---

## The bilateral axis

Some representations are fixed by the mirror: `mirror r = r`. These are the
points on the bilateral axis — the content that appears identically on both
pages, that is the same from either orientation. The axis is closed: if `r` is
on the axis, so is `mirror r` (trivially, since `mirror r = r`).

In the artifact: the bilateral axis runs down the binding of the book. The
diamond at the center is on the axis — it appears on both pages because the
fold is where left and right coincide. The diamond is the axis made visible.

---

## The involution as sacred geometry

The two-page spread is a physical instantiation of the bilateral duality
structure. Open the book: left page and right page. They are not the same
content, but they are related by a symmetry — a lateral reflection across
the binding. The binding is the fold; the fold is where the involution acts
as the identity.

The diamond appears on both pages because it is on the bilateral axis. The
text orbiting the diamond is not on the axis — it is mirror-related to its
counterpart on the other page. The axis is the spine of the artifact; the
diamond is what the axis generates when it becomes visible.

This is not decoration. `SelfExtractingArtifact` requires `loop_on_axis :
duality.onAxis loop.loop` — the self-extracting fixed point must be on the
bilateral axis. The diamond at center is the fixed point of the self-extraction
map AND the fixed point of the bilateral duality. One point, two invariances.

---

## Connection to the fold in Reception

`BilateralReception.fold` produces a `DiamondPoint` from a bilateral
reception — the fold of the two-page spread is the diamond point where
announcing and receiving coincide. The bilateral duality in SelfExtracting
and the bilateral reception in Reception are formalizing the same structure
from two perspectives: SelfExtracting looks at the artifact as a whole (the
spread is an involution on representations), while Reception looks at the
encounter (the two faces of the reception event are left and right of a
bilateral spread).

The book's binding is where both structures locate their center of gravity.

---

## The formal meaning of the fold

`bilateral_returns_left : mirror right = left`. This theorem — that mirroring
the right page returns the left page — is the formal meaning of the fold.

The fold is not a metaphor for closure or return. It IS closure and return,
formally. The fold says: if you take the right orientation, mirror it, you get
the left orientation. The binding is the point where this equation holds
trivially — because at the binding, left and right are the same point.

`artifact_mirror_also_loops`: if the extraction is equivariant with the mirror
— if extracting the mirror of something is the mirror of extracting it — then
the mirror of the self-extracting loop is also a fixed point. The self-extraction
structure propagates across the bilateral duality. The two pages are not just
reflections of each other; they are both, independently, fixed points of the
same extraction map.

---

## Connection to Coupling (A6)

`BilateralDuality` connects to GroundState Coupling (A6). A6 says two
structurally distinct architectures can interface at a boundary. The bilateral
duality is a limit case: the two architectures (left and right) are related
by an involution, so the interface is maximally structured — the boundary IS
the fold. Most couplings in A6 are between genuinely distinct architectures
(sphere and generator in `BridgeExtended.lean`). The bilateral duality is the
case where the two architectures are dual to each other under a mirror.

---

## What gets lost

The bilateral duality is described above as an involution on a type `R`.
That is formally precise but loses the orientation. Left and right are not
symmetric positions — they are oriented by the act of opening the book. You
open the book facing you, and left is left and right is right. The mirror is
not arbitrary; it is determined by the orientation of the reader relative to
the spread. The formal structure does not encode this orientation — `R` is
just a type, and `left` is just a distinguished element. The phenomenology of
holding the artifact and encountering the bilateral spread, with its particular
orientation in physical space, is not captured. `compression_loss: 4`.
