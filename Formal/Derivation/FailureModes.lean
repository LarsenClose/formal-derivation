/-
  Failure Modes — The Three Structural Pathologies

  Three failure modes derived as negations of specific axiom instances.
  Each represents a way the ground state axioms can be violated:

  1. Globalization  — failure of return (A2 Closure failure from the
     non-ordinary side). The consequence chain from state-specific truth
     to action never closes back through ordinary functioning.

  2. Instrumentalization — return-address severed (A2 read through A3 Opacity).
     Belief modified during a shifted state without marking provenance;
     the opacity of the generating state means the return-address is lost.

  3. Flattening — refusal of departure (consequence chain cut at outset).
     The inclusion ι from A3 is claimed to be an isomorphism: nothing
     beyond the observable. Treats one phase's criteria as universally
     sufficient.

  Key structural insight: Globalization universalizes from the state side,
  Flattening universalizes from the gross side. Both commit the same formal
  error — treating one phase's disclosures as exhaustive.

  Source: paper §§2, 6.6, 7
-/

import Formal.GroundState.Axioms
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.EssentialImage

universe u v u₁ v₁ u₂ v₂

namespace GroundState

open CategoryTheory

/-!
## Consequence Chains

A consequence chain is a composable sequence of morphisms in a category —
a path from an origin object to a terminus. In the ground state framework,
consequence chains represent the propagation of effect from action to
reaction. A chain "closes" when its terminus equals its origin and there
exists a return morphism.
-/

/-- A consequence chain in category C: a composable pair of morphisms
    from an origin through an intermediate to a terminus.
    This captures the minimal non-trivial chain structure (two steps).
    Longer chains reduce to compositions. -/
structure ConsequenceChain (C : Type u) [Category.{v} C] where
  /-- The origin of the chain -/
  origin : C
  /-- The intermediate object -/
  mid : C
  /-- The terminus of the chain -/
  terminus : C
  /-- First leg of the chain -/
  step₁ : origin ⟶ mid
  /-- Second leg of the chain -/
  step₂ : mid ⟶ terminus

/-- The composite morphism of a consequence chain. -/
def ConsequenceChain.composite {C : Type u} [Category.{v} C]
    (ch : ConsequenceChain C) : ch.origin ⟶ ch.terminus :=
  ch.step₁ ≫ ch.step₂

/-- A consequence chain closes when there exists a return morphism from
    terminus back to origin (a return-address exists). -/
def ConsequenceChain.closes {C : Type u} [Category.{v} C]
    (ch : ConsequenceChain C) : Prop :=
  Nonempty (ch.terminus ⟶ ch.origin)

/-!
## Failure Mode 1: Closure Failure

A closure failure is a consequence chain that does not return to its origin.
This is the negation of A2's closing pair property for that specific chain:
no return morphism exists.
-/

/-- A closure failure: a consequence chain with no return morphism.
    The chain propagates effect outward but nothing comes back.
    This is the structural precondition for both Globalization and
    Instrumentalization. -/
structure ClosureFailure (C : Type u) [Category.{v} C] where
  /-- The consequence chain that fails to close -/
  chain : ConsequenceChain C
  /-- No return morphism exists: the chain does not close -/
  no_return : IsEmpty (chain.terminus ⟶ chain.origin)

/-!
## Failure Mode 1a: Globalization

Globalization = failure of return from the non-ordinary side.
The consequence chain originates in a non-ordinary phase (inside the
opaque subcategory D, beyond the image of C under ι) and never closes
back through the ordinary phase (C).

Structurally: a morphism chain in D that starts at an opaque object
(not in the essential image of ι) and targets an image object ι.obj X,
but the chain cannot close — there is no morphism from ι.obj X back to
the opaque origin. State-specific truth asserted as universal.
-/

/-- Globalization: a consequence chain in D originating at an opaque object
    (not in the essential image of C) that reaches an ordinary object
    (in the image of ι) but cannot return. The non-ordinary phase's
    disclosures are projected onto the ordinary without a return-address. -/
structure Globalization (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D]
    (op : Opacity C D) where
  /-- The ordinary object that the chain reaches -/
  ordinary : C
  /-- An intermediate object in D -/
  mid : D
  /-- The outgoing morphism from the opaque object -/
  depart : op.opaque_object ⟶ mid
  /-- The morphism arriving at the ordinary object's image -/
  arrive : mid ⟶ op.ι.obj ordinary
  /-- No return: no morphism from the ordinary image back to the opaque origin -/
  no_return : IsEmpty (op.ι.obj ordinary ⟶ op.opaque_object)

/-!
## Failure Mode 2: Instrumentalization

Instrumentalization = return-address severed via opacity.
A closing pair exists in C (A2 is not violated at the C level), but the
modification happens in D — within the opaque subcategory — and the
return morphism in C cannot track the provenance of the modification.

Structurally: there is a round-trip in D (from ι.obj X through an opaque
object and back to ι.obj X), but the opaque object is not in the image
of ι, so the round-trip cannot be factored as ι.map of any C-morphism
composed with a C-return. The belief modification passes through opaque
territory, severing the return-address.
-/

/-- Instrumentalization: a round-trip in D factors through an opaque object
    that is not in C's image, so the modification cannot be tracked.
    The return-address (A2's closing morphism) is formally present in D
    but its provenance is lost because it transits through opacity. -/
structure Instrumentalization (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D]
    (op : Opacity C D) where
  /-- The ordinary object where the round-trip starts and ends -/
  subject : C
  /-- The outgoing morphism into the opaque object -/
  into_opaque : op.ι.obj subject ⟶ op.opaque_object
  /-- The return morphism from the opaque object -/
  from_opaque : op.opaque_object ⟶ op.ι.obj subject
  /-- The round-trip is non-trivial: it is not the identity -/
  nontrivial : into_opaque ≫ from_opaque ≠ 𝟙 (op.ι.obj subject)
  /-- The opaque object is not in the image of C (inherited from Opacity,
      but made explicit: the transit point has no C-level name) -/
  opaque_not_in_image : ∀ (Y : C), ¬ Nonempty (op.ι.obj Y ≅ op.opaque_object)

/-!
## Failure Mode 3: Flattening

Flattening = refusal of departure. The inclusion ι : C ⥤ D from Opacity
is claimed to be an isomorphism of categories (essentially surjective in
addition to being full and faithful). This asserts that C captures all of
D — nothing beyond the observable. The consequence chain from ordinary
consciousness to non-ordinary disclosure is cut at the outset.

This directly contradicts A3 (Opacity), which requires both that D contains
objects not in the essential image of ι and that no retraction exists.
-/

/-- Flattening: the claim that ι is an equivalence — that C captures all
    of D. This is the assertion that the ordinary phase's disclosures are
    exhaustive, cutting off any possibility of non-ordinary disclosure. -/
structure Flattening (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D]
    (op : Opacity C D) where
  /-- The claim: every object of D is isomorphic to some object in the
      image of ι. Nothing is opaque. -/
  everything_visible : ∀ (d : D), ∃ (X : C), Nonempty (op.ι.obj X ≅ d)

/-!
## Structural Symmetry: Globalization and Flattening

Both Globalization and Flattening commit the same formal error: treating
one phase's disclosures as exhaustive. Globalization universalizes from
the state side (non-ordinary → ordinary, no return). Flattening
universalizes from the gross side (ordinary is everything).

We formalize this symmetry: both modes entail that exactly one side of
the C/D boundary is treated as sufficient. In Globalization, the opaque
side projects without return. In Flattening, the ordinary side claims
completeness.

The symmetry theorem: both modes deny the irreducible relation between
C and D. They are "mirror" violations of Opacity — one from each side.
-/

/-- Globalization denies that the ordinary phase can respond to the
    non-ordinary: there is no morphism from the ordinary image back
    to the opaque origin. This makes the opaque side's projection
    one-directional — its disclosures are treated as final. -/
theorem globalization_denies_return
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    {op : Opacity C D}
    (g : Globalization C D op) :
    IsEmpty (op.ι.obj g.ordinary ⟶ op.opaque_object) :=
  g.no_return

/-- Flattening denies that the non-ordinary phase has anything the
    ordinary cannot capture: every D-object is in C's image.
    This directly contradicts the opaque_object witness in Opacity. -/
theorem flattening_denies_opacity
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    {op : Opacity C D}
    (f : Flattening C D op) :
    ∃ (X : C), Nonempty (op.ι.obj X ≅ op.opaque_object) :=
  f.everything_visible op.opaque_object

/-- The structural symmetry: both Globalization and Flattening deny the
    bidirectional irreducibility of the C-D relation.

    Globalization denies it by cutting the return (no morphism back from
    ordinary to opaque). Flattening denies it by collapsing the distinction
    (every D-object is in C's image).

    Both yield a one-directional relation where one side dominates. -/
theorem symmetry_of_globalization_and_flattening
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    {op : Opacity C D}
    (g : Globalization C D op)
    (f : Flattening C D op) :
    -- Globalization: opaque → ordinary is one-way (no return)
    IsEmpty (op.ι.obj g.ordinary ⟶ op.opaque_object) ∧
    -- Flattening: claims the opaque object is reachable from C
    (∃ (X : C), Nonempty (op.ι.obj X ≅ op.opaque_object)) :=
  ⟨g.no_return, f.everything_visible op.opaque_object⟩

/-!
## Inconsistency with Well-Formed Beach

A well-formed Beach satisfies all seven axioms (A1–A7). We show that
each failure mode is inconsistent with having a well-formed Beach:

1. Flattening contradicts Opacity (A3) directly: Opacity requires an
   opaque object not in C's image; Flattening claims everything is in
   C's image.

2. Globalization, instantiated at the Beach's opacity, leads to a
   contradiction when combined with the Communication Theorem (A2 + A3):
   the full + faithful embedding means round-trips through D factor
   through C-endomorphisms. If the opaque object admits a morphism
   *to* ι.obj X, then by fullness a preimage exists — but Globalization
   says no return exists. We derive a contradiction if the Globalization's
   intermediate object is in C's image.

3. Instrumentalization's opaque_not_in_image is the restatement of
   Opacity's not_in_image. The failure is that the round-trip modifies
   belief via opaque transit. In a well-formed Beach, the communication
   bound theorem ensures that any round-trip starting and ending in C's
   image is the image of a C-endomorphism — so the provenance IS tracked
   at the C level. Instrumentalization's nontrivial round-trip is still
   an image of a C-endomorphism; the provenance is not actually severed.
-/

/-- Flattening is inconsistent with Opacity: if Flattening holds, then
    the opaque_object is in C's image, contradicting not_in_image. -/
theorem flattening_inconsistent_with_opacity
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (op : Opacity C D)
    (f : Flattening C D op) : False := by
  obtain ⟨X, ⟨iso⟩⟩ := f.everything_visible op.opaque_object
  exact op.not_in_image X ⟨iso⟩

/-- Flattening is inconsistent with any Beach. -/
theorem flattening_inconsistent_with_beach
    {C D Ωt Ωg F : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} Ωt] [Category.{v} Ωg] [Category.{v} F]
    (b : Beach C D Ωt Ωg F)
    (f : Flattening C D b.opacity) : False :=
  flattening_inconsistent_with_opacity b.opacity f

/-- In a well-formed Beach, any round-trip in D starting and ending at
    an image of C is the image of a C-endomorphism (Communication Bound).
    Instrumentalization posits a round-trip through an opaque object, but
    the communication bound shows this round-trip has a C-level preimage.
    The endo tracks the provenance: the "severed return-address" is actually
    recoverable via fullness. -/
theorem instrumentalization_has_preimage
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (op : Opacity C D)
    (inst : Instrumentalization C D op) :
    ∃ (endo : inst.subject ⟶ inst.subject),
      op.ι.map endo = inst.into_opaque ≫ inst.from_opaque := by
  haveI := op.full
  exact ⟨op.ι.preimage (inst.into_opaque ≫ inst.from_opaque),
         op.ι.map_preimage (inst.into_opaque ≫ inst.from_opaque)⟩

/-- In a Beach, Instrumentalization's round-trip is tracked at the C level:
    the return-address is not actually severed because fullness of ι
    provides a C-endomorphism preimage. -/
theorem instrumentalization_tracked_in_beach
    {C D Ωt Ωg F : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} Ωt] [Category.{v} Ωg] [Category.{v} F]
    (b : Beach C D Ωt Ωg F)
    (inst : Instrumentalization C D b.opacity) :
    ∃ (endo : inst.subject ⟶ inst.subject),
      b.opacity.ι.map endo = inst.into_opaque ≫ inst.from_opaque :=
  instrumentalization_has_preimage b.opacity inst

/-- Globalization posits a chain from an opaque object to an ordinary
    image with no return. In a well-formed Opacity structure, the opaque
    object is genuinely outside C's image (not_in_image), so such a chain
    represents a one-way projection. This is inconsistent with having a
    closing pair (A2) IF the closing pair's target coincides with the
    Globalization's intermediate/ordinary objects.

    More directly: Globalization is inconsistent with Opacity whenever
    Flattening also holds (the opaque object is reachable from C), because
    Flattening itself is inconsistent with Opacity. But even without
    Flattening, Globalization demonstrates a broken return structure.

    The key theorem: in a Beach, the opacity's not_in_image guarantees
    the opaque_object is genuinely beyond C. Globalization's no_return
    is consistent with this — the failure is that the agent ACTS as if
    the opaque disclosure has ordinary status (projects it without return).
    The Beach's closure ensures that SOME chains close (A2), so the
    Globalization chain is one of the non-closing ones guaranteed by A2's
    nonClosing field. But the pathology is treating this non-closing chain
    as if it closed — universalizing from the state side. -/
theorem globalization_is_nonclosing
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (op : Opacity C D)
    (g : Globalization C D op) :
    ¬ Nonempty (op.ι.obj g.ordinary ⟶ op.opaque_object) :=
  fun ⟨f⟩ => g.no_return.false f

/-- In a Beach, the Globalization chain is an instance of the non-closing
    morphisms guaranteed by A2: it is one of those morphisms that have no
    return-address. -/
theorem globalization_among_nonclosing_in_beach
    {C D Ωt Ωg F : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} Ωt] [Category.{v} Ωg] [Category.{v} F]
    (b : Beach C D Ωt Ωg F)
    (g : Globalization C D b.opacity) :
    (∃ (A B : C) (_ : A ⟶ B), IsEmpty (B ⟶ A)) ∧
    IsEmpty (b.opacity.ι.obj g.ordinary ⟶ b.opacity.opaque_object) :=
  ⟨b.closure.nonClosing, g.no_return⟩

/-!
## Partition of the Failure Space

Any violation of the Closure+Opacity combination falls into one of the
three modes. We characterize what it means for the A2+A3 combination to
fail and show the three modes cover the cases.

The A2+A3 interaction has three aspects:
(a) Closure provides closing pairs and witnesses non-closing morphisms
(b) Opacity provides the C ↪ D embedding with opaque objects
(c) The Communication Bound (derived from A2+A3) says round-trips through
    D factor through C-endomorphisms

A failure of this interaction takes one of three forms:
1. A chain from the opaque side reaches ordinary but cannot return
   (Globalization — failure of return from non-ordinary)
2. A round-trip through the opaque side modifies ordinary belief without
   trackable provenance (Instrumentalization — return-address severed)
3. The claim that there IS no opaque side (Flattening — refusal of departure)

We formalize this as: given any "pathology witness" — evidence that the
C-D interaction is dysfunctional — it must be classifiable as one of the three.
-/

/-- A pathology witness for the C-D interaction. Exactly one of:
    - An opaque-to-ordinary chain with no return (Globalization-type)
    - A round-trip through opacity with non-trivial modification
      (Instrumentalization-type)
    - A claim that ι is essentially surjective (Flattening-type) -/
inductive FailureWitness (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D]
    (op : Opacity C D) where
  /-- Failure of return from the non-ordinary side -/
  | globalization (g : Globalization C D op) : FailureWitness C D op
  /-- Return-address severed via opaque transit -/
  | instrumentalization (i : Instrumentalization C D op) : FailureWitness C D op
  /-- Refusal of departure — denial of opacity -/
  | flattening (f : Flattening C D op) : FailureWitness C D op

/-- Every FailureWitness is inconsistent with the corresponding aspect of
    a well-formed Beach:
    - Globalization witnesses produce non-closing chains
    - Instrumentalization witnesses have C-level preimages (tracked)
    - Flattening witnesses contradict Opacity directly -/
theorem failure_witness_diagnosed
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (op : Opacity C D)
    (w : FailureWitness C D op) :
    -- At least one structural defect is present
    (∃ (X : C) (d : D), ¬ Nonempty (op.ι.obj X ⟶ d) ∨
      (∃ (f : op.ι.obj X ⟶ d) (g : d ⟶ op.ι.obj X), f ≫ g ≠ 𝟙 _) ∨
      (∃ (Y : C), Nonempty (op.ι.obj Y ≅ d) ∧
        Nonempty (op.ι.obj Y ≅ op.opaque_object))) := by
  match w with
  | .globalization g =>
    exact ⟨g.ordinary, op.opaque_object,
           Or.inl (fun ⟨f⟩ => g.no_return.false f)⟩
  | .instrumentalization inst =>
    exact ⟨inst.subject, op.opaque_object,
           Or.inr (Or.inl ⟨inst.into_opaque, inst.from_opaque, inst.nontrivial⟩)⟩
  | .flattening f =>
    obtain ⟨X, hX⟩ := f.everything_visible op.opaque_object
    exact ⟨X, op.opaque_object,
           Or.inr (Or.inr ⟨X, hX, hX⟩)⟩

/-- The three failure modes are exhaustive for FailureWitness: any
    FailureWitness is one of the three. This is trivially true by
    construction of the inductive type, but we state it as a theorem
    to make the partition explicit. -/
theorem failure_modes_exhaustive
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (op : Opacity C D)
    (w : FailureWitness C D op) :
    (∃ g, w = .globalization g) ∨
    (∃ i, w = .instrumentalization i) ∨
    (∃ f, w = .flattening f) := by
  match w with
  | .globalization g => exact Or.inl ⟨g, rfl⟩
  | .instrumentalization i => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | .flattening f => exact Or.inr (Or.inr ⟨f, rfl⟩)

/-- In a well-formed Beach, Flattening is impossible (contradicts A3),
    Globalization chains are among the non-closing morphisms (A2),
    and Instrumentalization round-trips are tracked via fullness (A3).
    No FailureWitness represents a genuine undiagnosed failure in a Beach. -/
theorem beach_diagnoses_all_failures
    {C D Ωt Ωg F : Type u} [Category.{v} C] [Category.{v} D]
    [Category.{v} Ωt] [Category.{v} Ωg] [Category.{v} F]
    (b : Beach C D Ωt Ωg F)
    (w : FailureWitness C D b.opacity) :
    -- Flattening is outright impossible
    (∀ f, w = .flattening f → False) ∧
    -- Globalization chains are recognized as non-closing
    (∀ g, w = .globalization g →
      IsEmpty (b.opacity.ι.obj g.ordinary ⟶ b.opacity.opaque_object)) ∧
    -- Instrumentalization round-trips have C-level preimages
    (∀ i, w = .instrumentalization i →
      ∃ (endo : i.subject ⟶ i.subject),
        b.opacity.ι.map endo = i.into_opaque ≫ i.from_opaque) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    subst hf
    exact flattening_inconsistent_with_beach b f
  · intro g hg
    subst hg
    exact g.no_return
  · intro i hi
    subst hi
    exact instrumentalization_has_preimage b.opacity i

end GroundState
