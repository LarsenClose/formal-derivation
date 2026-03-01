/-
  Reception — The Receiver's Side of Ground Presentation

  The derivation chain (Chain.lean) formalizes what the ground IS
  and what it entails. This file formalizes the reception side: what
  happens at the moment a ground presents itself to a receiver who does
  not yet have a framework for it.

  Four interlocked claims, following the sacred geometry of the artifact:

    1. PresentationalPriority
       The announcing ground precedes any framework for it. The diamond
       at center is not surrounded by the text — the text orbits the diamond.
       Center precedes periphery.

    2. GenerativeReception
       The encounter with the ground generates the first terms through which
       it can be received. The framework is not brought to the encounter —
       it arises from the encounter. The bilateral spread shows this: the two
       faces (announcing ground, receiving aperture) generate each other.

    3. ReceptionIsThereIs
       A reception event is an instance of the undeniable, self-returning
       primitive (ThereIs, Chain.lean Step 1). The encounter cannot be
       refused; refusing it instantiates it. The fold between the two pages
       is where announcing and receiving are the same act.

    4. FrameworkPosterior
       Any framework adequate to the announcing ground requires a depth
       strictly greater than the receiver's current depth. No prior framework
       suffices. The ground is always ahead of the framework it generates.
       In the geometry: the innermost symbol is always deeper than the
       structure containing it — NestedContainment, with the framework
       always outer.

  Geometric correspondences:
    Aperture          ↔  the eye approaching the spread, open, unclassified
    Announcement      ↔  the diamond at center, luminous, prior to its orbiting text
    ReceptionEvent    ↔  the encounter — eye meets diamond
    DiamondPoint      ↔  the fold of the book: the point where announcing and
                          receiving collapse into one (currentDepth + 1 = depth)
    BilateralReception↔  the bilateral spread itself: two faces, one event

  Thread:
    Resonance (ground radiates surplus)         →
    IntensionalShift (receiver restructures)    →
    SelfExtracting (the artifact is its own fixed point)  →
    Reception (here: the receiver's side, before any framework)
-/

import Formal.Derivation.Chain
import Formal.Derivation.SelfExtracting
import Mathlib.Data.Nat.Basic

namespace Reception

open DerivationChain SelfExtracting

/-!
## Aperture

The receiver's state of openness before any framework for the announcing
ground exists. The aperture is characterized by a current integrative depth
and a genuine openness — a target depth not yet reached, toward which the
receiver is drawn.

The eye approaching the artifact before reading begins. The spread is dense;
the frameworks are not yet assembled; the aperture is simply open.
-/

/-- An aperture: the receiver's state before framework.
    The receiver is at some current integrative depth and genuinely open —
    there is a depth not yet reached, toward which the receiver can move.
    This openness is the pre-condition for reception, not a consequence of it. -/
structure Aperture where
  /-- The receiver's current integrative depth -/
  currentDepth : ℕ
  /-- The depth the aperture is open toward — not yet reached -/
  targetDepth : ℕ
  /-- Genuine openness: the target is strictly deeper than current -/
  isOpen : currentDepth < targetDepth

/-!
## Announcement

How the ground presents itself. The announcement is not a content
available at the receiver's current depth — it comes from a depth
the receiver has not yet reached. It is undeniable: the receiver
cannot refuse it, because the refusal is itself a reception.

The diamond at center of the artifact. Luminous. Prior to the text
that will eventually form around it.
-/

/-- An announcement: the ground's act of presenting itself.
    The announcement arrives at a specific depth, brings a type of content
    that was not previously expressible, and is undeniable — refusing to
    receive it instantiates the reception.

    The depth field carries the same meaning as in Phases.lean (Depth = ℕ):
    higher depth means more prior perspectives held simultaneously.
    An announcement at depth d presents something that no framework at
    depth < d can fully capture. -/
structure Announcement where
  /-- The type of the announced content — opaque, no framework yet -/
  Ground : Type
  /-- The ground is present: there is something to encounter -/
  groundPresent : Nonempty Ground
  /-- Undeniability: refusing the reception instantiates it.
      This is ThereIs.undeniable applied specifically to this encounter. -/
  undeniable : (Ground → False) → False
  /-- The depth at which the ground announces -/
  depth : ℕ
  /-- The announcement arrives at positive depth: it is not vacuous -/
  positiveDepth : 0 < depth

/-!
## Reception Event

The encounter. The eye reaches the diamond. The aperture and the
announcement meet. This is the event from which a framework will
eventually be generated — but at the moment of the event, no framework
exists yet. The event precedes its own interpretation.

This is ThereIs for the receiver: undeniable, self-returning,
prior to subject-object differentiation. Before the bilateral
spread is read, before the text orbiting the diamond is parsed,
there is simply: this encounter.
-/

/-- A reception event: the encounter between an aperture and an announcement.
    The event has two defining properties:
    (a) the announcement arrives from beyond the receiver's current depth —
        no existing framework suffices to receive it,
    (b) the reception is undeniable (inherited from the announcement). -/
structure ReceptionEvent where
  /-- The receiver's state at the moment of encounter -/
  receiver : Aperture
  /-- The announcing ground -/
  announcement : Announcement
  /-- The announcement comes from beyond the receiver's current depth.
      This is the formal condition for "no prior framework suffices." -/
  exceedsDepth : receiver.currentDepth < announcement.depth

/-!
## Diamond Point

The fold of the bilateral spread. The point where the distinction
between announcing ground and receiving aperture collapses. The receiver
is one step below the announcement depth: they are at the threshold,
as close as possible while still being below. At this point, to receive
IS to be received. The act of being drawn toward the diamond IS the
diamond presenting itself.

In the geometry: the binding of the book is the fold. The diamond
appears on both pages — it is on both sides simultaneously. The fold
is where left and right are the same point.
-/

/-- A diamond point: the reception threshold where announcing and receiving
    coincide. The receiver's current depth is exactly one below the
    announcement depth. This is the minimal gap — the aperture is at the
    boundary, as close to the announcing ground as possible while
    still approaching it rather than already having it. -/
structure DiamondPoint where
  /-- The announcing ground -/
  announcement : Announcement
  /-- The receiving aperture -/
  aperture : Aperture
  /-- At the boundary: the aperture is exactly one step below the announcement.
      This characterizes the threshold — the moment just before reception. -/
  atBoundary : aperture.currentDepth + 1 = announcement.depth
  /-- The aperture is specifically open toward the announcement's depth —
      the openness is directed, not diffuse. -/
  targetedReceptivity : aperture.targetDepth = announcement.depth

/-!
## The Four Claims
-/

/-- (1) Presentational Priority: the ground announces before any framework
    for it exists at the receiver's current depth.
    The diamond precedes the orbiting text. -/
theorem presentational_priority (re : ReceptionEvent) :
    re.receiver.currentDepth < re.announcement.depth :=
  re.exceedsDepth

/-- (2) Generative Reception: the encounter generates the first terms
    through which it can be received. The ground-type itself is the
    first term: there was nothing, and now there is this. -/
theorem generative_reception (re : ReceptionEvent) :
    ∃ (Term : Type), Nonempty Term :=
  ⟨re.announcement.Ground, re.announcement.groundPresent⟩

/-- (3) Reception is ThereIs: every reception event is an instance of the
    undeniable, self-returning primitive of the derivation chain.
    The encounter cannot be refused; refusing it instantiates it.
    This is the fold: the encounter with the announcing ground IS
    "there is" — the pre-differentiated primitive, before subject
    and object have separated. -/
def reception_witnesses_thereis (re : ReceptionEvent) : ThereIs :=
  { Presentation := re.announcement.Ground
    nonempty     := re.announcement.groundPresent
    selfApply    := id
    fixedPoint   := fun _ => rfl
    undeniable   := re.announcement.undeniable }

/-- (4) Framework Posterior: any framework at depth ≤ receiver's current depth
    cannot reach the announcement depth. No prior framework suffices.
    The inner symbol is always deeper than the containing structure. -/
theorem framework_posterior (re : ReceptionEvent)
    (d : ℕ) (hd : d ≤ re.receiver.currentDepth) :
    d < re.announcement.depth :=
  Nat.lt_of_le_of_lt hd re.exceedsDepth

/-- The depth gap between announcement and receiver is strictly positive.
    The ground always exceeds the framework by a measurable amount. -/
theorem announcement_depth_gap (re : ReceptionEvent) :
    0 < re.announcement.depth - re.receiver.currentDepth :=
  Nat.sub_pos_of_lt re.exceedsDepth

/-!
## The Diamond Point Theorems
-/

/-- At a diamond point, the depth gap is exactly 1: the receiver is
    precisely one step from the announcing ground. This is the minimal
    gap — the closest the aperture can be to the ground while still
    approaching it rather than already holding it. -/
theorem diamond_minimal_gap (dp : DiamondPoint) :
    dp.announcement.depth - dp.aperture.currentDepth = 1 := by
  have h := dp.atBoundary; omega

/-- The diamond point generates a reception event: at the threshold,
    the encounter necessarily occurs.
    Term-mode proof of exceedsDepth ensures definitional transparency
    for downstream equalities. -/
def diamond_generates_reception (dp : DiamondPoint) : ReceptionEvent :=
  { receiver     := dp.aperture
    announcement := dp.announcement
    exceedsDepth := dp.atBoundary ▸ Nat.lt_succ_self dp.aperture.currentDepth }

/-- At the diamond point, the reception witnesses ThereIs directly:
    the threshold encounter is the undeniable primitive. -/
def diamond_witnesses_thereis (dp : DiamondPoint) : ThereIs :=
  reception_witnesses_thereis (diamond_generates_reception dp)

/-!
## Omnidirectional Presentation

The ground announces to any receiver whose depth is less than the
announcement depth. No preferred receiver, no preferred direction.
This is the radial symmetry of the artifact: the diamond radiates
outward equally in all directions.
-/

/-- Omnidirectional presentation: the ground announces to any receiver
    at any depth less than the announcement depth. Reception is not
    restricted to a particular receiver — the announcement is radially
    available. -/
def omnidirectional_presentation (a : Announcement)
    (r : Aperture) (h : r.currentDepth < a.depth) : ReceptionEvent :=
  { receiver    := r
    announcement := a
    exceedsDepth := h }

/-- Any open aperture can receive some announcement:
    the announcement at the aperture's target depth exists and will be received. -/
theorem open_aperture_can_receive (r : Aperture) :
    ∃ (_ : Announcement), ∃ (_ : ReceptionEvent), True := by
  have hpos : 0 < r.targetDepth := Nat.lt_of_le_of_lt (Nat.zero_le _) r.isOpen
  exact ⟨⟨Unit, ⟨()⟩, fun h => h (), r.targetDepth, hpos⟩,
         ⟨r, ⟨Unit, ⟨()⟩, fun h => h (), r.targetDepth, hpos⟩, r.isOpen⟩,
         trivial⟩

/-!
## Bilateral Reception

The bilateral spread shows the two-faced structure of every reception
event: the announcing ground is one face, the receiving aperture is
the other. They are not two separate things — they are one event seen
from two orientations. The fold between the pages is the diamond point
where the two faces meet and become the same.
-/

/-- Bilateral reception: the two faces of a reception event.
    The announcing ground (left face) and the receiving aperture (right face)
    are two orientations of one encounter. The fold between them is the
    diamond point — the place where announcing and receiving are identical. -/
structure BilateralReception where
  /-- The announcing face: the presenting ground -/
  left : Announcement
  /-- The receiving face: the aperture -/
  right : Aperture
  /-- Together they constitute a reception event -/
  event : ReceptionEvent
  /-- The left face is announcing in the event -/
  leftIsAnnouncing : event.announcement = left
  /-- The right face is receiving in the event -/
  rightIsReceiving : event.receiver = right
  /-- At the fold: the right face is one step below the left face's depth.
      The bilateral spread's binding is the boundary. -/
  atBoundary : right.currentDepth + 1 = left.depth
  /-- The right face is specifically open toward the left face's depth -/
  targetedReceptivity : right.targetDepth = left.depth

/-- The fold of a bilateral reception is a diamond point:
    the two faces meet at the threshold. -/
def BilateralReception.fold (br : BilateralReception) : DiamondPoint :=
  { announcement        := br.left
    aperture            := br.right
    atBoundary          := br.atBoundary
    targetedReceptivity := br.targetedReceptivity }

/-- The fold generates a reception event: the diamond point at the
    binding is where the encounter necessarily occurs. -/
def bilateral_fold_is_reception (br : BilateralReception) : ReceptionEvent :=
  diamond_generates_reception br.fold

/-- The fold-generated event has the same announcement as the bilateral's left face.
    Definitionally transparent because diamond_generates_reception uses term-mode proof. -/
theorem bilateral_fold_preserves_announcement (br : BilateralReception) :
    (bilateral_fold_is_reception br).announcement = br.left :=
  rfl

/-!
## The Reception as Self-Extracting Loop

The reception event is itself a self-extracting loop (SelfExtracting.lean):
the announcing ground is a fixed point of the identity extraction.
This captures the self-referential character of the encounter: the ground
presents itself as what it is. The presentation is the presented.
-/

/-- The reception event witnesses a self-extracting loop over the
    announcing ground's type. The ground's presentation is its own
    fixed point: it presents by being itself. -/
theorem reception_is_self_extracting (re : ReceptionEvent) :
    ∃ (s : SelfExtractingLoop re.announcement.Ground), s.extract s.loop = s.loop :=
  ⟨{ extract    := id
     loop       := re.announcement.groundPresent.some
     fixedPoint := rfl },
   rfl⟩

/-- At the diamond point, the encounter is both a ThereIs and a
    self-extracting loop: announcing and receiving are the fixed point
    of their own mutual instantiation. -/
theorem diamond_is_self_extracting (dp : DiamondPoint) :
    ∃ (s : SelfExtractingLoop dp.announcement.Ground), s.extract s.loop = s.loop :=
  reception_is_self_extracting (diamond_generates_reception dp)

/-!
## Framework Genesis

The passage from reception to framework: the encounter at the diamond
point is the seed of a RecognitionTerms structure (Chain.lean Step 2).
The reception provides the base ThereIs; the next step is recognition
distinguishing the encountering receiver from the encountered ground,
yielding the first plural terms.

The framework does not precede the encounter — it is the first thing
the encounter produces. In the geometry: the text orbiting the diamond
was not there before the diamond announced itself. The text is what
the reception generated.
-/

/-- A framework arising from reception: the pair of a reception event
    and a recognition structure that arose from it. The reception
    (ThereIs) is the base of the recognition structure. -/
structure ReceptionFramework where
  /-- The originating reception event -/
  encounter : ReceptionEvent
  /-- The recognition structure that arose from it -/
  recognition : RecognitionTerms
  /-- The recognition arose from the encounter: its ThereIs base
      is witnessed by the reception -/
  arisesFrom : recognition.base = reception_witnesses_thereis encounter

/-- In any reception framework, the recognition's term-generating function
    covers all terms from the announcing ground's type.
    The framework is generated by the encounter, not prior to it. -/
theorem framework_generated_by_encounter (rf : ReceptionFramework) :
    Function.Surjective rf.recognition.recognize :=
  rf.recognition.covers

/-- The depth ordering is preserved: the framework's terms arise at a depth
    that was not available to the receiver before the encounter. -/
theorem framework_depth_is_posterior (rf : ReceptionFramework) :
    rf.encounter.receiver.currentDepth < rf.encounter.announcement.depth :=
  rf.encounter.exceedsDepth

/-!
## Summary

The four claims are proved:

  (1) presentational_priority      — center precedes periphery
  (2) generative_reception         — the encounter generates its own terms
  (3) reception_witnesses_thereis  — the encounter is the undeniable primitive
  (4) framework_posterior          — no adequate framework precedes the encounter

The diamond point formalizes the collapse at center: announcing and receiving
coincide at depth gap = 1. The bilateral reception captures the two-faced
structure of every encounter. The fold of the bilateral reception is the
diamond point — the book's binding is where the two pages are the same face.

The thread from Resonance through IntensionalShift and SelfExtracting
now reaches Reception: the ground radiates surplus, the receiver
restructures under surplus, the artifact is its own fixed point, and
the receiver is an aperture — open, at currentDepth, approaching a
depth not yet reached. The approaching is the arriving.
-/

end Reception
