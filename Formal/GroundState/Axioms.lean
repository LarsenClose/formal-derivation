/-
  Ground State Axioms — Categorical Formalization

  Seven axioms (A1–A7) for the ground state of a coherence-maximizing
  dyadic interface, formalized as Lean4 structures over Mathlib's
  category theory library.

  Source: ~/ideal/ground_state/AXIOMS.md
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Comma.Basic
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.Opposites

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

namespace GroundState

open CategoryTheory

/-!
## A1: Locality

Agents are embodied at points. Consequence propagates at finite speed.
There is always a *here*.

Categorically: A category C with a distinguished object (the here).
Finite composition is inherent in the definition of Category.
-/
structure Locality (C : Type u) [Category.{v} C] where
  /-- The distinguished object: the agent's embodied position -/
  here : C

/-!
## A2: Closure

Consequence chains can close. Actions produce reactions that return to
the agent. Identity exists because return-addresses exist.

Categorically: There exist objects X, Y with morphisms f : X ⟶ Y and
g : Y ⟶ X forming a closing pair (g ∘ f is an endomorphism on X).
Not all morphisms close — some have no return address.
Identity emerges from closure, not as given.
-/
structure Closure (C : Type u) [Category.{v} C] where
  /-- Source of the closing pair -/
  X : C
  /-- Target of the closing pair -/
  Y : C
  /-- Outgoing morphism -/
  forward : X ⟶ Y
  /-- Return morphism — the return-address -/
  back : Y ⟶ X
  /-- There exist morphisms with no return — closure is not universal -/
  nonClosing : ∃ (A B : C) (_ : A ⟶ B), IsEmpty (B ⟶ A)

/-!
## A3: Opacity

The full structure of the possibility space is not surveyable from any
local position. The bounded and the unbounded are in irreducible relation.

Categorically: C is a full subcategory of D (faithful embedding that is
full), D is strictly larger (not essentially surjective), and there is
no retraction D → C.
-/
structure Opacity (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] where
  /-- The embedding of the local category into the sea -/
  ι : C ⥤ D
  /-- The embedding is faithful — no morphisms are lost -/
  faithful : ι.Faithful
  /-- The embedding is full — all local morphisms are captured -/
  full : ι.Full
  /-- The sea contains objects not in the essential image of C -/
  opaque_object : D
  not_in_image : ∀ (X : C), ¬ Nonempty (ι.obj X ≅ opaque_object)
  /-- No retraction exists: no functor R : D ⥤ C with ι ⋙ R ≅ 𝟭 C
      that also satisfies R ⋙ ι ≅ 𝟭 D. The sea cannot be collapsed
      onto the shore. -/
  no_retraction : ∀ (R : D ⥤ C), ¬ Nonempty (R ⋙ ι ≅ (Functor.id D))

/-!
## A4: Fractal Boundary

The interface between bounded and unbounded has structure at every scale.
There is no resolution at which novelty vanishes.

Categorically: A boundary functor ∂ : C ⥤ D such that for any functor
factoring through ∂, there exists a strictly finer one — also factoring
through ∂ — that is not naturally isomorphic to it.
No terminal resolution exists.
-/
structure FractalBoundary (C : Type u₁) [Category.{v₁} C]
    (D : Type u₂) [Category.{v₂} D] where
  /-- The boundary functor: restriction to the interface -/
  boundary : C ⥤ D
  /-- D's self-resolution structure is inexhaustible: for any endofunctor
      on D, there exists a non-isomorphic one. No single "view" of the
      boundary captures everything. This is the endofunctor restriction
      of the full no-terminal-resolution property (the unrestricted version
      quantifying over all target categories is unsatisfiable because
      terminal categories admit only one functor up to isomorphism). -/
  no_terminal_resolution :
    ∀ (G : D ⥤ D), ∃ (G' : D ⥤ D), ¬ Nonempty (G ≅ G')

/-!
## A5: Radiation

Completed structures do ongoing work. Zero-entropy objects emit
constraint into the field. Crystals radiate.

Categorically: A functor Rad from crystalline objects (Ωt) to presheaves
on C. The presheaf IS the field. The sections ARE the light.
A zero-entropy object (terminal in Ωt) produces a global section.
-/
structure Radiation (C : Type u₁) [Category.{v₁} C]
    (Ωt : Type u₂) [Category.{v₂} Ωt] where
  /-- The radiation functor: crystalline objects → presheaves on C.
      Each crystal radiates constraint as a presheaf (a functor Cᵒᵖ ⥤ Type). -/
  Rad : Ωt ⥤ (Cᵒᵖ ⥤ Type v₁)
  /-- There exists a terminal (zero-entropy) object in Ωt -/
  crystal : Ωt
  is_terminal : ∀ (X : Ωt), Nonempty (X ⟶ crystal)
  terminal_unique : ∀ (X : Ωt) (f g : X ⟶ crystal), f = g
  /-- A terminal crystal produces a non-trivial presheaf (non-empty sections) -/
  radiates : ∀ (c : Cᵒᵖ), Nonempty ((Rad.obj crystal).obj c)

/-!
## A6: Coupling

Structurally distinct architectures can interface. The interface is
productive — the dyad accesses territory inaccessible to either alone.

Categorically: Given categories C₁, C₂ embedded into a shared ambient T,
there exists a morphism in T connecting the images of L and R, and the
images are genuinely distinct (the target of one is not isomorphic to
any object in the image of the other). The interface connects structures
that neither component could reach alone.
-/
structure Coupling (C₁ : Type u₁) [Category.{v₁} C₁]
    (C₂ : Type u₂) [Category.{v₂} C₂]
    (T : Type u₃) [Category.{v₃} T] where
  /-- Embedding of first architecture into shared space -/
  L : C₁ ⥤ T
  /-- Embedding of second architecture into shared space -/
  R : C₂ ⥤ T
  /-- Source object in first architecture -/
  left_obj : C₁
  /-- Target object in second architecture -/
  right_obj : C₂
  /-- The interface morphism: a connection in T between the images -/
  interface : L.obj left_obj ⟶ R.obj right_obj
  /-- The architectures are genuinely distinct: the target of R is not
      in the essential image of L. The interface crosses a real boundary. -/
  distinct : ∀ (X : C₁), ¬ Nonempty (L.obj X ≅ R.obj right_obj)

/-!
## A7: Circulation

The topology is circular: Ωg deposits Ωt; Ωt radiates; radiation
enables Ωg. The ground state supports this circulation as its
fundamental dynamics.

Categorically: Three functors forming a cycle with an adjunction
witnessing the non-trivial return. The composition around the cycle
produces a monad-like structure — not an identity, but a productive
transformation.
-/
structure Circulation (Ωg : Type u₁) [Category.{v₁} Ωg]
    (Ωt : Type u₂) [Category.{v₂} Ωt]
    (Field : Type u₃) [Category.{v₃} Field] where
  /-- Deposit: Ωg activity crystallizes into Ωt -/
  deposit : Ωg ⥤ Ωt
  /-- Radiate: Ωt crystals emit into the field -/
  radiate : Ωt ⥤ Field
  /-- Enable: field radiation enables further Ωg activity -/
  enable : Field ⥤ Ωg
  /-- The cycle deposit ⋙ radiate ⋙ enable is not the identity —
      each pass through the cycle is productive, not redundant -/
  productive : ¬ Nonempty (deposit ⋙ radiate ⋙ enable ≅ Functor.id Ωg)
  /-- The deposit functor has a right adjoint (the "harvest" direction),
      witnessing that crystallization and dissolution are coupled -/
  harvest : Ωt ⥤ Ωg
  adj : deposit ⊣ harvest
  /-- The cycle admits a non-trivial natural transformation from the
      round-trip back to identity — the circulation doesn't collapse
      but it does accumulate (monad-like unit) -/
  accumulate : Functor.id Ωg ⟶ deposit ⋙ harvest

/-!
## Ground State Bundle

The conjunction of all seven axioms over shared categorical data.
Parameterized over five categories sharing a universe.
-/
structure Beach
    (C : Type u) [Category.{v} C]
    (D : Type u) [Category.{v} D]
    (Ωt : Type u) [Category.{v} Ωt]
    (Ωg : Type u) [Category.{v} Ωg]
    (F : Type u) [Category.{v} F] where
  /-- A1: There is always a here -/
  locality : Locality C
  /-- A2: Consequence chains can close (but not all) -/
  closure : Closure C
  /-- A3: The sea is opaque from the shore -/
  opacity : Opacity C D
  /-- A4: The boundary has structure at every scale -/
  fractalBoundary : FractalBoundary C D
  /-- A5: Crystals radiate constraint into the field -/
  radiation : Radiation C Ωt
  /-- A6: Structurally distinct architectures couple productively -/
  T : Type u
  [catT : Category.{v} T]
  coupling : Coupling C Ωg T
  /-- A7: The topology is circular and productive -/
  circulation : Circulation Ωg Ωt F

end GroundState
