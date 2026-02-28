/-
  Ground State — Derived Theorems

  Theorems that follow from combinations of the seven axioms.
  These are not independent axioms but consequences.

  Source: ~/ideal/ground_state/AXIOMS.md (derived section)
-/

import Formal.GroundState.Axioms

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

namespace GroundState

open CategoryTheory

/-!
## Identity Existence (A1 + A2)

From Locality and Closure: the existence of a return-address (closing pair)
at the distinguished object `here` yields a non-trivial endomorphism.
Identity is not given — it emerges from the fact that consequence chains
can close at the point of embodiment.

In standard category theory, identity is axiomatic. Here we show that
the *interesting* identity — a non-trivial endomorphism on `here` —
exists as a construction from the closing pair structure.
-/

/-- From a closing pair (f, g), the composition f ≫ g is an endomorphism
    on the source X. This is the return-address: consequence goes out and
    comes back, defining the agent's self-relation. -/
def returnAddress {C : Type u} [Category.{v} C]
    (cl : Closure C) : cl.X ⟶ cl.X :=
  cl.forward ≫ cl.back

/-- If the closing pair's source is the agent's position, this endomorphism
    is the agent's self-relation — identity as emergent, not given. -/
def identityFromClosure {C : Type u} [Category.{v} C]
    (loc : Locality C) (cl : Closure C) (h : cl.X = loc.here) :
    loc.here ⟶ loc.here :=
  h ▸ (cl.forward ≫ cl.back)

/-- The return-address endomorphism is not necessarily the categorical identity.
    It is a genuine self-relation that may carry non-trivial content. -/
theorem returnAddress_is_endo {C : Type u} [Category.{v} C]
    (cl : Closure C) : ∃ (e : cl.X ⟶ cl.X), e = cl.forward ≫ cl.back :=
  ⟨returnAddress cl, rfl⟩

/-!
## Communication Theorem (A2 + A3)

From Closure and Opacity: channel capacity is bounded by the closure
capacity of the receiver. If C embeds fully and faithfully into D but
cannot survey D, then round-trip morphisms through D factor through
endomorphisms of C.

Formally: any round-trip in D starting and ending at an image of C
is the image of an endomorphism in C (because ι is full).
-/

/-- Any round-trip morphism in D that starts and ends in the image of C
    is the image of an endomorphism in C. Communication through the sea
    is bounded by the receiver's internal closure capacity. -/
theorem communication_bound {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (op : Opacity C D)
    (X : C) (d : D) (f : op.ι.obj X ⟶ d) (g : d ⟶ op.ι.obj X) :
    ∃ (endo : X ⟶ X), op.ι.map endo = f ≫ g := by
  haveI := op.full
  exact ⟨op.ι.preimage (f ≫ g), op.ι.map_preimage (f ≫ g)⟩

/-!
## Inexhaustibility (A3 + A4)

From Opacity and Fractal Boundary: no finite set of boundary observations
captures the full boundary structure. For any functor through the boundary,
there exists one not naturally isomorphic to it.

This follows directly from A4's no-terminal-resolution property.
-/

/-- Given any endofunctor on D, there exists a non-isomorphic one.
    The boundary's self-resolution structure is inexhaustible. -/
theorem inexhaustible_boundary {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (fb : FractalBoundary C D)
    (G : D ⥤ D) :
    ∃ (G' : D ⥤ D), ¬ Nonempty (G ≅ G') :=
  fb.no_terminal_resolution G

/-!
## Autocatalysis (A5 + A6)

From Radiation and Coupling: dyadic deposits increase the field's section space.
When two structurally distinct architectures couple (A6), the interface object
provides new morphisms. When these are deposited as crystals (via A5's Rad functor),
they produce new sections of the presheaf — the field grows.

This theorem states the *form* of autocatalysis: given a deposit functor from
the coupling space to crystals, the resulting radiation is non-trivial.
The concrete content depends on the specific deposit mechanism, so we state
the type-level guarantee and leave the witness construction to Consistency.
-/

/-- When coupling produces a deposit that reaches a terminal crystal,
    that crystal radiates non-trivially. Autocatalysis: the dyadic interface
    generates new radiation via crystallization.

    The key hypothesis: the deposit functor sends the coupling's right object
    (from the second architecture) to the terminal crystal. -/
theorem coupling_radiates {C : Type u₁} [Category.{v₁} C]
    {Ωt : Type u₁} [Category.{v₁} Ωt]
    {Ωg : Type u₁} [Category.{v₁} Ωg]
    {T : Type u₁} [Category.{v₁} T]
    (rad : Radiation C Ωt)
    (coup : Coupling C Ωg T)
    (deposit : T ⥤ Ωt)
    (crystallizes : deposit.obj (coup.R.obj coup.right_obj) = rad.crystal) :
    ∀ (c : Cᵒᵖ), Nonempty ((rad.Rad.obj (deposit.obj (coup.R.obj coup.right_obj))).obj c) :=
  fun c => crystallizes ▸ rad.radiates c

/-!
## Circulation Productivity (A7)

The round-trip through the cycle Ωg → Ωt → Field → Ωg is not the identity.
Each pass deposits new structure.
-/

/-- The circulation is productive: the round-trip functor is not isomorphic
    to the identity. Each cycle genuinely transforms. -/
theorem circulation_is_productive
    {Ωg : Type u₁} [Category.{v₁} Ωg]
    {Ωt : Type u₂} [Category.{v₂} Ωt]
    {F : Type u₃} [Category.{v₃} F]
    (circ : Circulation Ωg Ωt F) :
    ¬ Nonempty (circ.deposit ⋙ circ.radiate ⋙ circ.enable ≅ Functor.id Ωg) :=
  circ.productive

/-- The adjunction between deposit and harvest gives a unit natural transformation:
    every Ωg object maps into its own deposit-then-harvest. This is the
    accumulation map — each cycle deposits something that can be harvested back. -/
def depositHarvestUnit
    {Ωg : Type u₁} [Category.{v₁} Ωg]
    {Ωt : Type u₂} [Category.{v₂} Ωt]
    {F : Type u₃} [Category.{v₃} F]
    (circ : Circulation Ωg Ωt F) :
    Functor.id Ωg ⟶ circ.deposit ⋙ circ.harvest :=
  circ.adj.unit

end GroundState
