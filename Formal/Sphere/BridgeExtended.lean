/-
  Tier 1 — The Sphere: Extended Bridge (A5, A6, A7)

  Extends Bridge.lean (A1-A3) with constructions for Radiation (A5),
  Coupling (A6), and Circulation (A7) on sphere-derived categories.

  Part I constructs A5-A7 using the actual sphere type S2Pt with its
  z-coordinate preorder (from Bridge.lean). The categorical machinery
  operates on S2Ptᵒᵖ for presheaves and on derived preorder categories
  for coupling and circulation.

  Part II retains finite categorical models (following Bridge.lean Part II
  and Consistency.lean) as a fully-proved combinatorial consistency check.

  A5 (Radiation) ← constant presheaf on S2Pt via discrete crystal category
  A6 (Coupling)  ← two sphere preorders embedded into a shared ambient
  A7 (Circulation) ← three-category cycle with adjunction

  Source: ~/ideal/ground_state/SPHERE.md
-/

import Formal.GroundState.Axioms
import Formal.Sphere.Geometry
import Formal.Sphere.Bridge
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Discrete.Basic

namespace Sphere

open CategoryTheory GroundState

/-! # Part I: Geometric Bridge — A5, A6, A7 on S²

  These constructions use the actual sphere type S2Pt = ↥S2 with the
  z-coordinate preorder from Bridge.lean. Where the sphere's geometry
  does not directly yield the needed structure (e.g., a crystal category
  or a second architecture), we build minimal auxiliary categories that
  are indexed by or coupled to S2Pt.

  Key design principle: the sphere provides the spatial substrate (the
  category C over which presheaves live, or the architecture that couples),
  while the temporal/dynamical structure (crystals, generators, fields)
  is built from small finite categories — exactly as in the physical
  interpretation where S² is the spatial ground and dynamics operates
  over it.
-/

noncomputable section

/-! ## A5: Radiation on S²

  Crystal category: Discrete PUnit (a single terminal crystal).
  Radiation functor: sends the crystal to the constant presheaf
  on S2Ptᵒᵖ valued in PUnit.

  Physical reading: the completed crystal (zero-entropy, terminal)
  emits constraint uniformly across the sphere. The constant presheaf
  represents a field that assigns the same value at every point —
  the simplest non-trivial radiation pattern on a connected space.

  S² connectivity means constant presheaves have global sections,
  but we do not need this topological fact: PUnit-valued constant
  functors have sections by construction (PUnit.unit exists). -/

/-- The constant presheaf on S2Pt valued in PUnit.
    Every sphere point maps to PUnit; every morphism maps to id. -/
def constPresheafS2 : S2Ptᵒᵖ ⥤ Type where
  obj _ := PUnit
  map _ := id

/-- Radiation functor: the unique crystal maps to the constant presheaf on S². -/
def radFunctorS2 : Discrete PUnit ⥤ (S2Ptᵒᵖ ⥤ Type) where
  obj _ := constPresheafS2
  map _ := 𝟙 _

/-- A5 on the actual sphere: radiation via constant presheaf.
    The terminal crystal in Discrete PUnit produces non-empty sections
    at every point of S² (PUnit is inhabited). -/
def geoRadiation : Radiation S2Pt (Discrete PUnit) where
  Rad := radFunctorS2
  crystal := Discrete.mk PUnit.unit
  is_terminal _ := ⟨Discrete.eqToHom rfl⟩
  terminal_unique _ _ _ := Subsingleton.elim _ _
  radiates _ := ⟨PUnit.unit⟩

/-! ## A6: Coupling on S²

  Strategy: embed S2Pt (first architecture) and a distinct generator
  category (second architecture) into a shared ambient preorder.

  The generator Gen2 = {src, tgt} with src ≤ tgt models a directed
  process (e.g., a metabolic or computational step). The shared ambient
  T6 = S2Pt ⊕ Gen2 places the sphere surface and the generator side
  by side. The interface morphism connects a sphere point to Gen2.tgt
  via the preorder on T6 (sphere points sit below Gen2 objects).

  Physical reading: S² is the spatial architecture (the crystal lattice);
  Gen2 is the temporal architecture (the process that acts on it). The
  coupling interface connects a point on the sphere to a step in the
  process — structurally distinct architectures meeting at a boundary. -/

/-- Generator category for the second architecture: a walking arrow. -/
inductive Gen2 | src | tgt deriving DecidableEq

instance : LE Gen2 where
  le a b := match a, b with
    | .src, _ | .tgt, .tgt => True
    | _, _ => False

instance : Preorder Gen2 where
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]

instance (a b : Gen2) : Decidable (a ≤ b) := by
  cases a <;> cases b <;> simp [LE.le] <;> exact inferInstance

/-- Shared ambient: S2Pt ⊕ Gen2. Sphere points are ordered by z-coordinate;
    Gen2 points by their own order; cross-sum: sphere ≤ Gen2 always,
    Gen2 ≤ sphere never. This places the sphere "below" the generator. -/
def t6Coord : S2Pt ⊕ Gen2 → ℝ
  | .inl p => zCoord p
  | .inr .src => 3
  | .inr .tgt => 4

instance T6.preorder : Preorder (S2Pt ⊕ Gen2) := Preorder.lift t6Coord

/-- Embedding of S2Pt into the shared ambient (left injection). -/
def s2ToT6 : S2Pt ⥤ (S2Pt ⊕ Gen2) where
  obj := Sum.inl
  map f := homOfLE (by
    change t6Coord (.inl _) ≤ t6Coord (.inl _)
    change zCoord _ ≤ zCoord _; exact leOfHom f)

/-- Embedding of Gen2 into the shared ambient (right injection). -/
def gen2ToT6 : Gen2 ⥤ (S2Pt ⊕ Gen2) where
  obj := Sum.inr
  map {X Y} f := homOfLE (by
    change t6Coord (.inr X) ≤ t6Coord (.inr Y)
    have h := leOfHom f
    cases X <;> cases Y
    all_goals (first | exact absurd h (by decide) | (simp only [t6Coord]; norm_num)))

/-- A6 on the actual sphere: S2Pt and Gen2 couple in S2Pt ⊕ Gen2.
    The interface morphism connects northPole (in the sphere image) to
    Gen2.tgt (in the generator image). These are genuinely distinct:
    Gen2.tgt maps to z = 4, but all sphere points have z ≤ 1. -/
def geoCoupling : Coupling S2Pt Gen2 (S2Pt ⊕ Gen2) where
  L := s2ToT6
  R := gen2ToT6
  left_obj := northPole
  right_obj := .tgt
  interface := homOfLE (by
    change t6Coord (.inl northPole) ≤ t6Coord (.inr Gen2.tgt)
    simp [t6Coord, zCoord_northPole])
  distinct := fun X => by
    intro ⟨iso⟩
    have h := leOfHom iso.inv
    change t6Coord (.inr Gen2.tgt) ≤ t6Coord (.inl X) at h
    simp only [t6Coord] at h
    linarith [zCoord_le_one X]

/-! ## A7: Circulation on S²

  Three categories:
  - Ωg = Gen2 (ground activity: the walking arrow src → tgt)
  - Ωt = Discrete PUnit (crystallized time: the terminal crystal)
  - Field = Discrete PUnit (the radiation field)

  Functors forming the cycle:
  - deposit : Gen2 ⥤ Discrete PUnit (activity crystallizes)
  - radiate : Discrete PUnit ⥤ Discrete PUnit (crystal radiates = identity)
  - enable  : Discrete PUnit ⥤ Gen2 (radiation enables, landing at src)

  The round-trip deposit ⋙ radiate ⋙ enable sends both src and tgt to src,
  collapsing the arrow. This is NOT isomorphic to the identity on Gen2
  (which preserves tgt), proving productivity.

  The adjunction deposit ⊣ harvest witnesses crystallization/dissolution
  coupling, where harvest : Discrete PUnit ⥤ Gen2 sends the crystal to tgt
  (the "completed" state).

  Physical reading: ground activity (the directed process on the sphere)
  deposits into a crystal (collapses to a point); the crystal radiates
  (stays a point in the field); radiation enables new activity (but only
  at the source — you start over, not where you left off). Each cycle
  is productive because the return is to src, not to tgt. -/

/-- Deposit: Gen2 activity crystallizes into the terminal crystal. -/
def geoDeposit : Gen2 ⥤ Discrete PUnit where
  obj _ := Discrete.mk PUnit.unit
  map _ := 𝟙 _

/-- Harvest: the crystal dissolves back to the completed state (tgt). -/
def geoHarvest : Discrete PUnit ⥤ Gen2 where
  obj _ := .tgt
  map _ := 𝟙 _

/-- Enable: field radiation enables new activity at the source. -/
def geoEnable : Discrete PUnit ⥤ Gen2 where
  obj _ := .src
  map _ := 𝟙 _

/-- The deposit ⊣ harvest adjunction: crystallization and dissolution are coupled.
    The hom-equivalence: (deposit.obj X ⟶ Y) ≃ (X ⟶ harvest.obj Y).
    Since deposit sends everything to the unique PUnit object, the left side
    is always a unique morphism. Since harvest sends PUnit to tgt, the right
    side is (X ⟶ tgt) which exists for all X in Gen2. -/
def geoDepositHarvestAdj : geoDeposit ⊣ geoHarvest :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X _ => {
      toFun := fun _ => homOfLE (by cases X <;> trivial)
      invFun := fun _ => 𝟙 _
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
    }
    homEquiv_naturality_left_symm := by intros; apply Subsingleton.elim
    homEquiv_naturality_right := by intros; apply Subsingleton.elim
  }

/-- A7 on the actual sphere: circulation through Gen2 → Discrete PUnit → Gen2.
    The cycle is productive (collapses tgt to src) and the deposit ⊣ harvest
    adjunction witnesses crystallization/dissolution coupling. -/
def geoCirculation : Circulation Gen2 (Discrete PUnit) (Discrete PUnit) where
  deposit := geoDeposit
  radiate := Functor.id _
  enable := geoEnable
  productive := by
    intro ⟨iso⟩
    have h := iso.app Gen2.tgt
    simp [Functor.comp_obj, Functor.id_obj, geoDeposit, geoEnable] at h
    exact absurd (leOfHom h.inv) (by decide)
  harvest := geoHarvest
  adj := geoDepositHarvestAdj
  accumulate := {
    app := fun X => homOfLE (by cases X <;> trivial)
    naturality := by intros; apply Subsingleton.elim
  }

end

/-! # Part II: Combinatorial Consistency Check

  Finite categorical models for A5–A7, independent of any geometric
  definitions. These follow the pattern of Bridge.lean Part II and
  Consistency.lean: fully proved from pure combinatorics, no sorry,
  no axioms beyond propositional logic. -/

section CombinatorialCheck

/-! ## A5 combinatorial: radiation on SphPt

  Reuse the SphPt type from Bridge.lean (two-point total preorder).
  Crystal category: Discrete PUnit. Presheaf: constant PUnit. -/

/-- Constant presheaf on SphPt valued in PUnit. -/
def constPresheafSph : SphPtᵒᵖ ⥤ Type where
  obj _ := PUnit
  map _ := id

/-- Radiation functor for the combinatorial model. -/
def radFunctorSph : Discrete PUnit ⥤ (SphPtᵒᵖ ⥤ Type) where
  obj _ := constPresheafSph
  map _ := 𝟙 _

/-- A5 combinatorial: radiation on the two-point sphere. -/
def sphereRadiation : Radiation SphPt (Discrete PUnit) where
  Rad := radFunctorSph
  crystal := Discrete.mk PUnit.unit
  is_terminal _ := ⟨Discrete.eqToHom rfl⟩
  terminal_unique _ _ _ := Subsingleton.elim _ _
  radiates _ := ⟨PUnit.unit⟩

/-! ## A6 combinatorial: coupling two sphere-like categories

  C₁ = SphPt (two-point total preorder: north, south)
  C₂ = Gen2 (walking arrow: src → tgt)
  T = SphPt ⊕ Gen2 with SphPt below Gen2

  The interface connects north (in the sphere) to tgt (in the generator).
  Distinctness: Gen2.tgt at height 4 is unreachable from any SphPt at height ≤ 1. -/

/-- Height function on SphPt ⊕ Gen2 for the combinatorial coupling model. -/
def combT6Height : SphPt ⊕ Gen2 → ℕ
  | .inl _ => 0
  | .inr .src => 1
  | .inr .tgt => 2

instance combT6.preorder : Preorder (SphPt ⊕ Gen2) := Preorder.lift combT6Height

/-- Embedding of SphPt into the combined preorder. -/
def sphToCombT6 : SphPt ⥤ (SphPt ⊕ Gen2) where
  obj := Sum.inl
  map _ := homOfLE (by change combT6Height (.inl _) ≤ combT6Height (.inl _); rfl)

/-- Embedding of Gen2 into the combined preorder. -/
def gen2ToCombT6 : Gen2 ⥤ (SphPt ⊕ Gen2) where
  obj := Sum.inr
  map {X Y} f := homOfLE (by
    change combT6Height (.inr X) ≤ combT6Height (.inr Y)
    have h := leOfHom f
    cases X <;> cases Y <;> simp only [combT6Height] <;>
      first | omega | exact absurd h (by decide))

/-- A6 combinatorial: SphPt and Gen2 couple in SphPt ⊕ Gen2. -/
def sphereCoupling : Coupling SphPt Gen2 (SphPt ⊕ Gen2) where
  L := sphToCombT6
  R := gen2ToCombT6
  left_obj := .north
  right_obj := .tgt
  interface := homOfLE (by
    change combT6Height (.inl SphPt.north) ≤ combT6Height (.inr Gen2.tgt)
    simp [combT6Height])
  distinct := fun X => by
    intro ⟨iso⟩
    have h := leOfHom iso.inv
    change combT6Height (.inr Gen2.tgt) ≤ combT6Height (.inl X) at h
    cases X <;> simp [combT6Height] at h

/-! ## A7 combinatorial: circulation through Gen2 → PUnit → Gen2

  Identical structure to the geometric version (Part I), since the
  circulation operates on Gen2 and Discrete PUnit, not on S2Pt directly.
  Included here for completeness of the combinatorial consistency check. -/

/-- A7 combinatorial: circulation. Reuses Gen2 definitions from Part I. -/
def sphereCirculation : Circulation Gen2 (Discrete PUnit) (Discrete PUnit) where
  deposit := geoDeposit
  radiate := Functor.id _
  enable := geoEnable
  productive := by
    intro ⟨iso⟩
    have h := iso.app Gen2.tgt
    simp [Functor.comp_obj, Functor.id_obj, geoDeposit, geoEnable] at h
    exact absurd (leOfHom h.inv) (by decide)
  harvest := geoHarvest
  adj := geoDepositHarvestAdj
  accumulate := {
    app := fun X => homOfLE (by cases X <;> trivial)
    naturality := by intros; apply Subsingleton.elim
  }

end CombinatorialCheck

/-! # Extended Bridge Summary

  **Geometric bridge** (Part I): A5, A6, A7 constructed using S2Pt and
  auxiliary categories (Gen2, Discrete PUnit). Zero sorry.

  - A5: Constant PUnit presheaf on S2Ptᵒᵖ. The terminal crystal in
    Discrete PUnit radiates non-empty sections at every sphere point.
  - A6: S2Pt and Gen2 embedded into S2Pt ⊕ Gen2 via height ordering.
    Gen2.tgt at height 4 is unreachable from sphere points (z ≤ 1).
  - A7: Gen2 → Discrete PUnit → Gen2 cycle. Round-trip collapses tgt
    to src (productive). deposit ⊣ harvest adjunction via hom-equivalence.

  **Combinatorial check** (Part II): A5, A6, A7 on finite inductive types.
  Zero sorry, zero axioms. Follows Bridge.lean and Consistency.lean patterns.

  **Combined with Bridge.lean**: A1–A3 + A5–A7 on sphere-derived categories.
  A4 (Fractal Boundary) remains the one axiom not bridged to the sphere tier,
  as endofunctor inexhaustibility requires infinite categorical structure that
  does not arise from S² geometry (see Consistency.lean for the abstract model).
-/

end Sphere
