/-
  Ground State — Consistency (Concrete Model)

  Construct a concrete model satisfying all seven axioms simultaneously,
  proving the axiom system is consistent.
-/

import Formal.GroundState.Axioms
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Discrete.Basic

namespace GroundState

open CategoryTheory

/-! ## Model types

Shore (C): 3 objects {h, t, f} with preorder h ≡ t, both ≤ f
Sea (D):   4 objects = Shore + abyss, isolated
Gen (Ωg):  2 objects {src, tgt} with src ≤ tgt (walking arrow)
-/

inductive Shore | h | t | f deriving DecidableEq
inductive Sea   | h | t | f | abyss deriving DecidableEq
inductive Gen   | src | tgt deriving DecidableEq

/-! ## Preorder instances -/

instance : LE Shore where
  le a b := match a, b with
    | .h, .h | .h, .t | .h, .f | .t, .h | .t, .t | .t, .f | .f, .f => True
    | _, _ => False

instance : Preorder Shore where
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]

instance (a b : Shore) : Decidable (a ≤ b) := by
  cases a <;> cases b <;> simp [LE.le] <;> exact inferInstance

instance : LE Sea where
  le a b := match a, b with
    | .h, .h | .h, .t | .h, .f | .t, .h | .t, .t | .t, .f
    | .f, .f | .abyss, .abyss => True
    | _, _ => False

instance : Preorder Sea where
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]

instance (a b : Sea) : Decidable (a ≤ b) := by
  cases a <;> cases b <;> simp [LE.le] <;> exact inferInstance

instance : LE Gen where
  le a b := match a, b with
    | .src, _ | .tgt, .tgt => True
    | _, _ => False

instance : Preorder Gen where
  le_refl a := by cases a <;> trivial
  le_trans a b c := by cases a <;> cases b <;> cases c <;> simp_all [LE.le]

instance (a b : Gen) : Decidable (a ≤ b) := by
  cases a <;> cases b <;> simp [LE.le] <;> exact inferInstance

/-! ## The embedding ι : Shore → Sea -/

def embed : Shore → Sea
  | .h => .h | .t => .t | .f => .f

def shoreToSea : Shore ⥤ Sea where
  obj := embed
  map {X Y} f := homOfLE (by
    have h := leOfHom f
    cases X <;> cases Y <;> simp_all [embed, LE.le])

/-! ## A1: Locality -/
def modelLocality : Locality Shore where
  here := .h

/-! ## A2: Closure -/
def modelClosure : Closure Shore where
  X := .h
  Y := .t
  forward := homOfLE (by trivial : Shore.h ≤ Shore.t)
  back := homOfLE (by trivial : Shore.t ≤ Shore.h)
  nonClosing := ⟨.h, .f, homOfLE (by trivial : Shore.h ≤ Shore.f),
    ⟨fun g => absurd (leOfHom g) (by decide)⟩⟩

/-! ## A3: Opacity -/
def modelOpacity : Opacity Shore Sea where
  ι := shoreToSea
  faithful := ⟨fun _ => Subsingleton.elim _ _⟩
  full := ⟨fun {X Y} f => by
    refine ⟨homOfLE ?_, Subsingleton.elim _ _⟩
    have := leOfHom f; cases X <;> cases Y <;> first | trivial | exact this⟩
  opaque_object := .abyss
  not_in_image := fun X => by
    intro ⟨iso⟩
    have := leOfHom iso.hom; cases X <;> simp [embed, shoreToSea, LE.le] at this
  no_retraction := fun R => by
    intro ⟨iso⟩
    have h_inv := leOfHom (iso.app Sea.abyss).inv
    have : ∀ s : Shore, ¬ (Sea.abyss ≤ embed s) := by
      intro s; cases s <;> decide
    exact this _ h_inv

/-! ## A4: Fractal Boundary -/

def constAbyss : Sea ⥤ Sea where
  obj _ := .abyss
  map _ := 𝟙 _

def modelFractalBoundary : FractalBoundary Shore Sea where
  boundary := shoreToSea
  no_terminal_resolution := fun G => by
    by_cases h : Nonempty (G ≅ constAbyss)
    · refine ⟨Functor.id _, fun ⟨iso_id⟩ => ?_⟩
      have := (h.some.app Sea.h).symm ≪≫ iso_id.app Sea.h
      simp [constAbyss] at this
      exact absurd (leOfHom this.inv) (by decide)
    · exact ⟨constAbyss, h⟩

/-! ## A5: Radiation -/

def modelRadiation : Radiation Shore (Discrete PUnit) where
  Rad := (Functor.const _).obj ((Functor.const _).obj PUnit)
  crystal := Discrete.mk PUnit.unit
  is_terminal _ := ⟨Discrete.eqToHom rfl⟩
  terminal_unique _ _ _ := Subsingleton.elim _ _
  radiates _ := ⟨PUnit.unit⟩

/-! ## A6: Coupling

Use T = Gen. L : Shore ⥤ Gen sends everything to src.
R = 𝟭 Gen. Interface: src → tgt exists. Images distinct: src ≇ tgt.
-/

def shoreToGen : Shore ⥤ Gen where
  obj _ := .src
  map _ := 𝟙 _

def modelCoupling : Coupling Shore Gen Gen where
  L := shoreToGen
  R := Functor.id _
  left_obj := .h
  right_obj := .tgt
  interface := homOfLE (show Gen.src ≤ Gen.tgt from by trivial)
  distinct := fun X => by
    cases X <;> intro ⟨iso⟩ <;> exact absurd (leOfHom iso.inv) (by decide)

/-! ## A7: Circulation -/

def depositFun : Gen ⥤ Discrete PUnit where
  obj _ := Discrete.mk PUnit.unit
  map _ := 𝟙 _

def harvestFun : Discrete PUnit ⥤ Gen where
  obj _ := .tgt
  map _ := 𝟙 _

def enableFun : Discrete PUnit ⥤ Gen where
  obj _ := .src
  map _ := 𝟙 _

def depositHarvestAdj : depositFun ⊣ harvestFun :=
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

def modelCirculation : Circulation Gen (Discrete PUnit) (Discrete PUnit) where
  deposit := depositFun
  radiate := Functor.id _
  enable := enableFun
  productive := by
    intro ⟨iso⟩
    have h := iso.app Gen.tgt
    simp [Functor.comp_obj, Functor.id_obj, depositFun, enableFun] at h
    exact absurd (leOfHom h.inv) (by decide)
  harvest := harvestFun
  adj := depositHarvestAdj
  accumulate := {
    app := fun X => homOfLE (by cases X <;> trivial)
    naturality := by intros; apply Subsingleton.elim
  }

/-! ## Ground State Consistency -/

theorem ground_state_consistent :
    ∃ (C D Ωt Ωg F : Type) (_ : SmallCategory C) (_ : SmallCategory D)
      (_ : SmallCategory Ωt) (_ : SmallCategory Ωg) (_ : SmallCategory F),
      Nonempty (@Beach C _ D _ Ωt _ Ωg _ F _) :=
  ⟨Shore, Sea, Discrete PUnit, Gen, Discrete PUnit,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨⟨modelLocality, modelClosure, modelOpacity, modelFractalBoundary,
      modelRadiation, Gen, modelCoupling, modelCirculation⟩⟩⟩

theorem a1_satisfiable :
    ∃ (C : Type) (_ : SmallCategory C), Nonempty (@Locality C _) :=
  ⟨Discrete Unit, inferInstance, ⟨⟨Discrete.mk ()⟩⟩⟩

end GroundState
