/-
  Tier 1 — The Sphere: A4 (Fractal Boundary) Bridge

  Constructs A4 (FractalBoundary) on sphere-derived categories, completing
  the bridge of all seven ground state axioms to the sphere tier.

  ## Mathematical interpretation

  The Riemann sphere Ĉ = ℂ ∪ {∞} ≅ S² is the natural home for complex
  dynamics. Rational self-maps f : Ĉ → Ĉ of degree d produce Julia sets
  J(f) — the boundary between stable and chaotic behavior under iteration.

  Key facts from complex dynamics (not in Mathlib):
  - For each degree d ≥ 2, there exist rational maps with topologically
    distinct Julia sets
  - The family of Julia sets across all degrees has structure at every
    scale: no finite collection of degrees captures all boundary phenomena
  - The Julia set is the boundary of the Fatou set — literally the
    "fractal boundary" between regions of regular and irregular dynamics

  ## Categorical construction

  The construction models this via:
  - C = S2Pt (sphere surface with z-coordinate preorder)
  - D = ℕ (natural numbers with standard preorder)

  The natural numbers ℕ serve as a "polynomial degree index" — the category
  of resolution levels for dynamics on the Riemann sphere. The boundary
  functor S2Pt ⥤ ℕ maps sphere points to ℕ, modeling the assignment of
  each sphere point to its base resolution level.

  The endofunctor inexhaustibility of ℕ captures the key property: for any
  endofunctor G : ℕ ⥤ ℕ (any monotone re-indexing of resolution levels),
  the composite G ⋙ succ produces a strictly finer resolution that is
  never isomorphic to G. This is because in ℕ (a linear order), a natural
  isomorphism between functors requires pointwise equality, and
  G.obj 0 ≠ G.obj 0 + 1.

  Physically: no matter how you re-index the polynomial degrees, adding one
  more degree of complexity always produces genuinely new structure. The
  boundary between order and chaos on S² has no terminal resolution.

  ## What resists

  1. **Julia set theory is absent from Mathlib.** There is no formalization
     of Julia sets, Fatou sets, rational dynamics on P¹, or the Mandelbrot
     set. The connection between ℕ-indexed resolution levels and actual
     Julia set complexity is therefore interpretive, not formal.

  2. **The boundary functor is degenerate.** The map S2Pt ⥤ ℕ is constant
     (every point maps to 0) because no nontrivial monotone map from the
     z-coordinate preorder to ℕ captures Julia set structure. The fractal
     boundary property lives entirely in D = ℕ, not in the functor itself.
     This is honest: the A4 axiom's content is about the inexhaustibility
     of the boundary category's endofunctors, not about the boundary map.

  3. **The ℕ model is algebraic, not geometric.** Using ℕ as the boundary
     category captures the right cardinality and order-theoretic property
     (linear, well-ordered, infinite) but loses the topological/metric
     structure of actual Julia sets. A richer model would use a category
     of compact metric spaces with Hausdorff distance, but this machinery
     is far beyond current Mathlib.

  4. **Connection to A3 (Opacity) is structural, not canonical.** The
     A4 boundary functor does not compose with the A3 opacity embedding
     in any meaningful way. In the abstract model (Consistency.lean),
     the same C and D serve both A3 and A4; here, A3 uses D = S2Pt ⊕ PUnit
     while A4 uses D = ℕ. Unifying them would require a single D that
     is both "S2Pt plus opaque points" and "has inexhaustible endofunctors,"
     which is achievable (e.g., ℕ ⊕ PUnit) but at the cost of naturality.

  Source: ~/ideal/ground_state/SPHERE.md
-/

import Formal.GroundState.Axioms
import Formal.Sphere.Geometry
import Formal.Sphere.Bridge
import Mathlib.CategoryTheory.Category.Preorder

namespace Sphere

open CategoryTheory GroundState

/-! # Part I: Geometric Bridge — A4 on S²

  The boundary category is ℕ, modeling polynomial degree / resolution
  level on the Riemann sphere. The successor functor n ↦ n + 1 on ℕ
  represents "increase the polynomial degree by one" — moving to the
  next level of dynamical complexity.

  Key lemma: for any endofunctor G : ℕ ⥤ ℕ, the composite G ⋙ succ
  is never naturally isomorphic to G. In a preorder category, natural
  isomorphism requires pointwise equality of objects. But
  (G ⋙ succ).obj 0 = G.obj 0 + 1 > G.obj 0,
  so the two functors disagree at 0.
-/

noncomputable section

/-! ## Successor functor on ℕ

  Models "increase polynomial degree by one" on the Riemann sphere.
  In complex dynamics terms: if f has degree d, then z·f(z) has degree
  d + 1, producing a dynamical system with a strictly more complex
  Julia set. -/

/-- The successor functor on ℕ: n ↦ n + 1.
    Monotone because a ≤ b implies a + 1 ≤ b + 1. -/
def succNat : ℕ ⥤ ℕ where
  obj n := n + 1
  map {a b} f := homOfLE (by have h := leOfHom f; omega)

/-! ## Boundary functor: S²  ⥤ ℕ

  Maps every sphere point to the base resolution level 0.
  Interpretation: before choosing a dynamical system (a polynomial),
  every point on the Riemann sphere sits at the ground level.
  The fractal boundary structure emerges in ℕ, not in the map itself.

  A constant functor is the honest choice: no nontrivial monotone map
  from the z-coordinate preorder on S² to ℕ captures complex-dynamical
  structure, because Julia set complexity depends on the polynomial,
  not on the point's z-height. -/

/-- Boundary functor: S2Pt → ℕ, constant at 0.
    Every sphere point starts at resolution level 0. -/
def sphereBoundary : S2Pt ⥤ ℕ where
  obj _ := 0
  map _ := homOfLE (le_refl 0)

/-! ## Key lemma: ℕ has inexhaustible endofunctors

  For any monotone self-map G on ℕ, composing with the successor
  produces a strictly different monotone self-map. The proof uses the
  fact that in ℕ (a linear order), natural isomorphism between functors
  on the preorder category requires pointwise equality of objects:
  if G ≅ G', then for all n, G.obj n = G'.obj n (because a ≤ b and
  b ≤ a in ℕ implies a = b). But (G ⋙ succ).obj 0 = G.obj 0 + 1 ≠ G.obj 0.

  This is the categorical core of A4: the successor operation on ℕ
  witnesses that resolution can always be refined. In complex dynamics
  terms: for any finite collection of polynomial degrees, there is always
  a higher degree producing genuinely new Julia set structure. -/

/-- No endofunctor on ℕ is naturally isomorphic to its post-composition
    with the successor. Proof: at object 0, the composite yields
    G.obj 0 + 1, while G yields G.obj 0. In ℕ, these are never equal. -/
theorem succNat_not_iso (G : ℕ ⥤ ℕ) : ¬ Nonempty (G ≅ (G ⋙ succNat)) := by
  intro ⟨iso⟩
  have h1 := leOfHom (iso.app 0).hom
  have h2 := leOfHom (iso.app 0).inv
  simp [Functor.comp_obj, succNat] at h1 h2

/-- ℕ has no terminal resolution: for any endofunctor G, the composite
    G ⋙ succNat is a non-isomorphic endofunctor. -/
theorem nat_no_terminal_resolution :
    ∀ (G : ℕ ⥤ ℕ), ∃ (G' : ℕ ⥤ ℕ), ¬ Nonempty (G ≅ G') :=
  fun G => ⟨G ⋙ succNat, succNat_not_iso G⟩

/-! ## A4 instance: FractalBoundary on S2Pt and ℕ -/

/-- A4 on the sphere: the boundary between S² and ℕ (polynomial degree
    space on the Riemann sphere) has structure at every resolution level.

    The boundary functor maps S2Pt to ℕ (constant at 0 — base resolution).
    The inexhaustibility lives in ℕ: for any endofunctor G, the composite
    G ⋙ succNat is strictly finer. No finite set of polynomial degrees
    captures all the dynamical complexity of rational maps on Ĉ ≅ S². -/
def geoFractalBoundary : FractalBoundary S2Pt ℕ where
  boundary := sphereBoundary
  no_terminal_resolution := nat_no_terminal_resolution

end

/-! # Part II: Combinatorial Consistency Check

  Finite/infinite categorical models demonstrating A4 satisfiability.
  Following the pattern of Bridge.lean Part II and Consistency.lean.

  Model 1: ℕ-based (matching Part I, but without sphere dependency).
  Model 2: Finite 4-element model (matching Consistency.lean's Sea). -/

section CombinatorialCheck

/-! ## Model 1: ℕ-based combinatorial check

  Uses ℕ directly as both C and D, with the identity as boundary.
  This is the purest form of A4: the natural numbers themselves have
  inexhaustible endofunctor structure. -/

/-- Successor functor for the combinatorial model (computable). -/
def succNatComb : ℕ ⥤ ℕ where
  obj n := n + 1
  map {a b} f := homOfLE (by have h := leOfHom f; omega)

/-- A4 combinatorial: ℕ with identity boundary and successor witness. -/
def combFractalBoundary : FractalBoundary ℕ ℕ where
  boundary := Functor.id ℕ
  no_terminal_resolution := fun G => ⟨G ⋙ succNatComb, fun ⟨iso⟩ => by
    have h1 := leOfHom (iso.app 0).hom
    have h2 := leOfHom (iso.app 0).inv
    simp [Functor.comp_obj, succNatComb] at h1 h2⟩

/-! ## Model 2: Finite model (Sea-based, matching Consistency.lean)

  The Sea type from Consistency.lean (h, t, f, abyss) has the property
  that its endofunctor space is finite. A4 still holds because the
  number of endofunctors exceeds 1: constAbyss and the identity functor
  are non-isomorphic.

  This model is included for completeness but is strictly weaker than
  the ℕ-based model — it only shows there are at least 2 endofunctors,
  while ℕ shows there are infinitely many. -/

/-- A 4-element preorder: three connected elements plus an isolated point.
    Matches the Sea type from Consistency.lean. -/
inductive FourPt | a | b | c | iso deriving DecidableEq

instance : LE FourPt where
  le x y := match x, y with
    | .a, .a | .a, .b | .a, .c | .b, .a | .b, .b | .b, .c
    | .c, .c | .iso, .iso => True
    | _, _ => False

instance : Preorder FourPt where
  le_refl x := by cases x <;> trivial
  le_trans x y z := by cases x <;> cases y <;> cases z <;> simp_all [LE.le]

instance (a b : FourPt) : Decidable (a ≤ b) := by
  cases a <;> cases b <;> simp [LE.le] <;> exact inferInstance

/-- Constant functor to the isolated point. -/
def constIso : FourPt ⥤ FourPt where
  obj _ := .iso
  map _ := 𝟙 _

/-- A4 on the finite model: case split on whether G ≅ constIso. -/
def finiteFractalBoundary : FractalBoundary FourPt FourPt where
  boundary := Functor.id _
  no_terminal_resolution := fun G => by
    by_cases h : Nonempty (G ≅ constIso)
    · refine ⟨Functor.id _, fun ⟨iso_id⟩ => ?_⟩
      have := (h.some.app FourPt.a).symm ≪≫ iso_id.app FourPt.a
      simp [constIso] at this
      exact absurd (leOfHom this.inv) (by decide)
    · exact ⟨constIso, h⟩

end CombinatorialCheck

/-! # Bridge Summary — A4 (Fractal Boundary)

  **Geometric bridge** (Part I): A4 constructed with C = S2Pt, D = ℕ.
  Zero sorry, zero axioms beyond propositional logic. The boundary functor
  maps sphere points to ℕ (constant at 0). Inexhaustibility proved via
  the successor functor: for any G : ℕ ⥤ ℕ, the composite G ⋙ succNat
  disagrees with G at object 0 (G.obj 0 + 1 ≠ G.obj 0).

  **Combinatorial checks** (Part II): Two models.
  - ℕ-based: identity boundary, successor witness. Zero sorry.
  - FourPt-based: finite model matching Consistency.lean pattern.

  **Interpretation**: ℕ models polynomial degree on the Riemann sphere.
  The successor functor models "increase degree by one," which always
  produces a dynamical system with genuinely new Julia set structure.
  The proof is purely order-theoretic; the complex dynamics interpretation
  is semantics, not syntax.

  **What resists** (see file header for details):
  - Julia set theory is absent from Mathlib (no Fatou/Julia, no rational
    dynamics on P¹, no Mandelbrot).
  - The boundary functor is constant — the fractal structure lives in D,
    not in the map.
  - The ℕ model is algebraic, not topological — it captures cardinality
    and order but not metric structure of Julia sets.
  - A4 uses D = ℕ while A3 uses D = S2Pt ⊕ PUnit — these are different
    "sea" categories, reflecting different aspects of the sphere's
    relationship to its boundary.

  **Status**: A4 bridged to S². Combined with Bridge.lean (A1-A3) and
  BridgeExtended.lean (A5-A7), all seven axioms are now constructed on
  sphere-derived categories. Zero sorry across the full bridge.
-/

end Sphere
