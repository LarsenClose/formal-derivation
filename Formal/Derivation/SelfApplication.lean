/-
  Self-Application — The Derivation Certifies Itself

  The derivation chain (fullChain) proves: Nonempty ThereIs -> Nonempty SphereIsS2.
  The phase-invariance framework (Phases.lean) defines FormallyDerived propositions
  and proves they have phase-invariant validity conditions.

  This file instantiates FormallyDerived for the fullChain result itself:
  the framework that evaluates phase-invariance certifies that its own central
  theorem IS phase-invariant. The system checks itself -- not circularly,
  because the check is mechanical (proof checking is phase-independent).

  This is the formal analogue of paper section 6.11:
  "The Paper's Own Schema Applied to Its Central Claim."

  Three altitudes of the same structure:
    1. "There is" survives self-application (the primitive, Step 1)
    2. The paper applies its own schema to its claim (section 6.11)
    3. The Lean formalization proves its central theorem satisfies the
       phase-invariance property it defines (this file)
-/

import Formal.Derivation.Chain
import Formal.Derivation.Phases

namespace DerivationChain

open PhaseEpistemology

/-!
## The Central Claim as a Phase-Indexed Proposition

We wrap `fullChain`'s type -- `Nonempty ThereIs -> Nonempty SphereIsS2` --
as a `PhaseIndexedProp`. The proposition is parametric over any `PhaseSpace`:
the whole point is that formal derivation produces phase-invariant results
regardless of which phases of consciousness exist.

The validity conditions are set to `ValidityCondition.universal`: they hold
in every phase. This is not an assumption -- it is what it MEANS for a
proposition to be formally derived. The proof steps (the body of `fullChain`)
constitute the validity conditions, and a proof checker can verify them from
any phase.
-/

/-- The central claim of the derivation chain, wrapped as a phase-indexed
    proposition. For any phase space:
    - content = the derivation from "there is" to S^2
    - phase = an arbitrary generating phase (the claim is formal, not phase-bound)
    - depth = 0 (the derivation is self-contained, requires no prior perspectives)
    - validity = universal (holds in every phase, because proof is phase-independent) -/
def centralClaim (Phase : Type*) [PhaseSpace Phase] (φ₀ : Phase) :
    PhaseIndexedProp Phase where
  content := Nonempty ThereIs → Nonempty SphereIsS2
  phase := φ₀
  depth := 0
  validity := ValidityCondition.universal Phase

/-- The central claim is formally derived: `fullChain` is the proof of its content,
    and its validity conditions hold universally because they are the proof steps
    themselves -- checkable from any phase by a mechanical verifier. -/
def centralClaim_formallyDerived (Phase : Type*) [PhaseSpace Phase] (φ₀ : Phase) :
    FormallyDerived (centralClaim Phase φ₀) where
  content_proved := fullChain
  validity_universal := fun _ => trivial

/-!
## Self-Application: The Derivation Certifies Itself

The framework proves that formally-derived propositions are phase-invariant
(`phase_invariant_C`). The derivation chain IS formally derived (`centralClaim_formallyDerived`).
Therefore the derivation chain is phase-invariant. The framework certifies its
own central result.
-/

/-- **Self-application theorem**: the derivation chain's central result
    satisfies the phase-invariance property that the framework defines.

    The framework certifies itself: `phase_invariant_C` applied to `fullChain`
    yields phase-invariance of the derivation. This is not circular -- the
    check is mechanical. `fullChain` compiles (it is a proof), therefore
    `FormallyDerived` is instantiated, therefore `PhaseInvariant` follows. -/
theorem derivation_certifies_itself (Phase : Type*) [PhaseSpace Phase] (φ₀ : Phase) :
    PhaseInvariant (centralClaim Phase φ₀) :=
  phase_invariant_C (centralClaim Phase φ₀) (centralClaim_formallyDerived Phase φ₀)

/-- The central claim is not phase-locked: its validity does not depend on the
    generating phase. This follows from `formally_derived_not_locked` applied
    to the central claim. -/
theorem derivation_not_phase_locked (Phase : Type*) [ps : PhaseSpace Phase] (φ₀ : Phase) :
    ¬ PhaseLocked (centralClaim Phase φ₀) :=
  formally_derived_not_locked (centralClaim Phase φ₀) (centralClaim_formallyDerived Phase φ₀)

/-- The central claim survives translation into any target phase.
    Any translation function that satisfies the coherence conditions
    (identity + invariant preservation) will preserve the derivation. -/
theorem derivation_survives_translation (Phase : Type*) [PhaseSpace Phase]
    (φ₀ : Phase) (T : Translation Phase) :
    ∀ ψ : Phase, T.translate (centralClaim Phase φ₀) ψ =
      TranslationOutcome.preserved (centralClaim Phase φ₀) :=
  formally_derived_preserved T (centralClaim Phase φ₀) (centralClaim_formallyDerived Phase φ₀)

/-!
## Independence from Generating Phase

The choice of generating phase φ₀ is irrelevant: the phase-invariance
and non-locking results hold for ANY φ₀. This makes the self-application
genuinely universal -- not tied to any particular phase of consciousness.
-/

/-- Phase-invariance holds regardless of which phase is designated as
    the generating phase. The formal derivation is phase-independent
    in the strongest sense: not only do its validity conditions hold
    everywhere, but this fact is independent of the choice of φ₀. -/
theorem self_application_phase_independent (Phase : Type*) [PhaseSpace Phase] :
    ∀ φ₀ : Phase, PhaseInvariant (centralClaim Phase φ₀) :=
  fun φ₀ => derivation_certifies_itself Phase φ₀

/-!
## Summary

### Proved (zero sorry, zero additional axioms)
- `centralClaim`: wraps fullChain as a PhaseIndexedProp
- `centralClaim_formallyDerived`: fullChain IS the proof, validity is universal
- `derivation_certifies_itself`: the framework certifies its own central result
- `derivation_not_phase_locked`: the central claim is not phase-locked
- `derivation_survives_translation`: the central claim survives all translations
- `self_application_phase_independent`: results hold for any generating phase

### Structure
The self-application is a three-step argument:
1. `fullChain` compiles -- it is a Lean proof (mechanically verified)
2. Therefore `FormallyDerived` is instantiated (content_proved = fullChain)
3. Therefore `PhaseInvariant` follows (by phase_invariant_C)

No circularity: step 1 is a fact about the compiler, step 2 is instantiation,
step 3 is application of an already-proved theorem. The system checks itself
the way a proof checker checks proofs -- mechanically, not self-referentially.
-/

end DerivationChain
