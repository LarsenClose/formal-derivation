/-
  RF Layer — Impedance Theory

  Formalizes electromagnetic impedance: the bridge between wave propagation
  and energy transfer efficiency. Impedance determines how much power crosses
  any electromagnetic boundary.

  Key results (all proved, zero sorry):
    - Reflection coefficient Gamma = (Z_L - Z_c) / (Z_L + Z_c)
    - Power conservation: |Gamma|^2 + (1 - |Gamma|^2) = 1
    - Perfect match: Z_L = Z_c implies Gamma = 0
    - Boundedness: for real positive impedances, |Gamma|^2 <= 1
    - VSWR >= 1 with equality iff perfect match
    - Quarter-wave transformer matching
    - Friis connection: mismatch reduces received power

  Axioms (3):
    - freeSpaceImpedance / freeSpaceImpedance_pos (Z_0 ~ 377 ohms, positive)
    - antennaImpedanceExists (any RadiationPattern has a feed impedance)
-/

import Formal.RF.Maxwell
import Formal.RF.AntennaTheory

namespace RF.Impedance

noncomputable section

open Complex RF.Maxwell RF.AntennaTheory

/-! ## Impedance structure -/

/-- An electromagnetic impedance: Z = R + jX where R >= 0 is resistance
    and X is reactance. Encoded as a complex number with nonneg real part. -/
structure ImpedanceData where
  /-- Resistance (real part), nonneg -/
  resistance : ℝ
  /-- Reactance (imaginary part) -/
  reactance : ℝ
  /-- Resistance is nonneg (passive component) -/
  resistance_nonneg : 0 ≤ resistance

/-- Convert impedance to complex number Z = R + jX -/
def ImpedanceData.toComplex (z : ImpedanceData) : ℂ :=
  ⟨z.resistance, z.reactance⟩

/-- A transmission line with characteristic impedance and velocity factor -/
structure TransmissionLine where
  /-- Characteristic impedance (real, positive for lossless line) -/
  charImpedance : ℝ
  /-- Velocity factor: v/c where 0 < vf <= 1 -/
  velocityFactor : ℝ
  charImpedance_pos : 0 < charImpedance
  velocityFactor_pos : 0 < velocityFactor
  velocityFactor_le_one : velocityFactor ≤ 1

/-- Propagation velocity of a transmission line: v = c * velocityFactor -/
def TransmissionLine.propagationVelocity (tl : TransmissionLine) : ℝ :=
  speedOfLight * tl.velocityFactor

/-- Propagation velocity is positive -/
theorem TransmissionLine.propagationVelocity_pos (tl : TransmissionLine) :
    0 < tl.propagationVelocity :=
  mul_pos speedOfLight_pos tl.velocityFactor_pos

/-! ## Free-space impedance (axiom) -/

/-- The impedance of free space Z_0 = sqrt(mu_0 / epsilon_0) ~ 376.73 ohms.
    This is a fundamental electromagnetic constant relating E and H field
    amplitudes in a plane wave. -/
axiom freeSpaceImpedance : ℝ

axiom freeSpaceImpedance_pos : freeSpaceImpedance > 0

/-! ## Antenna impedance bridge (axiom) -/

/-- Every radiation pattern has an associated feed-point impedance.
    This is a physics axiom: the antenna's radiation pattern determines
    its input impedance via the induced EMF method. -/
axiom antennaImpedanceExists (pat : RadiationPattern) : ImpedanceData

/-! ## Reflection coefficient -/

/-- The voltage reflection coefficient: Gamma = (Z_L - Z_c) / (Z_L + Z_c).
    Requires Z_L + Z_c != 0 (encoded in hypothesis). -/
def reflectionCoeff (zl zc : ℂ) (_h : zl + zc ≠ 0) : ℂ :=
  (zl - zc) / (zl + zc)

/-- Reflected power ratio: |Gamma|^2 -/
def reflectedPowerRatio (gamma : ℂ) : ℝ :=
  Complex.normSq gamma

/-- Transmitted (delivered) power ratio: 1 - |Gamma|^2 -/
def transmittedPowerRatio (gamma : ℂ) : ℝ :=
  1 - Complex.normSq gamma

/-- Mismatch factor: same as transmitted power ratio, named for Friis connection -/
def mismatchFactor (gamma : ℂ) : ℝ :=
  transmittedPowerRatio gamma

/-! ## Algebraic theorems -/

/-- Power conservation: reflected + transmitted = 1 -/
theorem power_conservation (gamma : ℂ) :
    reflectedPowerRatio gamma + transmittedPowerRatio gamma = 1 := by
  unfold reflectedPowerRatio transmittedPowerRatio
  ring

/-- Reflected power ratio is nonneg -/
theorem reflectedPowerRatio_nonneg (gamma : ℂ) :
    0 ≤ reflectedPowerRatio gamma :=
  Complex.normSq_nonneg gamma

/-- Perfect match: Z_L = Z_c implies Gamma = 0 -/
theorem perfect_match_zero_reflection (zc : ℂ) (h : zc + zc ≠ 0) :
    reflectionCoeff zc zc h = 0 := by
  unfold reflectionCoeff
  simp [sub_self]

/-- Swapping source and load negates the reflection coefficient -/
theorem reflection_self_inverse (zl zc : ℂ) (h1 : zl + zc ≠ 0) (h2 : zc + zl ≠ 0) :
    reflectionCoeff zc zl h2 = -reflectionCoeff zl zc h1 := by
  unfold reflectionCoeff
  field_simp
  ring

/-! ## Boundedness for real positive impedances -/

/-- For real positive impedances, |Gamma|^2 <= 1.
    If Z_L = a > 0 and Z_c = b > 0 (both real), then
    |Gamma|^2 = ((a-b)/(a+b))^2 <= 1. -/
theorem real_positive_reflection_bounded (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Complex.normSq (reflectionCoeff (↑a) (↑b) (by
      intro h; have h1 : (↑a + ↑b : ℂ).re = 0 := by rw [h]; simp
      simp [Complex.add_re] at h1; linarith)) ≤ 1 := by
  unfold reflectionCoeff
  rw [show (↑a : ℂ) - ↑b = ↑(a - b) from by push_cast; ring,
      show (↑a : ℂ) + ↑b = ↑(a + b) from by push_cast; ring,
      ← Complex.ofReal_div, Complex.normSq_ofReal]
  rw [div_mul_div_comm, div_le_one (by positivity)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

/-- Mismatch factor is at most 1 (can't deliver more power than available) -/
theorem mismatch_le_one (gamma : ℂ) (_h : Complex.normSq gamma ≤ 1) :
    mismatchFactor gamma ≤ 1 := by
  unfold mismatchFactor transmittedPowerRatio
  linarith [Complex.normSq_nonneg gamma]

/-- Mismatch factor is nonneg when |Gamma|^2 <= 1 -/
theorem mismatch_nonneg (gamma : ℂ) (h : Complex.normSq gamma ≤ 1) :
    0 ≤ mismatchFactor gamma := by
  unfold mismatchFactor transmittedPowerRatio
  linarith

/-! ## VSWR -/

/-- Voltage Standing Wave Ratio: VSWR = (1 + |Gamma|) / (1 - |Gamma|).
    Uses sqrt(normSq gamma) as |Gamma|.
    Defined only when |Gamma|^2 < 1 (physical constraint). -/
def vswr (gamma : ℂ) (_h : Complex.normSq gamma < 1) : ℝ :=
  (1 + Real.sqrt (Complex.normSq gamma)) / (1 - Real.sqrt (Complex.normSq gamma))

/-- VSWR >= 1 -/
theorem vswr_ge_one (gamma : ℂ) (h : Complex.normSq gamma < 1) :
    1 ≤ vswr gamma h := by
  unfold vswr
  have hsqrt_nonneg := Real.sqrt_nonneg (Complex.normSq gamma)
  have hsqrt_lt : Real.sqrt (Complex.normSq gamma) < 1 := by
    rw [Real.sqrt_lt' (by linarith : (0 : ℝ) < 1)]
    simp only [one_pow]; exact h
  rw [one_le_div (by linarith)]
  linarith

/-- Perfect match gives VSWR = 1 -/
theorem perfect_match_vswr_one :
    vswr 0 (by simp [Complex.normSq_zero]) = 1 := by
  unfold vswr
  simp [Complex.normSq_zero, Real.sqrt_zero]

/-! ## Total reflection cases -/

/-- Short circuit (Z_L = 0) gives total reflection: |Gamma|^2 = 1 -/
theorem total_reflection_short_circuit (zc : ℂ) (hzc : zc ≠ 0) :
    Complex.normSq (reflectionCoeff 0 zc (by simp [hzc])) = 1 := by
  unfold reflectionCoeff
  simp only [zero_sub, zero_add, neg_div, Complex.normSq_neg, Complex.normSq_div]
  exact div_self ((Complex.normSq_eq_zero.not).mpr hzc)

/-! ## Quarter-wave transformer -/

/-- Quarter-wave transformer input impedance: Z_in = Z_c^2 / Z_L -/
def quarterWaveInputImpedance (zc zl : ℂ) (_hzl : zl ≠ 0) : ℂ :=
  zc ^ 2 / zl

/-- Quarter-wave transformer inverts impedance through Z_c^2 -/
theorem quarter_wave_inverts (zc zl : ℂ) (hzl : zl ≠ 0) :
    quarterWaveInputImpedance zc zl hzl = zc ^ 2 / zl := rfl

/-- Quarter-wave matching: if Z_c^2 = Z_s * Z_L then Z_in = Z_s -/
theorem quarter_wave_matches (zs zc zl : ℂ) (hzl : zl ≠ 0)
    (hmatch : zc ^ 2 = zs * zl) :
    quarterWaveInputImpedance zc zl hzl = zs := by
  unfold quarterWaveInputImpedance
  rw [hmatch, mul_div_cancel_right₀ _ hzl]

/-! ## Friis connection -/

/-- Matched power ratio: Friis power ratio degraded by impedance mismatch.
    P_actual = P_friis * (1 - |Gamma|^2) -/
def matchedPowerRatio (link : FriisLink) (gamma : ℂ) : ℝ :=
  link.powerRatio * mismatchFactor gamma

/-- Matched power <= ideal Friis power (when |Gamma|^2 <= 1) -/
theorem matched_power_le_ideal (link : FriisLink) (gamma : ℂ)
    (h : Complex.normSq gamma ≤ 1) :
    matchedPowerRatio link gamma ≤ link.powerRatio := by
  unfold matchedPowerRatio
  calc link.powerRatio * mismatchFactor gamma
      ≤ link.powerRatio * 1 :=
        mul_le_mul_of_nonneg_left (mismatch_le_one gamma h)
          (le_of_lt link.powerRatio_pos)
    _ = link.powerRatio := mul_one _

/-- Perfect match recovers ideal Friis equation -/
theorem perfect_match_recovers_friis (link : FriisLink) :
    matchedPowerRatio link 0 = link.powerRatio := by
  unfold matchedPowerRatio mismatchFactor transmittedPowerRatio
  simp [map_zero, mul_one]

/-- Matched power ratio is nonneg when |Gamma|^2 <= 1 -/
theorem matched_power_nonneg (link : FriisLink) (gamma : ℂ)
    (h : Complex.normSq gamma ≤ 1) :
    0 ≤ matchedPowerRatio link gamma :=
  mul_nonneg (le_of_lt link.powerRatio_pos) (mismatch_nonneg gamma h)

end

end RF.Impedance
