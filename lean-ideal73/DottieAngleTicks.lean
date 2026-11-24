import DottieNormPhase
import Batteries.Tactic.OpenPrivate

namespace QuarticModel

open private piLower referenceHeightRat referenceAngleRat normAngleOf from DottieNormPhase

-- A common denominator for the phase, the height times the log ticks, and π's lower bound.
private def angleBase : ℕ := 10^12 * 2^96 * 5^8
private def anglePiTicks : ℕ := 314159265358979323846 * 2^88
private def anglePeriodTicks : ℕ := 2 * anglePiTicks
private def anglePhaseTicks : ℕ := 39229252 * 10^5 * 2^96 * 5^8
private def angleHeightMultiplier : ℕ := 4526119322477943440197603 * 5^8

private def angleRawTicks (ticks : ℕ) : ℤ :=
  (anglePhaseTicks : ℤ) - ((angleHeightMultiplier * ticks : ℕ) : ℤ)

/-- The common phase denominator, including the factor of four for the quarter angle. -/
def dottieAngleDenominator : ℕ := 4 * angleBase

/-- Reduce the phase from supplied log ticks to one centered period. -/
def dottieAngleNumeratorOf (ticks : ℕ) : ℤ :=
  Int.emod (angleRawTicks ticks + (anglePiTicks : ℤ)) (anglePeriodTicks : ℤ) - (anglePiTicks : ℤ)

/-- The centered phase numerator for the original log evaluation. -/
def dottieAngleNumerator (n : ℕ) : ℤ :=
  dottieAngleNumeratorOf (normLogBounds (2^96) 31 n).1

private theorem anglePi_eq : piLower = (anglePiTicks : ℚ) / angleBase := by
  norm_num [piLower, anglePiTicks, angleBase]

private theorem angleBase_ne_zero : (angleBase : ℚ) ≠ 0 := by
  norm_num [angleBase]

private theorem normAngleOf_eq_ticks (ticks : ℕ) :
    normAngleOf ticks = (angleRawTicks ticks : ℚ) / angleBase := by
  unfold normAngleOf angleRawTicks
  push_cast
  norm_num [referenceAngleRat, referenceHeightRat, anglePhaseTicks, angleHeightMultiplier,
    angleBase]
  ring

private theorem periodCountOf_eq_ticks (ticks : ℕ) :
    dottieNormPeriodCountOf ticks =
      (angleRawTicks ticks + (anglePiTicks : ℤ)) / (anglePeriodTicks : ℤ) := by
  unfold dottieNormPeriodCountOf
  rw [normAngleOf_eq_ticks, anglePi_eq]
  have hFrac :
      ((angleRawTicks ticks : ℚ) / angleBase + (anglePiTicks : ℚ) / angleBase) /
          (2 * ((anglePiTicks : ℚ) / angleBase)) =
        ((angleRawTicks ticks + (anglePiTicks : ℤ) : ℤ) : ℚ) / (anglePeriodTicks : ℚ) := by
    rw [← add_div, ← mul_div_assoc, div_div_div_cancel_right₀ angleBase_ne_zero]
    simp only [anglePeriodTicks, Nat.cast_mul, Nat.cast_ofNat, Int.cast_add, Int.cast_natCast]
  rw [hFrac, Rat.floor_intCast_div_natCast]

private theorem dottieAngleTicks_rat_of (ticks : ℕ) :
    (dottieAngleNumeratorOf ticks : ℚ) / dottieAngleDenominator = dottieNormAngleQuarterOf ticks := by
  rw [dottieNormAngleQuarterOf, normAngleOf_eq_ticks, periodCountOf_eq_ticks, anglePi_eq]
  unfold dottieAngleNumeratorOf dottieAngleDenominator
  have hEmod := Int.emod_def (angleRawTicks ticks + (anglePiTicks : ℤ)) (anglePeriodTicks : ℤ)
  change Int.emod _ _ = _ at hEmod
  rw [hEmod]
  simp only [anglePeriodTicks, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_comm (4 : ℚ) (angleBase : ℚ), ← div_div]
  ring

/-- The fixed-denominator quotient equals the rational quarter angle for every log tick. -/
theorem dottieAngleTicks_eq_quarter_of (ticks : ℕ) :
    (dottieAngleNumeratorOf ticks : ℝ) / dottieAngleDenominator =
      (dottieNormAngleQuarterOf ticks : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
    congrArg (fun a : ℚ => (a : ℝ)) (dottieAngleTicks_rat_of ticks)

/-- The integer quotient gives the original rational quarter angle at every norm. -/
theorem dottieAngleTicks_eq_quarter (n : ℕ) :
    (dottieAngleNumerator n : ℝ) / dottieAngleDenominator = (dottieNormAngleQuarter n : ℝ) :=
  dottieAngleTicks_eq_quarter_of (normLogBounds (2^96) 31 n).1

theorem dottieAngleDenominator_pos : 0 < dottieAngleDenominator := by decide +kernel

/-- The centered quarter angle is in the input range of `fixedCosBounds`. -/
theorem dottieAngleNumeratorOf_natAbs_le (ticks : ℕ) :
    (dottieAngleNumeratorOf ticks).natAbs ≤ dottieAngleDenominator := by
  let p : ℤ := anglePiTicks
  let a : ℤ := angleRawTicks ticks + p
  have hp : 0 < (anglePeriodTicks : ℤ) := by decide +kernel
  have hlo := Int.emod_nonneg a hp.ne'
  have htwice : (anglePeriodTicks : ℤ) = 2 * p := by simp [anglePeriodTicks, p]
  have hhi := (Int.emod_lt_of_pos a hp).trans_le htwice.le
  have hpd : p ≤ (dottieAngleDenominator : ℤ) := by
    change (anglePiTicks : ℤ) ≤ (dottieAngleDenominator : ℤ)
    decide +kernel
  have hAbs : |dottieAngleNumeratorOf ticks| ≤ (dottieAngleDenominator : ℤ) := by
    change |a % (anglePeriodTicks : ℤ) - p| ≤ _
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hCast : ((dottieAngleNumeratorOf ticks).natAbs : ℤ) ≤ (dottieAngleDenominator : ℤ) := by
    rwa [Int.natCast_natAbs]
  exact_mod_cast hCast

theorem dottieAngleNumerator_natAbs_le (n : ℕ) :
    (dottieAngleNumerator n).natAbs ≤ dottieAngleDenominator :=
  dottieAngleNumeratorOf_natAbs_le (normLogBounds (2^96) 31 n).1

#print axioms dottieAngleTicks_eq_quarter_of
#print axioms dottieAngleTicks_eq_quarter
#print axioms dottieAngleDenominator_pos
#print axioms dottieAngleNumeratorOf_natAbs_le
#print axioms dottieAngleNumerator_natAbs_le

end QuarticModel
