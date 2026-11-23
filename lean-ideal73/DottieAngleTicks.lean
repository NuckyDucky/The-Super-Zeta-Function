import DottieNormPhase
import Batteries.Tactic.OpenPrivate

namespace QuarticModel

open private piLower referenceHeightRat referenceAngleRat normAngle periodCount from DottieNormPhase

-- A common denominator for the phase, the height times the log ticks, and π's lower bound.
private def angleBase : ℕ := 10^12 * 2^96 * 5^8
private def anglePiTicks : ℕ := 314159265358979323846 * 2^88
private def anglePeriodTicks : ℕ := 2 * anglePiTicks
private def anglePhaseTicks : ℕ := 39229252 * 10^5 * 2^96 * 5^8
private def angleHeightMultiplier : ℕ := 4526119322477943440197603 * 5^8

private def angleRawTicks (n : ℕ) : ℤ :=
  (anglePhaseTicks : ℤ) - ((angleHeightMultiplier * (normLogBounds (2^96) 31 n).1 : ℕ) : ℤ)

/-- The common phase denominator, including the factor of four for the quarter angle. -/
def dottieAngleDenominator : ℕ := 4 * angleBase

/-- Reduce the phase to one centered period using an integer Euclidean remainder. -/
def dottieAngleNumerator (n : ℕ) : ℤ :=
  Int.emod (angleRawTicks n + (anglePiTicks : ℤ)) (anglePeriodTicks : ℤ) - (anglePiTicks : ℤ)

private theorem anglePi_eq : piLower = (anglePiTicks : ℚ) / angleBase := by
  norm_num [piLower, anglePiTicks, angleBase]

private theorem angleBase_ne_zero : (angleBase : ℚ) ≠ 0 := by
  norm_num [angleBase]

private theorem normAngle_eq_ticks (n : ℕ) : normAngle n = (angleRawTicks n : ℚ) / angleBase := by
  unfold normAngle angleRawTicks
  push_cast
  norm_num [referenceAngleRat, referenceHeightRat, anglePhaseTicks, angleHeightMultiplier,
    angleBase]
  ring

private theorem periodCount_eq_ticks (n : ℕ) :
    periodCount n = (angleRawTicks n + (anglePiTicks : ℤ)) / (anglePeriodTicks : ℤ) := by
  unfold periodCount
  rw [normAngle_eq_ticks, anglePi_eq]
  have hFrac :
      ((angleRawTicks n : ℚ) / angleBase + (anglePiTicks : ℚ) / angleBase) /
          (2 * ((anglePiTicks : ℚ) / angleBase)) =
        ((angleRawTicks n + (anglePiTicks : ℤ) : ℤ) : ℚ) / (anglePeriodTicks : ℚ) := by
    rw [← add_div, ← mul_div_assoc, div_div_div_cancel_right₀ angleBase_ne_zero]
    simp only [anglePeriodTicks, Nat.cast_mul, Nat.cast_ofNat, Int.cast_add, Int.cast_natCast]
  rw [hFrac, Rat.floor_intCast_div_natCast]

private theorem dottieAngleTicks_rat (n : ℕ) :
    (dottieAngleNumerator n : ℚ) / dottieAngleDenominator = dottieNormAngleQuarter n := by
  rw [dottieNormAngleQuarter, normAngle_eq_ticks, periodCount_eq_ticks, anglePi_eq]
  unfold dottieAngleNumerator dottieAngleDenominator
  have hEmod := Int.emod_def (angleRawTicks n + (anglePiTicks : ℤ)) (anglePeriodTicks : ℤ)
  change Int.emod _ _ = _ at hEmod
  rw [hEmod]
  simp only [anglePeriodTicks, Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [mul_comm (4 : ℚ) (angleBase : ℚ), ← div_div]
  ring

/-- The integer quotient gives the original rational quarter angle at every norm. -/
theorem dottieAngleTicks_eq_quarter (n : ℕ) :
    (dottieAngleNumerator n : ℝ) / dottieAngleDenominator = (dottieNormAngleQuarter n : ℝ) := by
  simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
    congrArg (fun a : ℚ => (a : ℝ)) (dottieAngleTicks_rat n)

theorem dottieAngleDenominator_pos : 0 < dottieAngleDenominator := by decide +kernel

/-- The centered quarter angle is in the input range of `fixedCosBounds`. -/
theorem dottieAngleNumerator_natAbs_le (n : ℕ) :
    (dottieAngleNumerator n).natAbs ≤ dottieAngleDenominator := by
  let p : ℤ := anglePiTicks
  let a : ℤ := angleRawTicks n + p
  have hp : 0 < (anglePeriodTicks : ℤ) := by decide +kernel
  have hlo := Int.emod_nonneg a hp.ne'
  have htwice : (anglePeriodTicks : ℤ) = 2 * p := by simp [anglePeriodTicks, p]
  have hhi := (Int.emod_lt_of_pos a hp).trans_le htwice.le
  have hpd : p ≤ (dottieAngleDenominator : ℤ) := by
    change (anglePiTicks : ℤ) ≤ (dottieAngleDenominator : ℤ)
    decide +kernel
  have hAbs : |dottieAngleNumerator n| ≤ (dottieAngleDenominator : ℤ) := by
    change |a % (anglePeriodTicks : ℤ) - p| ≤ _
    exact abs_le.mpr ⟨by omega, by omega⟩
  have hCast : ((dottieAngleNumerator n).natAbs : ℤ) ≤ (dottieAngleDenominator : ℤ) := by
    rwa [Int.natCast_natAbs]
  exact_mod_cast hCast

#print axioms dottieAngleTicks_eq_quarter
#print axioms dottieAngleDenominator_pos
#print axioms dottieAngleNumerator_natAbs_le

end QuarticModel
