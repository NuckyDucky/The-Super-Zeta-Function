import DottieDirectReferenceScore
import DottieCosRescale

namespace QuarticModel

open private referencePhaseRat referenceLog referenceAngleBeforeWrap referenceAngleBeforeWrap_eq
  directReferenceAngle directReferenceQuarter directReferenceCosineTicks referenceLog_enclosure
  from DottieDirectReferenceScore
open private log_lt_twenty_two from DottiePreciseMomentHeight

set_option autoImplicit false

-- This denominator represents the height, phase, pi and log ticks together.
private def phaseBase : ℕ := 2^116 * 5^30
private def piTicks : ℕ := 243068958312725669170431586544934771577391369597682188288
private def phaseTicks : ℕ := 303521612787161781551881792984819548815360000000000000000
private def heightTicks : ℕ := 4420038400857368548163288407086865234375
private def lowerCircleShiftTicks : ℕ := 1907348632812500000000000

private def rawReferenceTicks (ticks : ℕ) : ℤ :=
  (phaseTicks : ℤ) - ((heightTicks - lowerCircleShiftTicks) * ticks : ℕ)

private def referenceAngleNumerator (n : ℕ) : ℤ :=
  (piTicks : ℤ) - ((piTicks : ℤ) - rawReferenceTicks (dottieCachedLogLowerTicks n)) % (2*piTicks)

private def referenceQuarterDenominator : ℕ := 4 * phaseBase

private theorem pi_ticks_eq : dottieMomentPiRat = (piTicks : ℚ) / phaseBase := by
  norm_num [dottieMomentPiRat, piTicks, phaseBase]

private theorem raw_reference_ticks_eq (n : ℕ) :
    (rawReferenceTicks (dottieCachedLogLowerTicks n) : ℚ) / phaseBase =
      referencePhaseRat - dottieMomentHeightRat * referenceLog n + referenceLog n/512 := by
  unfold rawReferenceTicks referenceLog
  push_cast [show lowerCircleShiftTicks ≤ heightTicks by decide +kernel]
  norm_num [referencePhaseRat, dottieMomentHeightRat, phaseBase, phaseTicks,
    heightTicks, lowerCircleShiftTicks]
  ring

private theorem before_wrap_eq (n : ℕ) (hn : 0 < n) :
    referenceAngleBeforeWrap n =
      (rawReferenceTicks (dottieCachedLogLowerTicks n) : ℚ) / phaseBase -
        2 * dottieMomentPiRat * (dottieMomentAngleTurn n : ℚ) := by
  rw [referenceAngleBeforeWrap_eq hn, raw_reference_ticks_eq]
  unfold dottieMomentReducedAngle dottieMomentAngle referenceLog
  rw [dottieCachedLogLowerTicks_eq n hn]
  ring

private theorem angle_representation (n : ℕ) (hn : 0 < n) (hN : n ≤ 276824064) :
    ∃ q : ℤ, directReferenceAngle n =
      (rawReferenceTicks (dottieCachedLogLowerTicks n) : ℚ) / phaseBase -
        2 * dottieMomentPiRat * (q : ℚ) ∧
      -dottieMomentPiRat < directReferenceAngle n ∧
      directReferenceAngle n ≤ dottieMomentPiRat := by
  obtain ⟨hLo, hHi⟩ := dottie_moment_reduced_angle_bounds n
  obtain ⟨hLogLo, hLogHi, _⟩ := referenceLog_enclosure hn hN
  have hLogLo' : 0 ≤ referenceLog n := by exact_mod_cast hLogLo
  have hLogHi' : referenceLog n ≤ 22 := by
    exact_mod_cast hLogHi.trans (log_lt_twenty_two hn (hN.trans (by decide +kernel))).le
  have hPi : (3 : ℚ) < dottieMomentPiRat := by norm_num [dottieMomentPiRat]
  have hPhase : 0 < referencePhaseRat ∧ referencePhaseRat < 4 := by norm_num [referencePhaseRat]
  unfold directReferenceAngle
  dsimp only
  split
  · rename_i h
    refine ⟨dottieMomentAngleTurn n, before_wrap_eq n hn, ?_, h⟩
    rw [referenceAngleBeforeWrap_eq hn]
    linarith only [hLo, hLogLo', hPhase.1]
  · rename_i h
    refine ⟨dottieMomentAngleTurn n + 1, ?_, ?_, ?_⟩
    · rw [before_wrap_eq n hn, Int.cast_add, Int.cast_one]
      ring
    · linarith only [lt_of_not_ge h]
    · rw [referenceAngleBeforeWrap_eq hn]
      linarith only [hHi, hLogHi', hPi, hPhase.2]

private theorem centered_remainder (raw p q : ℤ)
    (hLo : -p < raw - 2*p*q) (hHi : raw - 2*p*q ≤ p) :
    p - (p - raw) % (2*p) = raw - 2*p*q := by
  have h : p - raw = (p - (raw - 2*p*q)) + (-q)*(2*p) := by ring
  have he : (p - raw) % (2*p) = p - (raw - 2*p*q) := by
    rw [h, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
  rw [he]
  ring

private theorem angle_numerator_eq (n : ℕ) (hn : 0 < n) (hN : n ≤ 276824064) :
    (referenceAngleNumerator n : ℚ) / phaseBase = directReferenceAngle n := by
  obtain ⟨q, he, hlo, hhi⟩ := angle_representation n hn hN
  let raw := rawReferenceTicks (dottieCachedLogLowerTicks n)
  let p : ℤ := piTicks
  have hScaled : directReferenceAngle n = ((raw - 2*p*q : ℤ) : ℚ) / phaseBase := by
    rw [he, pi_ticks_eq]
    simp only [p, raw, Int.cast_natCast, Int.cast_sub, Int.cast_mul, Int.cast_ofNat]
    ring
  rw [hScaled, pi_ticks_eq] at hlo hhi
  have hBase : 0 < (phaseBase : ℚ) := by norm_num [phaseBase]
  rw [← neg_div] at hlo
  have hLo : -p < raw - 2*p*q := by
    have h := (div_lt_div_iff_of_pos_right hBase).1 hlo
    exact_mod_cast h
  have hHi : raw - 2*p*q ≤ p := by
    have h := (div_le_div_iff_of_pos_right hBase).1 hhi
    exact_mod_cast h
  have hp : 2 * p = ((2 * piTicks : ℕ) : ℤ) := by simp [p]
  unfold referenceAngleNumerator
  change ((p - (p - raw) % ((2 * piTicks : ℕ) : ℤ) : ℤ) : ℚ) / phaseBase = _
  rw [← hp, centered_remainder raw p q hLo hHi, hScaled]

private theorem quarter_ticks_eq (n : ℕ) (hn : 0 < n) (hN : n ≤ 276824064) :
    (referenceAngleNumerator n : ℝ) / referenceQuarterDenominator =
      (directReferenceQuarter n : ℝ) := by
  have h : (referenceAngleNumerator n : ℚ) / referenceQuarterDenominator =
      directReferenceQuarter n := by
    unfold referenceQuarterDenominator directReferenceQuarter
    rw [Nat.cast_mul, Nat.cast_ofNat, mul_comm (4 : ℚ), ← div_div, angle_numerator_eq n hn hN]
  simpa only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] using
    congrArg (fun x : ℚ => (x : ℝ)) h

private theorem quarter_cosine_eq (n : ℕ) (hn : 0 < n) (hN : n ≤ 276824064) :
    fixedCosBounds (referenceAngleNumerator n) referenceQuarterDenominator =
      fixedCosBounds (directReferenceQuarter n).num (directReferenceQuarter n).den := by
  apply fixedCosBounds_eq_of_div_eq _ _ _ _ (by decide +kernel) (directReferenceQuarter n).den_pos
  rw [quarter_ticks_eq n hn hN, Rat.cast_def]

private def referenceCosineTicks (n : ℕ) : ℤ :=
  let c := (fixedCosBounds (referenceAngleNumerator n) referenceQuarterDenominator).1
  let scale : ℤ := fixedCosScale
  8*c^4 - 8*scale^2*c^2 + scale^4

/-- Integer-only phase reduction for the original reference weight within the certified prefix. -/
def dottieFastReferenceWeight (n : ℕ) : ℤ :=
  if n ≤ 276824064 then (inverseSqrtTicks (2^64) n : ℤ) * referenceCosineTicks n
  else dottieDirectReferenceWeight n

/-- The faster computation yields exactly the original integer, including its rounding. -/
theorem dottie_fast_reference_weight_eq (n : ℕ) :
    dottieFastReferenceWeight n = dottieDirectReferenceWeight n := by
  by_cases hN : n ≤ 276824064
  · rw [dottieFastReferenceWeight, if_pos hN, dottieDirectReferenceWeight]
    cases n with
    | zero => simp [inverseSqrtTicks]
    | succ n => simp only [referenceCosineTicks, directReferenceCosineTicks,
        quarter_cosine_eq (n+1) (Nat.succ_pos n) hN]
  · simp only [dottieFastReferenceWeight, if_neg hN]

def dottieFastReferenceScore : ℤ :=
  dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 (276824064 : ℕ).sqrt

theorem dottie_fast_reference_score_eq : dottieFastReferenceScore = dottieDirectReferenceScore := by
  unfold dottieFastReferenceScore dottieDirectReferenceScore
  rw [funext dottie_fast_reference_weight_eq]

#print axioms dottie_fast_reference_weight_eq
#print axioms dottie_fast_reference_score_eq

end QuarticModel
