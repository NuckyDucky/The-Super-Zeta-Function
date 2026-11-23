import DottieAngleTicks
import DottieFixedCos
import Batteries.Tactic.OpenPrivate

namespace QuarticModel

open private cosHornerTicks cosStep from DottieFixedCos

/-- Equal cross products give equal natural quotients when both denominators are positive. -/
private theorem natDiv_eq_of_cross_mul {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : a * d = c * b) : a / b = c / d := by
  have hLe (n : ℕ) : n ≤ a / b ↔ n ≤ c / d := by
    rw [Nat.le_div_iff_mul_le hb, Nat.le_div_iff_mul_le hd]
    calc
      n * b ≤ a ↔ (n * b) * d ≤ a * d := (Nat.mul_le_mul_right_iff hd).symm
      _ ↔ (n * d) * b ≤ c * b := by rw [mul_right_comm n b d, h]
      _ ↔ n * d ≤ c := Nat.mul_le_mul_right_iff hb
  exact le_antisymm ((hLe _).mp le_rfl) ((hLe _).mpr le_rfl)

private theorem cosHornerTicks_eq_of_cross_mul (scale aSq bSq cSq dSq : ℕ)
    (hb : 0 < bSq) (hd : 0 < dSq) (h : aSq * dSq = cSq * bSq) (terms i : ℕ) :
    cosHornerTicks scale aSq bSq terms i = cosHornerTicks scale cSq dSq terms i := by
  induction terms generalizing i with
  | zero => rfl
  | succ terms ih =>
    simp only [cosHornerTicks, ih (i + 1)]
    apply congrArg (fun ticks : ℕ => scale - ticks)
    have hs : 0 < cosStep i := by unfold cosStep; positivity
    apply natDiv_eq_of_cross_mul (Nat.mul_pos hb hs) (Nat.mul_pos hd hs)
    let tail := cosHornerTicks scale cSq dSq terms (i + 1)
    calc
      tail * aSq * (dSq * cosStep i) = tail * (aSq * dSq) * cosStep i := by ac_rfl
      _ = tail * (cSq * bSq) * cosStep i := by rw [h]
      _ = tail * cSq * (bSq * cosStep i) := by ac_rfl

/-- The cosine enclosure produces the same integer ticks for equal input quotients. -/
theorem fixedCosBounds_eq_of_div_eq (a : ℤ) (b : ℕ) (c : ℤ) (d : ℕ)
    (hb : 0 < b) (hd : 0 < d) (h : (a : ℝ) / b = (c : ℝ) / d) :
    fixedCosBounds a b = fixedCosBounds c d := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hAbs := congrArg (abs : ℝ → ℝ) ((div_eq_div_iff hb'.ne' hd'.ne').mp h)
  have hCross : a.natAbs * d = c.natAbs * b := by
    simp only [abs_mul, abs_of_pos hd', abs_of_pos hb', ← Int.cast_abs, ← Int.natCast_natAbs,
      Int.cast_natCast] at hAbs
    exact_mod_cast hAbs
  have hSq : a.natAbs ^ 2 * d ^ 2 = c.natAbs ^ 2 * b ^ 2 := by
    rw [← mul_pow, ← mul_pow, hCross]
  have hTicks := cosHornerTicks_eq_of_cross_mul fixedCosScale (a.natAbs ^ 2) (b ^ 2)
    (c.natAbs ^ 2) (d ^ 2) (pow_pos hb _) (pow_pos hd _) hSq 9 0
  simp only [fixedCosBounds, hTicks]

/-- The fixed-denominator phase preserves the endpoints for the original reduced fraction. -/
theorem dottieAngleTicks_fixedCosBounds (n : ℕ) :
    fixedCosBounds (dottieAngleNumerator n) dottieAngleDenominator =
      fixedCosBounds (dottieNormAngleQuarter n).num (dottieNormAngleQuarter n).den := by
  apply fixedCosBounds_eq_of_div_eq _ _ _ _ dottieAngleDenominator_pos
    (dottieNormAngleQuarter n).den_pos
  rw [dottieAngleTicks_eq_quarter, Rat.cast_def]

#print axioms fixedCosBounds_eq_of_div_eq
#print axioms dottieAngleTicks_fixedCosBounds

end QuarticModel
