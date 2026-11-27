import DedekindRationalCalibration
import DedekindMixedThetaRegularPartBound
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

namespace FieldTarget

open Complex Set NumberField
open DedekindZetaZeroFree.AbelianQuotient

private theorem eulerMascheroni_lt_582 : Real.eulerMascheroniConstant < 582 / 1000 := by
  have hsumQ : harmonic 128 < (54332 / 10000 : ℚ) := by decide +kernel
  have hsum' : (harmonic 128 : ℝ) < ((54332 / 10000 : ℚ) : ℝ) := Rat.cast_lt.mpr hsumQ
  have hsum : (harmonic 128 : ℝ) < 54332 / 10000 := by simpa using hsum'
  have hlog : (48517 / 10000 : ℝ) < Real.log 128 := by
    rw [show (128 : ℝ) = 2 ^ (7 : ℕ) by norm_num, Real.log_pow]
    linarith [Real.log_two_gt_d9]
  have hg := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 128
  have hn : (128 : ℕ) ≠ 0 := by decide
  simp only [Real.eulerMascheroniSeq', hn, ite_false, Nat.cast_ofNat] at hg
  linarith

private theorem log_four_pi_gt_253 : (253 / 100 : ℝ) < Real.log (4 * Real.pi) := by
  apply (Real.lt_log_iff_exp_lt (by positivity)).2
  have h1 : Real.exp 1 ≤ 27183 / 10000 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have h53 : Real.exp (53 / 100) ≤ 16997 / 10000 := by
    have h := Real.exp_bound' (x := 53 / 100) (by norm_num) (by norm_num) (n := 4) (by decide)
    exact h.trans (by norm_num [Finset.sum_range_succ, Nat.factorial])
  rw [show (253 / 100 : ℝ) = 1 + 1 + 53 / 100 by norm_num, Real.exp_add, Real.exp_add]
  have hprod : Real.exp 1 * Real.exp 1 * Real.exp (53 / 100) ≤
      (27183 / 10000 : ℝ) ^ 2 * (16997 / 10000) := by
    rw [pow_two]
    exact mul_le_mul (mul_le_mul h1 h1 (Real.exp_pos _).le (by norm_num))
      h53 (Real.exp_pos _).le (by positivity)
  have hcalc : (27183 / 10000 : ℝ) ^ 2 * (16997 / 10000) < 4 * 3.14 := by norm_num
  exact hprod.trans_lt (hcalc.trans (by linarith [Real.pi_gt_d2]))

/-- Closed form for the value in the mixed-theta band criterion over the rational field. -/
theorem rat_mixedTheta_regular_part_at_one :
    ((Theta.mixedThetaPair ℚ).Λ₀ 1).re =
      (Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 2 + 1 := by
  rw [rat_mixedTheta_regular_part_and_constant.1, completedRiemannZeta₀_one]
  have hlog : Complex.log (4 * (Real.pi : ℂ)) = (Real.log (4 * Real.pi) : ℂ) := by
    simpa using (Complex.ofReal_log (show 0 ≤ (4 : ℝ) * Real.pi by positivity)).symm
  rw [hlog]
  rw [← Complex.ofReal_sub, ← Complex.ofReal_ofNat, ← Complex.ofReal_div,
    ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.ofReal_re]

theorem rat_mixedTheta_regular_part_lt : ((Theta.mixedThetaPair ℚ).Λ₀ 1).re < 13 / 500 := by
  rw [rat_mixedTheta_regular_part_at_one]
  linarith [eulerMascheroni_lt_582, log_four_pi_gt_253]

/-- The regularized value gives a finite Dottie certificate on the entire height band. -/
theorem finite_dottie_boundary_rat_four :
    HasFiniteDottieBoundaryCertificate (mixedThetaContinuation ℚ) (mixedThetaCompletedReading ℚ)
      (-4) 4 := by
  apply finite_dottie_boundary_of_regularized_one ℚ (by norm_num)
  rw [rat_mixedTheta_regular_part_and_constant.2, norm_one]
  exact (mul_lt_mul_of_pos_left rat_mixedTheta_regular_part_lt (by norm_num : (0 : ℝ) < 2)).trans
    (by norm_num)

theorem mixedTheta_rat_band_nonzero {w : ℂ} (him : w.im ∈ Icc (-4 : ℝ) 4)
    (hre : 1/2 < w.re) (hhi : w.re ≤ 31/32) : mixedThetaContinuation ℚ w ≠ 0 :=
  dottie_band_nonzero_of_certificate (mixedThetaCompletedReading_differentiableOn ℚ)
    (fun z hlo hhi hz ↦ (mixedThetaCompletedReading_zero_iff ℚ z hlo hhi).mpr hz)
    finite_dottie_boundary_rat_four him hre hhi

#check @rat_mixedTheta_regular_part_at_one
#check @finite_dottie_boundary_rat_four
#check @mixedTheta_rat_band_nonzero
#print axioms rat_mixedTheta_regular_part_at_one
#print axioms rat_mixedTheta_regular_part_lt
#print axioms finite_dottie_boundary_rat_four
#print axioms mixedTheta_rat_band_nonzero

end FieldTarget
