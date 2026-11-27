import DottieDarkPhase

/-! Exact magnitude and phase formulas for the first overflow-prone
updates. The logarithmic form never constructs the large second phase. -/

noncomputable section

namespace SuperZeta.Reciprocal

open Complex Filter
open scoped Topology

/-- The real factor that decides the sign of the third logarithmic modulus. -/
def thirdPhaseFactor (L : ℂ) : ℝ :=
  L.re * Real.cos (-L*exp L).im - L.im * Real.sin (-L*exp L).im

theorem cap_second_log_modulus_eq (L : ℂ) :
    Real.log ‖(capOrbit L 2).2‖ = (-L*exp L).re := by
  simp only [capOrbit, step, mul_one, Complex.norm_exp, Real.log_exp]

theorem cap_third_log_modulus_eq (L : ℂ) :
    Real.log ‖(capOrbit L 3).1‖ =
      Real.exp (-L*exp L).re * thirdPhaseFactor L := by
  simp only [capOrbit, step, mul_one, Complex.norm_exp, Real.log_exp, thirdPhaseFactor]
  have h (z : ℂ) : (L * exp z).re =
      Real.exp z.re * (L.re * Real.cos z.im - L.im * Real.sin z.im) := by
    rw [Complex.mul_re, Complex.exp_re, Complex.exp_im]
    ring
  exact h (-L*exp L)

/-- Taking the log of the nonzero absolute log modulus leaves a sum of
finite-size real expressions. The factor retains the sign separately. -/
theorem cap_third_log_abs_log_modulus_eq (L : ℂ) (hf : thirdPhaseFactor L ≠ 0) :
    Real.log |Real.log ‖(capOrbit L 3).1‖| =
      (-L*exp L).re + Real.log |thirdPhaseFactor L| := by
  rw [cap_third_log_modulus_eq, abs_mul, abs_of_pos (Real.exp_pos _),
    Real.log_mul (Real.exp_ne_zero _) (abs_ne_zero.mpr hf), Real.log_exp]

private theorem log_bounds_in_range {n : ℕ} (hl : 4096 ≤ n) (hu : n ≤ 131072) :
    8 ≤ Real.log (n : ℝ) ∧ Real.log (n : ℝ) ≤ 12 := by
  have hLo : 8 ≤ Real.log (4096 : ℝ) := by
    rw [show (4096 : ℝ) = (2:ℝ)^12 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_gt_d9]
  have hHi : Real.log (131072 : ℝ) ≤ 12 := by
    rw [show (131072 : ℝ) = (2:ℝ)^17 by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  exact ⟨hLo.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hl)),
    (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast hu)).trans hHi⟩

private theorem log_nat_lift_norm {n : ℕ} (hx : 8 ≤ Real.log (n : ℝ))
    (hX : Real.log (n : ℝ) ≤ 12) : ‖logNatAddPiI n‖ ≤ 16 := by
  calc
    ‖logNatAddPiI n‖ ≤ ‖(Real.log (n : ℝ) : ℂ)‖ + ‖(Real.pi : ℂ)*I‖ := norm_add_le _ _
    _ ≤ 16 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ Real.log (n : ℝ)),
        norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
      linarith [Real.pi_lt_d2]

/-- All even integers in this range give explicit dark points whose
exact cap orbits converge to fixed pairs after crossing the range limit. -/
theorem cap_tendsto_fixed_overflow_at_even_range {n : ℕ}
    (hl : 4096 ≤ n) (hu : n ≤ 131072) (he : Even n) :
    710 < Real.log ‖(capOrbit (logNatAddPiI n) 2).2‖ ∧
    ∃ p : ℂ × ℂ, step (logNatAddPiI n) p = p ∧
      Tendsto (capOrbit (logNatAddPiI n)) atTop (𝓝 p) := by
  obtain ⟨hx, hX⟩ := log_bounds_in_range hl hu
  have hn : 0 < n := by omega
  refine ⟨?_, cap_tendsto_fixed_at_even_logNatAddPiI hn he hx (log_nat_lift_norm hx hX)⟩
  rw [cap_second_log_modulus_logNatAddPiI hn]
  exact (by norm_num : (710:ℝ) < 4096*8).trans_le
    (mul_le_mul (by exact_mod_cast hl) hx (by norm_num) (by positivity))

/-- The same range on odd lifts has a nearly vanishing third first phase
and a fourth second phase close to the cap. -/
theorem cap_odd_range_fourth_phase_near_one {n : ℕ}
    (hl : 4096 ≤ n) (hu : n ≤ 131072) (ho : Odd n) :
    ‖(capOrbit (logNatAddPiI n) 3).1‖ ≤ 1/1000 ∧
    ‖(capOrbit (logNatAddPiI n) 4).2-1‖ ≤ 1/20 := by
  obtain ⟨hx, hX⟩ := log_bounds_in_range hl hu
  have hn : 0 < n := by omega
  have hpow : (1:ℝ) ≤ (n:ℝ)^n := one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))
  have hx0 : 0 ≤ Real.log (n : ℝ) := by linarith
  have hlog : Real.log ‖(capOrbit (logNatAddPiI n) 3).1‖ ≤ -8 := by
    rw [cap_third_log_modulus_logNatAddPiI hn, ho.neg_one_pow, neg_one_mul, neg_mul]
    exact neg_le_neg (hx.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hx0))
  have hpos : 0 < ‖(capOrbit (logNatAddPiI n) 3).1‖ := by
    change 0 < ‖exp (logNatAddPiI n * (capOrbit (logNatAddPiI n) 2).2)‖
    exact norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hsmall : ‖(capOrbit (logNatAddPiI n) 3).1‖ ≤ 1/1000 := by
    rw [← Real.exp_log hpos]
    exact (Real.exp_le_exp.mpr (hlog.trans (by norm_num))).trans exp_neg_seven_lt.le
  refine ⟨hsmall, ?_⟩
  change ‖exp (-(logNatAddPiI n) * (capOrbit (logNatAddPiI n) 3).1)-1‖ ≤ 1/20
  exact pos_phase_near_one (by simpa only [norm_neg] using log_nat_lift_norm hx hX) hsmall

#print axioms cap_second_log_modulus_eq
#print axioms cap_third_log_modulus_eq
#print axioms cap_third_log_abs_log_modulus_eq
#print axioms cap_tendsto_fixed_overflow_at_even_range
#print axioms cap_odd_range_fourth_phase_near_one

end SuperZeta.Reciprocal
