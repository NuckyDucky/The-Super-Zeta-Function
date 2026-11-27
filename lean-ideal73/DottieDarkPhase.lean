import DottieOuterCapture
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Exact trajectories at parameters that exceed the atlas's arithmetic range
before its second update completes. -/

noncomputable section

namespace SuperZeta.Reciprocal

open Complex Filter
open scoped Topology

/-- A lift of the negative real integer `-n` with imaginary part `π`. -/
def logNatAddPiI (n : ℕ) : ℂ := (Real.log (n : ℝ) : ℂ) + (Real.pi : ℂ)*I

private theorem logNatAddPiI_re (n : ℕ) : (logNatAddPiI n).re = Real.log (n : ℝ) := by
  simp only [logNatAddPiI, add_re, ofReal_re, Complex.mul_re, I_re, I_im, ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero]

theorem exp_logNatAddPiI {n : ℕ} (hn : 0 < n) : exp (logNatAddPiI n) = -(n : ℂ) := by
  rw [logNatAddPiI, exp_add, ← Complex.ofReal_exp, Real.exp_log (by exact_mod_cast hn), exp_pi_mul_I]
  simp

/-- The second phase is an exact signed integer, even when its magnitude
exceeds the floating-point range. -/
theorem cap_second_phase_logNatAddPiI {n : ℕ} (hn : 0 < n) :
    (capOrbit (logNatAddPiI n) 2).2 = (-1 : ℂ)^n * (n : ℂ)^n := by
  let L := logNatAddPiI n
  change exp (-L * exp (L*1)) = _
  rw [mul_one, show exp L = -(n:ℂ) from exp_logNatAddPiI hn,
    show -L * -(n:ℂ) = (n:ℂ)*L by ring, Complex.exp_nat_mul,
    show exp L = -(n:ℂ) from exp_logNatAddPiI hn, neg_eq_neg_one_mul, mul_pow]

theorem cap_second_log_modulus_logNatAddPiI {n : ℕ} (hn : 0 < n) :
    Real.log ‖(capOrbit (logNatAddPiI n) 2).2‖ = (n : ℝ) * Real.log (n : ℝ) := by
  rw [cap_second_phase_logNatAddPiI hn, norm_mul, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_pow, Complex.norm_natCast, Real.log_pow]

/-- The sign of the third logarithmic modulus is the parity of the lift. -/
theorem cap_third_log_modulus_logNatAddPiI {n : ℕ} (hn : 0 < n) :
    Real.log ‖(capOrbit (logNatAddPiI n) 3).1‖ =
      ((-1 : ℝ)^n * (n : ℝ)^n) * Real.log (n : ℝ) := by
  let L := logNatAddPiI n
  change Real.log ‖exp (L*(capOrbit L 2).2)‖ = _
  have he : (capOrbit L 2).2 = Complex.ofReal ((-1 : ℝ)^n * (n : ℝ)^n) := by
    simpa only [ofReal_mul, ofReal_pow, ofReal_neg, ofReal_one, ofReal_natCast] using
      cap_second_phase_logNatAddPiI hn
  rw [Complex.norm_exp, Real.log_exp, he, Complex.mul_re, ofReal_re, ofReal_im,
    mul_zero, sub_zero, logNatAddPiI_re, mul_comm]

/-- At an even lift the fourth update enters the small trapping pair. -/
theorem cap_tendsto_fixed_at_even_logNatAddPiI {n : ℕ} (hn : 0 < n) (he : Even n)
    (hx : 8 ≤ Real.log (n : ℝ)) (hL : ‖logNatAddPiI n‖ ≤ 16) :
    ∃ p : ℂ × ℂ, step (logNatAddPiI n) p = p ∧
      Tendsto (capOrbit (logNatAddPiI n)) atTop (𝓝 p) := by
  let L := logNatAddPiI n
  let m := n^n
  have hre : 8 ≤ L.re := by rwa [logNatAddPiI_re]
  have hq2 : (capOrbit L 2).2 = (m : ℂ) := by
    rw [cap_second_phase_logNatAddPiI hn, he.neg_one_pow, one_mul]
    exact (Nat.cast_pow n n).symm
  have hp3 : (capOrbit L 3).1 = ((n^m : ℕ) : ℂ) := by
    change exp (L*(capOrbit L 2).2) = _
    have hem : Even m := he.pow_of_ne_zero hn.ne'
    rw [hq2, mul_comm, Complex.exp_nat_mul, show exp L = -(n:ℂ) from exp_logNatAddPiI hn,
      hem.neg_pow, Nat.cast_pow]
  have hp4 : ‖(capOrbit L 4).1-1‖ ≤ 1/20 := cap_even_first_near_one hre hL 2
  have hq4 : ‖(capOrbit L 4).2‖ ≤ 1/1000 := by
    change ‖exp (-L*(capOrbit L 3).1)‖ ≤ _
    rw [hp3, Complex.norm_exp]
    have hlarge : 1 ≤ ((n^m : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (pow_ne_zero m hn.ne')
    have hmull : 8 ≤ L.re * ((n^m : ℕ) : ℝ) := by
      simpa only [mul_one] using mul_le_mul hre hlarge (by norm_num : (0:ℝ) ≤ 1)
        (by linarith : 0 ≤ L.re)
    have hnegative : (-L*((n^m : ℕ):ℂ)).re ≤ -7 := by
      simp only [Complex.mul_re, neg_re, natCast_re, natCast_im, mul_zero, sub_zero, neg_mul]
      linarith
    exact (Real.exp_le_exp.mpr hnegative).trans exp_neg_seven_lt.le
  obtain ⟨p, hp, _, _, ht⟩ := cap_tendsto_fixed_of_box_entry hre hL hp4 hq4
  exact ⟨p, hp, ht⟩

private theorem log_4096_bounds : 8 ≤ Real.log 4096 ∧ Real.log 4096 ≤ 9 := by
  rw [show (4096 : ℝ) = (2:ℝ)^12 by norm_num, Real.log_pow]
  norm_num
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- A parameter in an overflow cell of the wider atlas converges to a fixed pair. -/
theorem cap_tendsto_fixed_overflow_4096 :
    Real.log ‖(capOrbit (logNatAddPiI 4096) 2).2‖ > 710 ∧
    ∃ p : ℂ × ℂ, step (logNatAddPiI 4096) p = p ∧
      Tendsto (capOrbit (logNatAddPiI 4096)) atTop (𝓝 p) := by
  have hx : 8 ≤ Real.log (4096 : ℝ) := log_4096_bounds.1
  constructor
  · rw [cap_second_log_modulus_logNatAddPiI (by decide : 0 < (4096:ℕ))]
    norm_num
    linarith
  apply cap_tendsto_fixed_at_even_logNatAddPiI (by decide) (by decide) (by simpa using hx)
  calc
    ‖logNatAddPiI 4096‖ ≤ ‖(Real.log (4096 : ℝ) : ℂ)‖ + ‖(Real.pi : ℂ)*I‖ :=
      norm_add_le _ _
    _ ≤ 16 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ Real.log 4096),
        norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
      linarith [log_4096_bounds.2, Real.pi_lt_d2]

/-- The neighboring odd lift also overflows at update two. At update three
its first phase has logarithmic modulus at most `-8`. -/
theorem cap_overflow_and_third_small_4097 :
    Real.log ‖(capOrbit (logNatAddPiI 4097) 2).2‖ > 710 ∧
    Real.log ‖(capOrbit (logNatAddPiI 4097) 3).1‖ ≤ -8 := by
  have hh : 8 ≤ Real.log (4097 : ℝ) :=
    log_4096_bounds.1.trans (Real.log_le_log (by norm_num) (by norm_num))
  constructor
  · rw [cap_second_log_modulus_logNatAddPiI (by decide : 0 < (4097:ℕ))]
    norm_num
    linarith
  · rw [cap_third_log_modulus_logNatAddPiI (by decide : 0 < (4097:ℕ)),
      (show Odd (4097:ℕ) by decide).neg_one_pow, neg_one_mul, neg_mul]
    change -((4097:ℝ)^4097 * Real.log 4097) ≤ -8
    have hpow : (1 : ℝ) ≤ 4097^4097 := one_le_pow₀ (by norm_num)
    have hlog : 0 ≤ Real.log (4097:ℝ) := by linarith
    refine neg_le_neg (hh.trans ?_)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hlog

#print axioms cap_second_phase_logNatAddPiI
#print axioms cap_third_log_modulus_logNatAddPiI
#print axioms cap_tendsto_fixed_overflow_4096
#print axioms cap_overflow_and_third_small_4097

end SuperZeta.Reciprocal
