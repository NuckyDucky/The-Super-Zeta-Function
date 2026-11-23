import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! An all-height Gamma bound for the line shifted by seven in the Dottie contour. -/

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace QuarticModel

/-- The Gamma modulus on the half line follows from reflection and conjugation. -/
theorem dottie_norm_Gamma_half_sq (v : ℝ) :
    ‖Gamma (1 / 2 + (v : ℂ) * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * v) := by
  let z : ℂ := 1 / 2 + (v : ℂ) * I
  have hc : 1 - z = conj z := by
    apply Complex.ext <;> norm_num [z, Complex.mul_re, Complex.mul_im]
  have hs : sin ((Real.pi : ℂ) * z) = (Real.cosh (Real.pi * v) : ℂ) := by
    rw [show (Real.pi : ℂ) * z = ((Real.pi * v : ℝ) : ℂ) * I + Real.pi / 2 by
      dsimp only [z]
      push_cast
      ring, Complex.sin_add_pi_div_two, Complex.cos_mul_I, Complex.ofReal_cosh]
  have h := congrArg norm (Gamma_mul_Gamma_one_sub z)
  rw [hc, Gamma_conj, norm_mul, norm_conj, norm_div, hs,
    Complex.norm_of_nonneg Real.pi_pos.le, Complex.norm_of_nonneg (Real.cosh_pos _).le] at h
  simpa only [pow_two, z] using h

private theorem norm_Gamma_half_le (v : ℝ) :
    ‖Gamma (1 / 2 + (v : ℂ) * I)‖ ≤ 3 * Real.exp (-(Real.pi / 2 * |v|)) := by
  have hc : Real.exp (Real.pi * |v|) / 2 ≤ Real.cosh (Real.pi * v) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    linarith only [Real.exp_nonneg (-(Real.pi * |v|))]
  have he : Real.exp (Real.pi / 2 * |v|) ^ 2 = Real.exp (Real.pi * |v|) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsq : (‖Gamma (1 / 2 + (v : ℂ) * I)‖ * Real.exp (Real.pi / 2 * |v|)) ^ 2 ≤ 3 ^ 2 := by
    rw [mul_pow, dottie_norm_Gamma_half_sq, he, div_mul_eq_mul_div,
      div_le_iff₀ (Real.cosh_pos _)]
    nlinarith only [hc, Real.pi_lt_four, Real.exp_nonneg (Real.pi * |v|),
      mul_nonneg (sub_nonneg.mpr hc) (show (0 : ℝ) ≤ 9 by norm_num),
      mul_nonneg (show 0 ≤ 9/2 - Real.pi by linarith [Real.pi_lt_four])
        (Real.exp_nonneg (Real.pi * |v|))]
  have hp := (pow_le_pow_iff_left₀ (by positivity : 0 ≤
    ‖Gamma (1 / 2 + (v : ℂ) * I)‖ * Real.exp (Real.pi / 2 * |v|))
    (by norm_num : (0 : ℝ) ≤ 3) (by decide : (2 : ℕ) ≠ 0)).mp hsq
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).2 hp

private theorem norm_betaIntegral_le_real (z : ℂ) (d : ℝ) :
    ‖betaIntegral z (d : ℂ)‖ ≤ ‖betaIntegral (z.re : ℂ) (d : ℂ)‖ := by
  simp only [betaIntegral, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_Ioc_eq_integral_Ioo]
  let f (x : ℝ) : ℂ := (x : ℂ) ^ (z - 1) * (1 - (x : ℂ)) ^ ((d : ℂ) - 1)
  let g (x : ℝ) : ℝ := x ^ (z.re - 1) * (1 - x) ^ (d - 1)
  change ‖∫ x in Ioo (0 : ℝ) 1, f x‖ ≤ _
  have hreal :
      (∫ x in Ioo (0 : ℝ) 1, (x : ℂ) ^ ((z.re : ℂ) - 1) *
        (1 - (x : ℂ)) ^ ((d : ℂ) - 1)) = Complex.ofReal (∫ x in Ioo (0 : ℝ) 1, g x) := by
    calc
      _ = ∫ x in Ioo (0 : ℝ) 1, (g x : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
        simp only [g, ofReal_mul, ofReal_cpow hx.1.le, ofReal_cpow (sub_nonneg.mpr hx.2.le),
          ofReal_sub, ofReal_one]
      _ = _ := integral_complex_ofReal
  rw [hreal, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ∫ x in Ioo (0 : ℝ) 1, ‖f x‖ := norm_integral_le_integral_norm _
    _ = ∫ x in Ioo (0 : ℝ) 1, g x := by
      refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      dsimp only [f]
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx.1,
        show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by simp,
        norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx.2)]
      simp only [g, Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    _ ≤ _ := le_abs_self _

private theorem norm_gamma_mul_le {z : ℂ} (hz : 0 < z.re) {d : ℝ} (hd : 0 < d) :
    ‖Gamma z‖ * Real.Gamma (z.re + d) ≤ Real.Gamma z.re * ‖Gamma (z + (d : ℂ))‖ := by
  have hΓd := Real.Gamma_pos_of_pos hd
  have hΓs := Real.Gamma_pos_of_pos hz
  have hΓsum := Real.Gamma_pos_of_pos (add_pos hz hd)
  have hdre : 0 < (d : ℂ).re := by simpa using hd
  have hComplex := congrArg norm (Gamma_mul_Gamma_eq_betaIntegral hz hdre)
  have hReal := congrArg norm (Gamma_mul_Gamma_eq_betaIntegral
    (s := (z.re : ℂ)) (by simpa using hz) hdre)
  simp only [norm_mul, Gamma_ofReal, Complex.norm_of_nonneg hΓd.le] at hComplex
  simp only [norm_mul, ← ofReal_add, Gamma_ofReal,
    Complex.norm_of_nonneg hΓd.le, Complex.norm_of_nonneg hΓs.le,
    Complex.norm_of_nonneg hΓsum.le] at hReal
  apply (mul_le_mul_iff_left₀ hΓd).mp
  calc
    (‖Gamma z‖ * Real.Gamma (z.re + d)) * Real.Gamma d =
        (‖Gamma z‖ * Real.Gamma d) * Real.Gamma (z.re + d) := by ring
    _ = (‖Gamma (z + (d : ℂ))‖ * ‖betaIntegral z (d : ℂ)‖) * Real.Gamma (z.re + d) := by
        rw [hComplex]
    _ ≤ (‖Gamma (z + (d : ℂ))‖ * ‖betaIntegral (z.re : ℂ) (d : ℂ)‖) *
        Real.Gamma (z.re + d) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (norm_betaIntegral_le_real z d) (norm_nonneg _)) hΓsum.le
    _ = ‖Gamma (z + (d : ℂ))‖ *
        (Real.Gamma (z.re + d) * ‖betaIntegral (z.re : ℂ) (d : ℂ)‖) := by ring
    _ = _ := by rw [← hReal]; ring

private theorem gamma_le_three {σ : ℝ} (hlo : (1 / 3 : ℝ) ≤ σ) (hhi : σ ≤ 1) :
    Real.Gamma σ ≤ 3 := by
  have hσ : 0 < σ := by linarith
  have hΓ : Real.Gamma (σ + 1) ≤ 1 := by
    have h := Real.convexOn_Gamma.le_max_of_mem_Icc
      (by norm_num [mem_Ioi] : (1 : ℝ) ∈ Ioi 0) (by norm_num [mem_Ioi] : (2 : ℝ) ∈ Ioi 0)
      (show σ + 1 ∈ Icc 1 2 from ⟨by linarith, by linarith⟩)
    simpa only [Real.Gamma_one, Real.Gamma_two, max_self] using h
  rw [Real.Gamma_add_one hσ.ne'] at hΓ
  linarith only [hΓ, mul_le_mul_of_nonneg_right hlo (Real.Gamma_pos_of_pos hσ).le]

private theorem half_le_gamma_three_halves : (1 / 2 : ℝ) ≤ Real.Gamma (3 / 2) := by
  have h := Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi)
  rw [Real.sqrt_one] at h
  rw [show (3 / 2 : ℝ) = 1/2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
  linarith

private theorem norm_real_add_imag_le (a b : ℝ) :
    ‖(a : ℂ) + (b : ℂ) * I‖ ≤ |a| + |b| := by
  simpa only [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] using
    norm_add_le (a : ℂ) ((b : ℂ) * I)

private theorem norm_gamma_add_nat_le (z : ℂ) (hz : 0 < z.re) (R : ℝ) (m : ℕ)
    (hR : ‖z‖ + (m : ℝ) ≤ R) : ‖Gamma (z + (m : ℂ))‖ ≤ R^m * ‖Gamma z‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hmR : ‖z‖ + (m : ℝ) ≤ R := by
      rw [Nat.cast_succ] at hR
      linarith
    have hm : ‖z + (m : ℂ)‖ ≤ R := (norm_add_le z (m : ℂ)).trans (by
      rwa [Complex.norm_natCast])
    have hpos : 0 < (z + (m : ℂ)).re := by
      simpa only [add_re, natCast_re] using add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg m)
    have hne : z + (m : ℂ) ≠ 0 := fun h => by simp [h] at hpos
    have hR₀ : 0 ≤ R := (norm_nonneg _).trans hm
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one _ hne, norm_mul, pow_succ]
    calc
      _ ≤ R * (R^m * ‖Gamma z‖) := mul_le_mul hm (ih hmR) (norm_nonneg _) hR₀
      _ = _ := by ring

/-- The all-height bound also covers a neighborhood of the Dottie strip. -/
theorem norm_Gamma_add_seven_le {σ : ℝ} (hlo : (1 / 3 : ℝ) ≤ σ) (hhi : σ ≤ 1) (v : ℝ) :
    ‖Gamma ((σ : ℂ) + 7 + (v : ℂ) * I)‖ ≤
      18 * (8 + |v|)^8 * Real.exp (-(Real.pi / 2 * |v|)) := by
  let z : ℂ := (σ : ℂ) + (v : ℂ) * I
  let q : ℂ := 1/2 + (v : ℂ) * I
  let R : ℝ := 8 + |v|
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hzre : z.re = σ := by simp [z, Complex.mul_re]
  have hzpos : 0 < z.re := by rw [hzre]; linarith
  have hqpos : 0 < q.re := by norm_num [q, Complex.mul_re, Complex.div_ofNat_re]
  have hmatch : z + ((3/2 - σ : ℝ) : ℂ) = q + 1 := by
    dsimp only [z, q]
    push_cast
    ring
  have hcomp : ‖Gamma z‖ ≤ 6 * ‖Gamma (q + 1)‖ := by
    have Hb := norm_gamma_mul_le hzpos (d := 3/2 - σ) (by linarith)
    rw [hzre, show σ + (3/2 - σ) = (3/2 : ℝ) by ring, hmatch] at Hb
    linarith only [Hb, mul_le_mul_of_nonneg_left half_le_gamma_three_halves (norm_nonneg (Gamma z)),
      mul_le_mul_of_nonneg_right (gamma_le_three hlo hhi) (norm_nonneg (Gamma (q + 1)))]
  have hzshift : ‖Gamma (z + 7)‖ ≤ R^7 * ‖Gamma z‖ := by
    have h := norm_real_add_imag_le σ v
    rw [abs_of_nonneg (by linarith : 0 ≤ σ)] at h
    exact norm_gamma_add_nat_le z hzpos R 7 (by dsimp only [R, z]; push_cast; linarith)
  have hqshift : ‖Gamma (q + 1)‖ ≤ R * ‖Gamma q‖ := by
    have h : ‖q‖ ≤ 1/2 + |v| := by
      simpa [q, ofReal_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)] using
        norm_real_add_imag_le (1/2) v
    simpa using norm_gamma_add_nat_le q hqpos R 1 (by dsimp only [R]; push_cast; linarith)
  rw [show (σ : ℂ) + 7 + (v : ℂ) * I = z + 7 by dsimp [z]; ring]
  calc
    _ ≤ R^7 * ‖Gamma z‖ := hzshift
    _ ≤ R^7 * (6 * ‖Gamma (q + 1)‖) := mul_le_mul_of_nonneg_left hcomp (pow_nonneg hR _)
    _ ≤ R^7 * (6 * (R * ‖Gamma q‖)) := by gcongr
    _ ≤ R^7 * (6 * (R * (3 * Real.exp (-(Real.pi / 2 * |v|))))) := by
      gcongr
      exact norm_Gamma_half_le v
    _ = _ := by dsimp only [R]; ring

/-- The shifted Dottie strip has Gamma decay for every real ordinate. -/
theorem dottie_norm_Gamma_seven_le {σ : ℝ} (hlo : 1/2 - 63/2048 ≤ σ)
    (hhi : σ ≤ 1/2 + 63/2048) (v : ℝ) :
    ‖Gamma ((σ : ℂ) + 7 + (v : ℂ) * I)‖ ≤
      18 * (8 + |v|)^8 * Real.exp (-(Real.pi / 2 * |v|)) :=
  norm_Gamma_add_seven_le (by linarith) (by linarith) v

/-- A Gamma lower bound for the normalization at the reference height. -/
theorem dottie_exp_neg_le_norm_Gamma_two (v : ℝ) :
    Real.exp (-(Real.pi / 2 * |v|)) ≤ ‖Gamma (2 + (v : ℂ) * I)‖ := by
  let q : ℂ := 1/2 + (v : ℂ) * I
  have hqre : q.re = 1/2 := by norm_num [q, Complex.mul_re, Complex.div_ofNat_re]
  have hqpos : 0 < q.re := by rw [hqre]; norm_num
  have hΓ : ‖Gamma q‖ ≤ Real.sqrt Real.pi * ‖Gamma (2 + (v : ℂ) * I)‖ := by
    have h := norm_gamma_mul_le hqpos (d := 3/2) (by norm_num)
    have he : q + ((3/2 : ℝ) : ℂ) = 2 + (v : ℂ) * I := by
      dsimp only [q]
      push_cast
      ring
    simpa only [hqre, he, show (1/2 + 3/2 : ℝ) = 2 by norm_num, Real.Gamma_two, mul_one,
      Real.Gamma_one_half_eq] using h
  have hCosh : Real.cosh (Real.pi * v) ≤ Real.exp (Real.pi * |v|) := by
    rw [← Real.cosh_abs, abs_mul, abs_of_pos Real.pi_pos, Real.cosh_eq]
    have hexp : Real.exp (-(Real.pi * |v|)) ≤ Real.exp (Real.pi * |v|) := by
      apply Real.exp_le_exp.mpr
      have h := mul_nonneg Real.pi_pos.le (abs_nonneg v)
      linarith
    linarith only [hexp]
  have hhalf : Real.sqrt Real.pi * Real.exp (-(Real.pi / 2 * |v|)) ≤ ‖Gamma q‖ := by
    apply (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) (by decide : (2 : ℕ) ≠ 0)).mp
    calc
      _ = Real.pi / Real.exp (Real.pi * |v|) := by
        rw [mul_pow, Real.sq_sqrt Real.pi_pos.le, ← Real.exp_nat_mul,
          show ((2 : ℕ) : ℝ) * -(Real.pi / 2 * |v|) = -(Real.pi * |v|) by push_cast; ring,
          Real.exp_neg, div_eq_mul_inv]
      _ ≤ Real.pi / Real.cosh (Real.pi * v) :=
        div_le_div_of_nonneg_left Real.pi_pos.le (Real.cosh_pos _) hCosh
      _ = _ := (dottie_norm_Gamma_half_sq v).symm
  exact (mul_le_mul_iff_right₀ (Real.sqrt_pos.2 Real.pi_pos)).mp (hhalf.trans hΓ)

#print axioms dottie_norm_Gamma_half_sq
#print axioms norm_Gamma_add_seven_le
#print axioms dottie_norm_Gamma_seven_le
#print axioms dottie_exp_neg_le_norm_Gamma_two

end QuarticModel
