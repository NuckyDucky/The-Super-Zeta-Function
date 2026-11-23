import ArchivedDottieHeight
import DottieHighGammaTail
import Mathlib.Analysis.Complex.ExponentialBounds

/-! An integrable bound on the exterior of the original right contour. -/

namespace QuarticModel

open Complex Set SuperZeta.StirlingCorrection
open private norm_gamma_mul_le norm_Gamma_half_le half_le_gamma_three_halves
  norm_real_add_imag_le norm_gamma_add_nat_le from DottieHighGammaTail

private theorem norm_Gamma_one_shift_le {σ : ℝ} (hσ₀ : 0 ≤ σ) (hσ₁ : σ ≤ 1) (v : ℝ) :
    ‖Gamma (⟨σ+1,v⟩ : ℂ)‖ ≤ 6*(3+|v|)^2*Real.exp (-(Real.pi/2*|v|)) := by
  let z : ℂ := (σ : ℂ)+1+(v : ℂ)*I
  let q : ℂ := 1/2+(v : ℂ)*I
  have hz_re : z.re = σ+1 := by simp [z, Complex.mul_re]
  have hz_pos : 0 < z.re := by rw [hz_re]; linarith only [hσ₀]
  have hq_pos : 0 < q.re := by norm_num [q, Complex.mul_re, Complex.div_ofNat_re]
  have hGamma_one : Real.Gamma (σ+1) ≤ 1 := by
    have h := Real.convexOn_Gamma.le_max_of_mem_Icc
      (by norm_num [mem_Ioi] : (1 : ℝ) ∈ Ioi 0) (by norm_num [mem_Ioi] : (2 : ℝ) ∈ Ioi 0)
      (show σ+1 ∈ Icc 1 2 from ⟨by linarith only [hσ₀], by linarith only [hσ₁]⟩)
    simpa only [Real.Gamma_one, Real.Gamma_two, max_self] using h
  have hGamma_half : (1/2 : ℝ) ≤ Real.Gamma (5/2) := by
    rw [show (5/2 : ℝ) = (3/2 : ℝ)+1 by norm_num,
      Real.Gamma_add_one (by norm_num : (3/2 : ℝ) ≠ 0)]
    linarith only [half_le_gamma_three_halves]
  have hmatch : z + ((3/2-σ : ℝ) : ℂ) = q+2 := by
    dsimp only [z, q]
    push_cast
    ring
  have hcomp : ‖Gamma z‖ ≤ 2*‖Gamma (q+2)‖ := by
    have hb := norm_gamma_mul_le hz_pos (d := 3/2-σ) (by linarith only [hσ₁])
    rw [hz_re, show σ+1+(3/2-σ) = (5/2 : ℝ) by ring, hmatch] at hb
    linarith only [hb, mul_le_mul_of_nonneg_left hGamma_half (norm_nonneg (Gamma z)),
      mul_le_mul_of_nonneg_right hGamma_one (norm_nonneg (Gamma (q+2)))]
  have hq_norm : ‖q‖ ≤ 1/2+|v| := by
    simpa [q, ofReal_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)] using
      norm_real_add_imag_le (1/2) v
  have hshift : ‖Gamma (q+2)‖ ≤ (3+|v|)^2*‖Gamma q‖ := by
    exact norm_gamma_add_nat_le q hq_pos (3+|v|) 2 (by push_cast; linarith only [hq_norm])
  have hz_eq : (⟨σ+1,v⟩ : ℂ) = z := by
    apply Complex.ext <;> simp [z, Complex.mul_re, Complex.mul_im]
  rw [hz_eq]
  calc
    _ ≤ 2*‖Gamma (q+2)‖ := hcomp
    _ ≤ 2*((3+|v|)^2*‖Gamma q‖) := mul_le_mul_of_nonneg_left hshift (by norm_num)
    _ ≤ 2*((3+|v|)^2*(3*Real.exp (-(Real.pi/2*|v|)))) := by
      gcongr
      exact norm_Gamma_half_le v
    _ = _ := by ring

private theorem exterior_quadratic_gauss_le {u : ℝ} (hu : 20 ≤ |u|) :
    (1+|u|)^2*Real.exp (-u^2) ≤ Real.exp (-300)*Real.exp (-(1/8 : ℝ)*u^2) := by
  have hlin : 2*|u| ≤ (1/10 : ℝ)*u^2 := by
    have h := mul_le_mul_of_nonneg_right hu (abs_nonneg u)
    nlinarith only [h, sq_abs u]
  have hsq : (400 : ℝ) ≤ u^2 := by
    simpa only [sq_abs, show (20 : ℝ)^2 = 400 by norm_num] using
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 20) hu 2
  have hpow : (1+|u|)^2 ≤ (Real.exp |u|)^2 := by
    apply pow_le_pow_left₀ (by positivity) _ 2
    simpa only [add_comm] using Real.add_one_le_exp |u|
  calc
    _ ≤ (Real.exp |u|)^2*Real.exp (-u^2) := mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = Real.exp (2*|u|-u^2) := by
      norm_num [← Real.exp_nat_mul, ← Real.exp_add, sub_eq_add_neg]
    _ ≤ Real.exp (-300+(-(1/8 : ℝ)*u^2)) := Real.exp_le_exp.mpr (by linarith only [hlin,hsq])
    _ = _ := Real.exp_add _ _

private theorem exp_neg_three_hundred_le : Real.exp (-300) ≤ 1/10^127 := by
  have hpow : (10 : ℕ)^127 * 3^300 ≤ 8^300 := by decide +kernel
  have h : (10 : ℝ)^127 ≤ Real.exp 300 := by
    calc
      _ ≤ (8/3 : ℝ)^(300 : ℕ) := by
        rw [div_pow, le_div_iff₀ (by positivity)]
        exact_mod_cast hpow
      _ ≤ (Real.exp 1)^(300 : ℕ) := pow_le_pow_left₀ (by norm_num)
        (by linarith only [Real.exp_one_gt_d9]) 300
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) h

/-- On the two original right-contour tails, the Gamma factor and tilt are bounded by
a Gaussian with a rational prefactor in the original reference normalization. -/
theorem dottie_lower_right_tail_gamma_envelope {σ t u : ℝ}
    (hσ : σ ∈ Icc (1/2-63/2048 : ℝ) (1/2+63/2048))
    (ht : |t-dottieHeight| ≤ 35/2048) (hu : 20 ≤ |u|) :
    ‖Gamma (⟨σ+1,t+u⟩ : ℂ)‖ * Real.exp (Real.pi*u/2-u^2) /
      ‖Gamma (2+(dottieHeight : ℂ)*I)‖ ≤
        (2/10^100 : ℝ)*Real.exp (-(1/8 : ℝ)*u^2) := by
  let T := dottieHeight
  let G := ‖Gamma (2+(T : ℂ)*I)‖
  have hT : 0 < T := by dsimp only [T]; linarith only [dottieHeight_enclosure.1]
  have hden : Real.exp (-(Real.pi/2*T)) ≤ G := by
    simpa only [abs_of_pos hT] using dottie_exp_neg_le_norm_Gamma_two T
  have hden_pos : 0 < G := (Real.exp_pos _).trans_le hden
  have hσ₀ : 0 ≤ σ := by linarith only [hσ.1]
  have hσ₁ : σ ≤ 1 := by linarith only [hσ.2]
  have hgap : T+u-|t+u| ≤ 35/2048 := by linarith only [(abs_le.mp ht).1, le_abs_self (t+u)]
  have htilt : Real.exp (-(Real.pi/2*|t+u|))*Real.exp (Real.pi*u/2-u^2) ≤
      (3*Real.exp (-u^2))*G := by
    rw [← Real.exp_add]
    have hpi : Real.pi/2*(35/2048) ≤ 1 := by linarith only [Real.pi_lt_four]
    have hgap' := mul_le_mul_of_nonneg_left hgap (show 0 ≤ Real.pi/2 by positivity)
    calc
      _ ≤ Real.exp (-(Real.pi/2*T)+(1-u^2)) :=
        Real.exp_le_exp.mpr (by nlinarith only [hgap',hpi])
      _ = (Real.exp 1*Real.exp (-u^2))*Real.exp (-(Real.pi/2*T)) := by
        rw [sub_eq_add_neg (1 : ℝ) (u^2), Real.exp_add, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le
        (Real.exp_pos _).le) hden (Real.exp_pos _).le (by positivity)
  have hnormalized : ‖Gamma (⟨σ+1,t+u⟩ : ℂ)‖*Real.exp (Real.pi*u/2-u^2)/G ≤
      18*(3+|t+u|)^2*Real.exp (-u^2) := by
    apply (div_le_iff₀ hden_pos).2
    calc
      _ ≤ (6*(3+|t+u|)^2*Real.exp (-(Real.pi/2*|t+u|)))*Real.exp (Real.pi*u/2-u^2) :=
        mul_le_mul_of_nonneg_right (norm_Gamma_one_shift_le hσ₀ hσ₁ (t+u)) (Real.exp_pos _).le
      _ = (6*(3+|t+u|)^2)*(Real.exp (-(Real.pi/2*|t+u|))*Real.exp (Real.pi*u/2-u^2)) := by ring
      _ ≤ (6*(3+|t+u|)^2)*((3*Real.exp (-u^2))*G) :=
        mul_le_mul_of_nonneg_left htilt (by positivity)
      _ = _ := by ring
  have ht_abs : |t| ≤ (10^13 : ℝ)-3 := by
    rw [abs_le]
    constructor
    · linarith only [dottieHeight_enclosure.1, (abs_le.mp ht).1]
    · linarith only [dottieHeight_enclosure.2, (abs_le.mp ht).2]
  have hpoly : 3+|t+u| ≤ (10^13 : ℝ)*(1+|u|) := by
    linarith only [ht_abs, abs_add_le t u, abs_nonneg u]
  have hpow : (3+|t+u|)^2 ≤ (10^26 : ℝ)*(1+|u|)^2 := by
    calc
      _ ≤ ((10^13 : ℝ)*(1+|u|))^2 := pow_le_pow_left₀ (by positivity) hpoly 2
      _ = _ := by rw [mul_pow]; norm_num
  calc
    _ ≤ 18*(3+|t+u|)^2*Real.exp (-u^2) := hnormalized
    _ ≤ 18*((10^26 : ℝ)*(1+|u|)^2)*Real.exp (-u^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) (Real.exp_pos _).le
    _ = (18*10^26 : ℝ)*((1+|u|)^2*Real.exp (-u^2)) := by ring
    _ ≤ (18*10^26 : ℝ)*(Real.exp (-300)*Real.exp (-(1/8 : ℝ)*u^2)) :=
      mul_le_mul_of_nonneg_left (exterior_quadratic_gauss_le hu) (by positivity)
    _ = ((18*10^26 : ℝ)*Real.exp (-300))*Real.exp (-(1/8 : ℝ)*u^2) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact (mul_le_mul_of_nonneg_left exp_neg_three_hundred_le (by positivity)).trans (by norm_num)

#print axioms dottie_lower_right_tail_gamma_envelope

end QuarticModel
