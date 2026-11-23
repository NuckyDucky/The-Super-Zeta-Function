import DottieHighGammaLocal
import DottieHighGammaTail
import DottieFarScalarBound
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Keep the accurate Gamma estimate near the contour center and use a
polynomial times a Gaussian outside that segment. -/

namespace QuarticModel

open Complex MeasureTheory Set
open scoped ComplexConjugate
open SuperZeta.StirlingCorrection
open private verticalPoint from ArchivedDottieContourShift
set_option autoImplicit false

noncomputable def dottieFarGammaCore (σ : ℝ) : ℝ :=
  dottieHeight^(σ+5) * Real.exp (35*Real.pi/4096+1/10^10)

noncomputable def dottieFarGammaOuter (t : ℝ) : ℝ :=
  18*(8+|t|)^8*Real.exp (35*Real.pi/4096-100)

noncomputable def dottieFarGammaEnvelope (σ t u : ℝ) : ℝ :=
  dottieFarGammaCore σ * Real.exp (-(1 : ℝ)*u^2) +
    dottieFarGammaOuter t * Real.exp (-(1/4 : ℝ)*u^2)

theorem dottie_far_gamma_envelope_integrable (σ t : ℝ) :
    Integrable (dottieFarGammaEnvelope σ t) := by
  have h₁ := (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num)).const_mul
    (dottieFarGammaCore σ)
  have h₂ := (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1/4 by norm_num)).const_mul
    (dottieFarGammaOuter t)
  exact h₁.add h₂

theorem dottie_far_gamma_envelope_integral (σ t : ℝ) :
    (∫ u : ℝ, dottieFarGammaEnvelope σ t u) =
      dottieFarGammaCore σ * √Real.pi + dottieFarGammaOuter t * √(Real.pi/(1/4)) := by
  have h₁ := (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num)).const_mul
    (dottieFarGammaCore σ)
  have h₂ := (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1/4 by norm_num)).const_mul
    (dottieFarGammaOuter t)
  unfold dottieFarGammaEnvelope
  rw [integral_add h₁ h₂, integral_const_mul, integral_const_mul,
    integral_gaussian (1 : ℝ), integral_gaussian (1/4 : ℝ), div_one]

private theorem exterior_polynomial_gauss_le (t u : ℝ) (hu : 20 < |u|) :
    (8+|t+u|)^8 * Real.exp (-u^2) ≤
      (8+|t|)^8 * Real.exp (-100) * Real.exp (-(1/4 : ℝ)*u^2) := by
  have habs : |t+u| ≤ |t|+|u| := abs_add_le t u
  have hprod : 8+|t+u| ≤ (8+|t|)*(1+|u|) := by
    nlinarith only [habs, abs_nonneg u, mul_nonneg (abs_nonneg t) (abs_nonneg u)]
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ 8+|t+u| by positivity) hprod 8
  have hExp : (1+|u|)^8 ≤ Real.exp (8*|u|) := by
    refine (pow_le_pow_left₀ (show (0 : ℝ) ≤ 1+|u| by positivity)
      (by simpa only [add_comm] using Real.add_one_le_exp |u|) 8).trans_eq ?_
    rw [← Real.exp_nat_mul]
    norm_num
  have hExpo : 8*|u|-u^2 ≤ -100-(1/4 : ℝ)*u^2 := by
    rw [← sq_abs u]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hu.le) (show 0 ≤ |u|+20 by positivity),
      mul_nonneg (sub_nonneg.mpr hu.le) (show 0 ≤ |u|-16 by linarith)]
  calc
    _ ≤ ((8+|t|)*(1+|u|))^8 * Real.exp (-u^2) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ ≤ _ := by
      rw [mul_pow, mul_assoc, mul_assoc, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ Real.exp (8*|u|)*Real.exp (-u^2) := mul_le_mul_of_nonneg_right hExp (Real.exp_pos _).le
        _ ≤ _ := by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith only [hExpo])

/-- The contour tilt cancels the large vertical Gamma exponential. The
outer bound absorbs a polynomial in u before integrating the Gaussian. -/
theorem dottie_far_tilted_gamma_envelope {σ t : ℝ}
    (hσ : σ ∈ Icc (1/2-63/2048) (1/2+63/2048)) (ht : |t-dottieHeight| ≤ 35/2048)
    (hden : Real.exp (-Real.pi*dottieHeight/2) ≤ ‖Gamma (2+(dottieHeight : ℂ)*I)‖)
    (houter : ∀ v : ℝ, ‖Gamma (⟨σ+7,v⟩ : ℂ)‖ ≤
      18*(8+|v|)^8*Real.exp (-Real.pi*|v|/2)) (u : ℝ) :
    ‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖ * Real.exp (-u^2+Real.pi*u/2) ≤
      ‖Gamma (2+(dottieHeight : ℂ)*I)‖ * dottieFarGammaEnvelope σ t u := by
  let G := ‖Gamma (2+(dottieHeight : ℂ)*I)‖
  have hG : 0 < G := (Real.exp_pos _).trans_le hden
  have hT : 0 ≤ dottieHeight := by linarith only [dottieHeight_enclosure.1]
  have hcore : 0 ≤ dottieFarGammaCore σ := mul_nonneg (Real.rpow_nonneg hT _) (Real.exp_pos _).le
  have hout : 0 ≤ dottieFarGammaOuter t := by unfold dottieFarGammaOuter; positivity
  rw [Real.exp_add]
  change ‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖ * (Real.exp (-u^2)*Real.exp (Real.pi*u/2)) ≤
    G*dottieFarGammaEnvelope σ t u
  by_cases hu : |u| ≤ 20
  · have hn := dottie_gamma_k7_local_tilted_norm_ratio hσ ht hu
    change (‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖/G)*Real.exp (Real.pi*u/2) ≤ dottieFarGammaCore σ at hn
    have hn' : ‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖ * Real.exp (Real.pi*u/2) ≤
        G*dottieFarGammaCore σ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hG] at hn
      simpa only [mul_comm G] using hn
    simp only [dottieFarGammaEnvelope, neg_mul, one_mul]
    rw [mul_add, ← mul_assoc, ← mul_assoc, mul_right_comm _ (Real.exp (-u^2))]
    exact (mul_le_mul_of_nonneg_right hn' (Real.exp_pos _).le).trans
      (le_add_of_nonneg_right (by positivity))
  · have hx : -Real.pi*|t+u|/2+Real.pi*u/2 ≤
      -Real.pi*dottieHeight/2+35*Real.pi/4096 := by
      have hn := mul_le_mul_of_nonneg_left (le_abs_self (t+u)) Real.pi_pos.le
      have ht0 := mul_le_mul_of_nonneg_left (abs_le.mp ht).1 Real.pi_pos.le
      nlinarith only [hn, ht0]
    have hfast :
      Real.exp (-Real.pi*|t+u|/2)*Real.exp (Real.pi*u/2) ≤
        G*Real.exp (35*Real.pi/4096) := by
      rw [← Real.exp_add]
      exact (Real.exp_le_exp.mpr hx).trans
        (by rw [Real.exp_add]; exact mul_le_mul_of_nonneg_right hden (Real.exp_pos _).le)
    have hb := exterior_polynomial_gauss_le t u (lt_of_not_ge hu)
    have hc := houter (t+u)
    simp only [dottieFarGammaEnvelope, neg_mul, one_mul]
    rw [show dottieFarGammaOuter t = 18*(8+|t|)^8*
      (Real.exp (35*Real.pi/4096)*Real.exp (-100)) by
        unfold dottieFarGammaOuter
        rw [sub_eq_add_neg, Real.exp_add]]
    have h₁ := mul_le_mul_of_nonneg_right hc
      (show 0 ≤ Real.exp (-u^2)*Real.exp (Real.pi*u/2) by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hfast
      (show 0 ≤ 18*((8+|t+u|)^8*Real.exp (-u^2)) by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hb
      (show 0 ≤ 18*(G*Real.exp (35*Real.pi/4096)) by positivity)
    simp only [neg_mul] at h₁ h₂ h₃ ⊢
    nlinarith only [h₁,h₂,h₃,
      mul_nonneg hG.le (mul_nonneg hcore (Real.exp_pos (-u^2)).le)]

noncomputable def dottieFarEnvelopeMass (w : ℂ) : ℝ :=
  dottieFarGammaCore w.re * √Real.pi + dottieFarGammaOuter w.im * √(Real.pi/(1/4))

theorem dottie_far_gamma_envelope_bound_at {w : ℂ}
    (hr : w.re ∈ Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) (u : ℝ) :
    ‖Gamma (w+verticalPoint 7 u)‖ * Real.exp (-u^2+Real.pi*u/2) ≤
      ‖Gamma (2+(dottieHeight : ℂ)*I)‖ * dottieFarGammaEnvelope w.re w.im u := by
  have he : w+verticalPoint 7 u = ⟨w.re+7,w.im+u⟩ := by
    apply Complex.ext <;> simp [verticalPoint]
  rw [he]
  have hT : 0 ≤ dottieHeight := by linarith only [dottieHeight_enclosure.1]
  apply dottie_far_tilted_gamma_envelope hr hi
  · have hg := dottie_exp_neg_le_norm_Gamma_two dottieHeight
    rw [abs_of_nonneg hT] at hg
    rw [show -Real.pi*dottieHeight/2 = -(Real.pi/2*dottieHeight) by ring]
    exact hg
  · intro v
    have hz : (⟨w.re+7,v⟩ : ℂ) = (w.re : ℂ)+7+(v : ℂ)*I := by
      apply Complex.ext <;> simp
    rw [hz]
    rw [show -Real.pi*|v|/2 = -(Real.pi/2*|v|) by ring]
    exact dottie_norm_Gamma_seven_le hr.1 hr.2 v

/-- The actual far omitted range is bounded by two explicit real numbers,
one for the original input and one for the reflected input. -/
theorem dottie_far_omitted_norm_le_scalar {w : ℂ}
    (hr : w.re ∈ Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieOmittedFarSmooth w‖ ≤
      dottieFarScalar dottieOmittedFarCut w * dottieFarEnvelopeMass w +
      dottieFarScalar dottieOmittedFarCut (1-conj w) * dottieFarEnvelopeMass (1-conj w) := by
  have hm : (1-conj w).re ∈ Icc (1/2-63/2048) (1/2+63/2048) := by
    simp only [sub_re, one_re, conj_re]
    exact ⟨by linarith only [hr.2], by linarith only [hr.1]⟩
  have hmi : |(1-conj w).im-dottieHeight| ≤ 35/2048 := by
    simpa only [sub_im, one_im, conj_im, sub_neg_eq_add, zero_add] using hi
  have h := dottie_far_omitted_norm_le_of_tilted_gamma
    (by linarith only [hr.1] : 0 < w.re) (by linarith only [hr.2] : w.re < 1)
    _ _ (dottie_far_gamma_envelope_integrable w.re w.im)
    (dottie_far_gamma_envelope_integrable (1-conj w).re (1-conj w).im)
    (dottie_far_gamma_envelope_bound_at hr hi) (dottie_far_gamma_envelope_bound_at hm hmi)
  rw [dottie_far_gamma_envelope_integral, dottie_far_gamma_envelope_integral] at h
  exact h

#print axioms dottie_far_gamma_envelope_integrable
#print axioms dottie_far_gamma_envelope_integral
#print axioms dottie_far_tilted_gamma_envelope
#print axioms dottie_far_gamma_envelope_bound_at
#print axioms dottie_far_omitted_norm_le_scalar

end QuarticModel
