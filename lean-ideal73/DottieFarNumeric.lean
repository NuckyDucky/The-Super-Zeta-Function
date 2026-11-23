import DottieFarGammaEnvelope

/-! Explicit rational arithmetic for the omitted far Gaussian contour. -/

namespace QuarticModel

open Complex Set
open scoped ComplexConjugate
open SuperZeta.StirlingCorrection
set_option autoImplicit false
set_option maxRecDepth 4096

theorem dottie_theta_scale_lt_two_million : archivedThetaScale < 2*10^6 := by
  have hs : √(26509772707289 : ℝ) < 6*10^6 :=
    (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  exact (div_lt_iff₀ Real.pi_pos).2 (by linarith only [hs, Real.pi_gt_three])

private theorem dottie_far_scalar_factor {w : ℂ} (hw : 0 ≤ w.re) :
    dottieFarScalar dottieOmittedFarCut w =
      ((1+(dottieOmittedFarCut.sqrt : ℝ)⁻¹)*((w.re+7)/(w.re+6))*Real.exp 49 /
        (14*Real.pi*(dottieOmittedFarCut : ℝ))) *
      (archivedThetaScale/(dottieOmittedFarCut : ℝ))^(w.re+5) := by
  let X : ℝ := dottieOmittedFarCut
  let B := archivedThetaScale
  let q := w.re+5
  have hX : 0 < X := by norm_num [X, dottieOmittedFarCut]
  have hB : 0 < B := archivedThetaScale_pos
  have hpowB : B^(w.re+7) = B^q*B^2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hB]
    congr 1
    dsimp [q]
    ring
  have hpowX : X^(1-(w.re+7)) = (X^q)⁻¹*X⁻¹ := by
    rw [show 1-(w.re+7) = -q+(-1) by dsimp [q]; ring, Real.rpow_add hX,
      Real.rpow_neg hX.le, Real.rpow_neg_one]
  unfold dottieFarScalar
  change (B^(w.re+7)*((1+(dottieOmittedFarCut.sqrt : ℝ)⁻¹)*
    (X^(1-(w.re+7))*((w.re+7)/(w.re+7-1)))))*Real.exp 49/(14*Real.pi*B^2) =
      ((1+(dottieOmittedFarCut.sqrt : ℝ)⁻¹)*((w.re+7)/(w.re+6))*Real.exp 49 /
        (14*Real.pi*X))*(B/X)^q
  rw [hpowB, hpowX, Real.div_rpow hB.le hX.le, show w.re+7-1=w.re+6 by ring]
  field_simp [Real.pi_ne_zero, hB.ne', hX.ne', (Real.rpow_pos_of_pos hX q).ne',
    show w.re+6 ≠ 0 by linarith]

private theorem dottie_far_one_side_numeric {w : ℂ} (hw : 0 ≤ w.re)
    (ht : |w.im-dottieHeight| ≤ 35/2048) :
    dottieFarScalar dottieOmittedFarCut w * dottieFarEnvelopeMass w ≤ 1/(5*10^33) := by
  let X : ℝ := dottieOmittedFarCut
  let B := archivedThetaScale
  let T := dottieHeight
  let q := w.re+5
  let C := (1+(dottieOmittedFarCut.sqrt : ℝ)⁻¹)*((w.re+7)/(w.re+6))*Real.exp 49 /
    (14*Real.pi*X)
  let M : ℝ := 4*3^49/(42*(2*10^25))
  have hX : X = 2*10^25 := by norm_num [X, dottieOmittedFarCut]
  have hX₀ : 0 < X := by rw [hX]; norm_num
  have hB : 0 < B := archivedThetaScale_pos
  have hT : 0 < T := by dsimp [T]; linarith only [dottieHeight_enclosure.1]
  have hT₁ : T < 5*10^12 := by dsimp [T]; linarith only [dottieHeight_enclosure.2]
  have hB₁ : B < 2*10^6 := dottie_theta_scale_lt_two_million
  have hBa : 0 ≤ B/X := by positivity
  have hBa₁ : B/X ≤ 1/10^19 := by
    rw [div_le_iff₀ hX₀, hX]
    linarith only [hB₁]
  have hBT : (B/X)*T ≤ 1/(2*10^6) :=
    (mul_le_mul hBa₁ hT₁.le hT.le (by norm_num)).trans (by norm_num)
  have hq : 5 ≤ q := by dsimp [q]; linarith
  have hpow (b bound : ℝ) (hb : 0 ≤ b) (h : b ≤ bound) (hl : bound ≤ 1) :
      b^q ≤ bound^5 :=
    (Real.rpow_le_rpow hb h (by linarith only [hq])).trans
      (by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge' (hb.trans h) hl (by norm_num) hq)
  have hct : ((B/X)*T)^q ≤ (1/(2*10^6) : ℝ)^5 :=
    hpow _ _ (mul_nonneg hBa hT.le) hBT (by norm_num)
  have hco : (B/X)^q ≤ (1/10^19 : ℝ)^5 := hpow _ _ hBa hBa₁ (by norm_num)
  have hs : (1 : ℝ) ≤ (dottieOmittedFarCut.sqrt : ℝ) := by
    exact_mod_cast (show 1 ≤ dottieOmittedFarCut.sqrt by decide +kernel)
  have hs' : 1+(dottieOmittedFarCut.sqrt : ℝ)⁻¹ ≤ 2 := by
    have h := (inv_le_one₀ (zero_lt_one.trans_le hs)).2 hs
    linarith
  have hp : 0 < w.re+6 := by linarith
  have hp' : (w.re+7)/(w.re+6) ≤ 2 := by
    exact (div_le_iff₀ hp).2 (by linarith)
  have hp₀ : 0 ≤ (w.re+7)/(w.re+6) := div_nonneg (by linarith) hp.le
  have he : Real.exp 49 ≤ (3 : ℝ)^49 := by
    rw [show (49 : ℝ) = (49 : ℕ)*(1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith only [Real.exp_one_lt_d9]) 49
  have hC₀ : 0 ≤ C := by dsimp only [C]; positivity
  have hC : C ≤ M := by
    have hnum := mul_le_mul_of_nonneg_right (mul_le_mul hs' hp' hp₀ (by norm_num))
      (Real.exp_pos 49).le
    have hnum' := hnum.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2*2))
    have hden : 42*(2*10^25 : ℝ) ≤ 14*Real.pi*X := by rw [hX]; linarith only [Real.pi_gt_three]
    calc
      C ≤ 2*2*3^49/(14*Real.pi*X) := div_le_div_of_nonneg_right hnum' (by positivity)
      _ ≤ 2*2*3^49/(42*(2*10^25)) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = M := by dsimp [M]; ring
  have hsqrt : √Real.pi ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [Real.pi_lt_four]⟩
  have hsqrt' : √(Real.pi/(1/4)) ≤ 4 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [Real.pi_lt_four]⟩
  have hsmall : Real.exp (35*Real.pi/4096+1/10^10) ≤ 2 := by
    refine (Real.exp_le_exp.mpr (show 35*Real.pi/4096+1/10^10 ≤ 1/2 by
      linarith only [Real.pi_lt_four])).trans ?_
    have heq : Real.exp (1/2 : ℝ)^2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add, show (1/2 : ℝ)+1/2=1 by norm_num]
    by_contra! hlarge
    have hsq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlarge.le 2
    linarith only [hsq,heq,Real.exp_one_lt_d9]
  have hout : Real.exp (35*Real.pi/4096-100) ≤ ((27/10 : ℝ)^99)⁻¹ := by
    have h99 : (27/10 : ℝ)^99 ≤ Real.exp 99 := by
      rw [show (99 : ℝ) = (99 : ℕ)*(1 : ℝ) by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith only [Real.exp_one_gt_d9]) 99
    refine (Real.exp_le_exp.mpr (show 35*Real.pi/4096-100 ≤ -99 by
      linarith only [Real.pi_lt_four])).trans ?_
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) (show (0 : ℝ) < (27/10)^99 by positivity)).2 h99
  have ht' : (8+|w.im|)^8 ≤ (6*10^12 : ℝ)^8 := by
    have ha := abs_add_le (w.im-T) T
    rw [sub_add_cancel, abs_of_pos hT] at ha
    exact pow_le_pow_left₀ (by positivity) (by linarith only [ha,ht,hT₁]) 8
  have hform : dottieFarScalar dottieOmittedFarCut w * dottieFarEnvelopeMass w =
      C*(((B/X)*T)^q * Real.exp (35*Real.pi/4096+1/10^10)*√Real.pi) +
      C*((B/X)^q * (18*(8+|w.im|)^8*Real.exp (35*Real.pi/4096-100))*√(Real.pi/(1/4))) := by
    rw [dottie_far_scalar_factor hw]
    unfold dottieFarEnvelopeMass dottieFarGammaCore dottieFarGammaOuter
    change C*(B/X)^q * (T^q * Real.exp (35*Real.pi/4096+1/10^10)*√Real.pi +
      (18*(8+|w.im|)^8*Real.exp (35*Real.pi/4096-100))*√(Real.pi/(1/4))) = _
    rw [Real.mul_rpow hBa hT.le]
    ring
  rw [hform]
  calc
    _ ≤ M*((1/(2*10^6) : ℝ)^5*2*2) +
        M*((1/10^19 : ℝ)^5*(18*(6*10^12 : ℝ)^8*((27/10 : ℝ)^99)⁻¹)*4) := by
      gcongr
    _ ≤ _ := by dsimp [M]; norm_num

/-- Uniform absolute far omitted bound on the full rectangle containing
both outer rings. The coefficient count and the charged integral are exact. -/
theorem dottie_far_omitted_uniform_absolute {w : ℂ}
    (hr : w.re ∈ Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieOmittedFarSmooth w‖ ≤ 2/(5*10^33) := by
  have hre : 0 ≤ w.re := by linarith only [hr.1]
  have hre' : 0 ≤ (1-conj w).re := by
    rw [sub_re, one_re, conj_re]
    linarith only [hr.2]
  have him' : |(1-conj w).im-dottieHeight| ≤ 35/2048 := by simpa using hi
  exact (dottie_far_omitted_norm_le_scalar hr hi).trans
    ((add_le_add (dottie_far_one_side_numeric hre hi) (dottie_far_one_side_numeric hre' him')).trans (by norm_num))

#print axioms dottie_theta_scale_lt_two_million
#print axioms dottie_far_omitted_uniform_absolute

end QuarticModel
