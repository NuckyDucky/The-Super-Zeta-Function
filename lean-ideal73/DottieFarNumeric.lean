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

private theorem dottie_far_scalar_factor {N : ℕ} (hN : 0 < N) {w : ℂ} (hw : 0 ≤ w.re) :
    dottieFarScalar N w =
      ((1+(N.sqrt : ℝ)⁻¹)*((w.re+7)/(w.re+6))*Real.exp 49 /
        (14*Real.pi*(N : ℝ))) *
      (archivedThetaScale/(N : ℝ))^(w.re+5) := by
  let X : ℝ := N
  let B := archivedThetaScale
  let q := w.re+5
  have hX : 0 < X := by dsimp only [X]; exact_mod_cast hN
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
  change (B^(w.re+7)*((1+(N.sqrt : ℝ)⁻¹)*
    (X^(1-(w.re+7))*((w.re+7)/(w.re+7-1)))))*Real.exp 49/(14*Real.pi*B^2) =
      ((1+(N.sqrt : ℝ)⁻¹)*((w.re+7)/(w.re+6))*Real.exp 49 /
        (14*Real.pi*X))*(B/X)^q
  rw [hpowB, hpowX, Real.div_rpow hB.le hX.le, show w.re+7-1=w.re+6 by ring]
  field_simp [Real.pi_ne_zero, hB.ne', hX.ne', (Real.rpow_pos_of_pos hX q).ne',
    show w.re+6 ≠ 0 by linarith]

private theorem dottie_far_one_side_numeric {N : ℕ} (hN : 8*10^24 ≤ N)
    {w : ℂ} (hw : 0 ≤ w.re)
    (ht : |w.im-dottieHeight| ≤ 35/2048) :
    dottieFarScalar N w * dottieFarEnvelopeMass w ≤ 1/(5*10^33) := by
  let X : ℝ := N
  let B := archivedThetaScale
  let T := dottieHeight
  let q := w.re+5
  let C := (1+(N.sqrt : ℝ)⁻¹)*((w.re+7)/(w.re+6))*Real.exp 49 /
    (14*Real.pi*X)
  let M : ℝ := 4*(11/4)^49/(42*(8*10^24))
  have hN₀ : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hX : (8*10^24 : ℝ) ≤ X := by dsimp only [X]; exact_mod_cast hN
  have hX₀ : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hB : 0 < B := archivedThetaScale_pos
  have hT : 0 < T := by dsimp [T]; linarith only [dottieHeight_enclosure.1]
  have hT₁ : T < 453*10^10 := by dsimp [T]; linarith only [dottieHeight_enclosure.2]
  have hB₁ : B < 1750000 := by
    have hs : √(26509772707289 : ℝ) < 5250000 :=
      (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
    exact (div_lt_iff₀ Real.pi_pos).2 (by linarith only [hs, Real.pi_gt_three])
  have hBa : 0 ≤ B/X := by positivity
  have hBa₁ : B/X ≤ 7/(32*10^18) := by
    rw [div_le_iff₀ hX₀]
    linarith only [hB₁,hX]
  have hBT : (B/X)*T ≤ 1/10^6 :=
    (mul_le_mul hBa₁ hT₁.le hT.le (by norm_num)).trans (by norm_num)
  have hq : 5 ≤ q := by dsimp [q]; linarith
  have hpow (b bound : ℝ) (hb : 0 ≤ b) (h : b ≤ bound) (hl : bound ≤ 1) :
      b^q ≤ bound^5 :=
    (Real.rpow_le_rpow hb h (by linarith only [hq])).trans
      (by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_ge' (hb.trans h) hl (by norm_num) hq)
  have hct : ((B/X)*T)^q ≤ (1/10^6 : ℝ)^5 :=
    hpow _ _ (mul_nonneg hBa hT.le) hBT (by norm_num)
  have hco : (B/X)^q ≤ (7/(32*10^18) : ℝ)^5 := hpow _ _ hBa hBa₁ (by norm_num)
  have hs : (1 : ℝ) ≤ (N.sqrt : ℝ) := by
    exact_mod_cast (show 1 ≤ N.sqrt from Nat.le_sqrt'.mpr (by omega))
  have hs' : 1+(N.sqrt : ℝ)⁻¹ ≤ 2 := by
    have h := (inv_le_one₀ (zero_lt_one.trans_le hs)).2 hs
    linarith
  have hp : 0 < w.re+6 := by linarith
  have hp' : (w.re+7)/(w.re+6) ≤ 2 := by
    exact (div_le_iff₀ hp).2 (by linarith)
  have hp₀ : 0 ≤ (w.re+7)/(w.re+6) := div_nonneg (by linarith) hp.le
  have he : Real.exp 49 ≤ (11/4 : ℝ)^49 := by
    rw [show (49 : ℝ) = (49 : ℕ)*(1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (by linarith only [Real.exp_one_lt_d9]) 49
  have hC₀ : 0 ≤ C := by dsimp only [C]; positivity
  have hC : C ≤ M := by
    have hnum := mul_le_mul_of_nonneg_right (mul_le_mul hs' hp' hp₀ (by norm_num))
      (Real.exp_pos 49).le
    have hnum' := hnum.trans (mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2*2))
    have hden : 42*(8*10^24 : ℝ) ≤ 14*Real.pi*X := by
      calc
        _ ≤ 42*X := by linarith only [hX]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [Real.pi_gt_three]) hX₀.le
    calc
      C ≤ 2*2*(11/4)^49/(14*Real.pi*X) := div_le_div_of_nonneg_right hnum' (by positivity)
      _ ≤ 2*2*(11/4)^49/(42*(8*10^24)) := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
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
  have hform : dottieFarScalar N w * dottieFarEnvelopeMass w =
      C*(((B/X)*T)^q * Real.exp (35*Real.pi/4096+1/10^10)*√Real.pi) +
      C*((B/X)^q * (18*(8+|w.im|)^8*Real.exp (35*Real.pi/4096-100))*√(Real.pi/(1/4))) := by
    rw [dottie_far_scalar_factor hN₀ hw]
    unfold dottieFarEnvelopeMass dottieFarGammaCore dottieFarGammaOuter
    change C*(B/X)^q * (T^q * Real.exp (35*Real.pi/4096+1/10^10)*√Real.pi +
      (18*(8+|w.im|)^8*Real.exp (35*Real.pi/4096-100))*√(Real.pi/(1/4))) = _
    rw [Real.mul_rpow hBa hT.le]
    ring
  rw [hform]
  calc
    _ ≤ M*((1/10^6 : ℝ)^5*2*2) +
        M*((7/(32*10^18) : ℝ)^5*(18*(6*10^12 : ℝ)^8*((27/10 : ℝ)^99)⁻¹)*4) := by
      gcongr
    _ ≤ _ := by dsimp [M]; norm_num

/-- The original smoothed, reflected norm sum above `8 * 10^24` is small
for any finite subset. Both Gaussian sheets use the original normalization. -/
theorem dottie_smooth_subset_uniform_absolute (S : Finset ℕ)
    (hS : ∀ n ∈ S, 8*10^24 < n) {w : ℂ}
    (hr : w.re ∈ Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖∑ n ∈ S, dottieSmoothTerm w n‖ ≤ 2/(5*10^33) := by
  have hS₀ : ∀ n ∈ S, n ≠ 0 := fun n hn => by have h := hS n hn; omega
  have hm : (1-conj w).re ∈ Icc (1/2-63/2048) (1/2+63/2048) := by
    simp only [sub_re, one_re, conj_re]
    exact ⟨by linarith only [hr.2], by linarith only [hr.1]⟩
  have him : |(1-conj w).im-dottieHeight| ≤ 35/2048 := by simpa using hi
  have hR : 0 < w.re := by linarith only [hr.1]
  have hM : 0 < (1-conj w).re := by linarith only [hm.1]
  have hside {v : ℂ} (hR : 0 < v.re)
      (hr : v.re ∈ Icc (1/2-63/2048) (1/2+63/2048))
      (hi : |v.im-dottieHeight| ≤ 35/2048) : ‖dottieRightSide S v 7‖ ≤ 1/(5*10^33) := by
    have h := dottie_right_seven_norm_le_of_tilted_gamma S
      (show 0 < 8*10^24 by norm_num) hS hR _ (dottie_far_gamma_envelope_integrable v.re v.im)
      (dottie_far_gamma_envelope_bound_at hr hi)
    rw [dottie_far_gamma_envelope_integral] at h
    exact h.trans (dottie_far_one_side_numeric le_rfl hR.le hi)
  have heq : (∑ n ∈ S, dottieSmoothTerm w n) =
      dottieRightSide S w 7 + conj (dottieRightSide S (1-conj w) 7) := by
    have hR' : 0 < w.re+1 := by linarith
    have hM' : 0 < (1-conj w).re+1 := by linarith
    rw [dottie_right_side_eq_range_side S w (by norm_num) hR' hS₀,
      dottie_right_side_eq_range_side S (1-conj w) (by norm_num) hM' hS₀,
      dottie_range_side_eq_sum S hR' hS₀, dottie_range_side_eq_sum S hM' hS₀,
      map_sum, ← Finset.sum_add_distrib]
    rfl
  rw [heq]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj]
  exact (add_le_add (hside hR hr hi) (hside hM hm him)).trans (by norm_num)

/-- The archived far range is a subset of the norms controlled by the
uniform bound. -/
theorem dottie_far_omitted_uniform_absolute {w : ℂ}
    (hr : w.re ∈ Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieOmittedFarSmooth w‖ ≤ 2/(5*10^33) := by
  unfold dottieOmittedFarSmooth
  exact dottie_smooth_subset_uniform_absolute _
    (fun _ hn => lt_of_le_of_lt (by norm_num [dottieOmittedFarCut]) (Finset.mem_filter.mp hn).2) hr hi

#print axioms dottie_theta_scale_lt_two_million
#print axioms dottie_smooth_subset_uniform_absolute
#print axioms dottie_far_omitted_uniform_absolute

end QuarticModel
