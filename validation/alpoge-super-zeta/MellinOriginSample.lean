import NativeDottieMellinFinite
import SuperZeta.MemePrecision

/-! The actual origin sample, using the earlier pi-hat bound for exp(1).
The two logarithmic inequalities are reduced to rational exponential tests. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

private theorem sinh_one_enclosure :
    (1.17520119364380145688238184:ℝ) ≤ Real.sinh 1 ∧
      Real.sinh 1 ≤ 1.17520119364380145688238186 := by
  obtain ⟨heL,heU⟩ := SuperZeta.Meme.exp_one_bounds
  have hiL : (0.36787944117144232159552376:ℝ) ≤ (Real.exp 1)⁻¹ := by
    calc
      _ ≤ (2.71828182845904523536028747135266252:ℝ)⁻¹ := by norm_num
      _ ≤ _ := (inv_le_inv₀ (by positivity) (Real.exp_pos 1)).mpr heU
  have hiU : (Real.exp 1)⁻¹ ≤ (0.36787944117144232159552378:ℝ) := by
    calc
      _ ≤ (2.71828182845904523536028747135266248:ℝ)⁻¹ :=
        (inv_le_inv₀ (Real.exp_pos 1) (by positivity)).mpr heL
      _ ≤ _ := by norm_num
  rw [Real.sinh_eq, Real.exp_neg]
  exact ⟨by linarith only [heL,hiU], by linarith only [heU,hiL]⟩

private def originRatio : ℝ :=
  (3+4*(Real.sinh 1^2+1)-4*Real.sinh 1)/(3+4*(Real.sinh 1^2+1)+4*Real.sinh 1)

private theorem originRatio_enclosure :
    (0.45419434045339830:ℝ) ≤ originRatio ∧ originRatio ≤ 0.45419434045339834 := by
  obtain ⟨hl,hu⟩ := sinh_one_enclosure
  have hl2 := pow_le_pow_left₀ (show 0 ≤ (1.17520119364380145688238184:ℝ) by norm_num) hl 2
  have hu2 := pow_le_pow_left₀ (Real.sinh_pos_iff.mpr one_pos).le hu 2
  have hd : 0 < 3+4*(Real.sinh 1^2+1)+4*Real.sinh 1 := by
    linarith only [hl, sq_nonneg (Real.sinh 1)]
  unfold originRatio
  exact ⟨(le_div_iff₀ hd).mpr (by linarith only [hl,hu,hl2,hu2]),
    (div_le_iff₀ hd).mpr (by linarith only [hl,hu,hl2,hu2])⟩

private def expApprox (q : ℚ) : ℚ := ∑ j ∈ Finset.range 28, q^j/(j.factorial:ℚ)

private theorem expApprox_error (q : ℚ) (hq : |(q:ℝ)| ≤ 1) :
    |Real.exp (q:ℝ) - (expApprox q:ℝ)| ≤ (1:ℝ)/10^26 := by
  have ht := Real.exp_bound hq (n := 28) (by norm_num)
  have hpow : |(q:ℝ)|^28 ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg (q:ℝ)) hq 28
  have htail : |(q:ℝ)|^28 * ((29:ℝ)/(Nat.factorial 28*28)) ≤ (1:ℝ)/10^26 := by
    calc
      _ ≤ 1 * ((29:ℝ)/(Nat.factorial 28*28)) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ _ := by norm_num [Nat.factorial]
  apply le_trans _ htail
  simpa only [expApprox, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.reduceAdd] using ht

private def sampleLower : ℚ := -789230109860795 / 10^15
private def sampleUpper : ℚ := -789230109860793 / 10^15

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
private theorem exp_sampleLower :
    Real.exp (sampleLower:ℝ) ≤ 0.45419434045339830 := by
  have hc : expApprox sampleLower + 1/10^26 ≤ (0.45419434045339830:ℚ) := by decide +kernel
  have hr : (expApprox sampleLower:ℝ)+(1:ℝ)/10^26 ≤ 0.45419434045339830 := by
    have h : ((expApprox sampleLower + 1/10^26:ℚ):ℝ) ≤ ((0.45419434045339830:ℚ):ℝ) :=
      Rat.cast_le.mpr hc
    norm_num at h ⊢
    exact h
  have he := (abs_le.mp (expApprox_error sampleLower (by norm_num [sampleLower, abs_le]))).2
  linarith only [hr,he]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 1000000 in
private theorem exp_sampleUpper :
    (0.45419434045339834:ℝ) ≤ Real.exp (sampleUpper:ℝ) := by
  have hc : (0.45419434045339834:ℚ) ≤ expApprox sampleUpper - 1/10^26 := by decide +kernel
  have hr : (0.45419434045339834:ℝ) ≤ (expApprox sampleUpper:ℝ)-(1:ℝ)/10^26 := by
    have h : ((0.45419434045339834:ℚ):ℝ) ≤ ((expApprox sampleUpper - 1/10^26:ℚ):ℝ) :=
      Rat.cast_le.mpr hc
    norm_num at h ⊢
    exact h
  have he := (abs_le.mp (expApprox_error sampleUpper (by norm_num [sampleUpper, abs_le]))).1
  linarith only [hr,he]

theorem mellinOriginSample :
    (-789230109860795/10^15:ℝ) ≤ finiteCoefficientDensity false 0 0 ∧
      finiteCoefficientDensity false 0 0 ≤ (-789230109860793/10^15:ℝ) ∧
      finiteCoefficientDensity true 0 0 = 0 := by
  have hf : finiteCoefficientDensity false 0 0 = Real.log originRatio := by
    rw [finiteCoefficientDensity, finiteLogGap_eq]
    norm_num [originRatio]
  obtain ⟨hl,hu⟩ := originRatio_enclosure
  have hp : 0 < originRatio := lt_of_lt_of_le (by norm_num) hl
  have hsL := (Real.le_log_iff_exp_le hp).mpr (exp_sampleLower.trans hl)
  have hsU := (Real.log_le_iff_le_exp hp).mpr (hu.trans exp_sampleUpper)
  refine ⟨?_,?_,by simp [finiteCoefficientDensity]⟩
  · rw [hf]
    simpa only [sampleLower, Rat.cast_div, Rat.cast_neg, Rat.cast_pow, Rat.cast_ofNat] using hsL
  · rw [hf]
    simpa only [sampleUpper, Rat.cast_div, Rat.cast_neg, Rat.cast_pow, Rat.cast_ofNat] using hsU

#print axioms mellinOriginSample

end DottieOriented.NativeSpectrum
end
