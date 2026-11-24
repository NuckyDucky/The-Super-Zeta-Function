import DottieGammaPhase

/-! Relative Stirling estimate with the same complex phase on both sides.
The common real normalization cancels in the finite Gamma products. -/

open Complex Filter
open scoped Topology

namespace QuarticModel

open private log_correction_tendsto gamma_log_partial_sum logTrapezoidError trapezoid_error_sum
  from DottieGammaPhase

noncomputable def dottieStirlingLeading (z : ℂ) : ℂ := (z-1/2)*Complex.log z-z

private noncomputable def endpoint (z : ℂ) (n : ℕ) : ℂ :=
  (z+n+1/2)*Complex.log (z+n)-(z+n) -
    z*Complex.log n - (((n : ℂ)+1/2)*Complex.log n-n)

private theorem endpoint_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (endpoint z) atTop (𝓝 0) := by
  apply (log_correction_tendsto z).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsplit : (n : ℂ)*(1+z/n) = z+n := by
    rw [mul_add, mul_one, mul_div_cancel₀ z hn', add_comm]
  have hsum : z+(n : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hne : 1+z/(n : ℂ) ≠ 0 := by
    intro he
    apply hsum
    rw [← hsplit, he, mul_zero]
  have hlog : Complex.log (z+n) = Complex.log (n : ℂ)+Complex.log (1+z/(n : ℂ)) := by
    rw [← hsplit]
    simpa only [Complex.ofReal_natCast, Complex.natCast_log] using
      Complex.log_ofReal_mul (Nat.cast_pos.mpr hn : (0 : ℝ) < n) hne
  unfold endpoint
  rw [hlog]
  ring

private noncomputable def finiteExponent (z : ℂ) (n : ℕ) : ℂ :=
  Complex.log (n : ℂ)*z + Complex.log (n.factorial : ℂ) -
    ∑ k ∈ Finset.range (n+1), Complex.log (z+k)

private theorem finiteExponent_difference {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re) (n : ℕ) :
    finiteExponent w n - finiteExponent z n =
      (dottieStirlingLeading w-dottieStirlingLeading z) - (endpoint w n-endpoint z n) -
        ((∑ k ∈ Finset.range n, logTrapezoidError w k) - ∑ k ∈ Finset.range n, logTrapezoidError z k) := by
  unfold finiteExponent endpoint dottieStirlingLeading
  rw [gamma_log_partial_sum hw, gamma_log_partial_sum hz]
  ring

/-- Exact ratio of Gamma values in the right half-plane, with the complex
relative Stirling correction bounded by the sum of the two endpoint errors. -/
theorem dottie_gamma_ratio_with_error {z w : ℂ} (hz : 0 < z.re) (hw : 0 < w.re)
    (hzt : 1 ≤ |z.im|) (hwt : 1 ≤ |w.im|) :
    ∃ error : ℂ, ‖error‖ ≤ 1/(3*|z.im|)+1/(3*|w.im|) ∧
      Gamma w/Gamma z = Complex.exp (dottieStirlingLeading w-dottieStirlingLeading z+error) := by
  obtain ⟨az,bz⟩ := trapezoid_error_sum hz hzt
  obtain ⟨aw,bw⟩ := trapezoid_error_sum hw hwt
  let error := (∑' k, logTrapezoidError z k)-(∑' k, logTrapezoidError w k)
  refine ⟨error, (norm_sub_le _ _).trans (add_le_add bz bw), ?_⟩
  have hseq := (GammaSeq_tendsto_Gamma w).div (GammaSeq_tendsto_Gamma z) (Gamma_ne_zero_of_re_pos hz)
  have hend := (endpoint_tendsto hw).sub (endpoint_tendsto hz)
  have hsum := aw.of_norm.hasSum.tendsto_sum_nat.sub az.of_norm.hasSum.tendsto_sum_nat
  have hg := (tendsto_const_nhds (x := dottieStirlingLeading w-dottieStirlingLeading z)).sub hend |>.sub hsum
  rw [sub_self, sub_zero, show dottieStirlingLeading w-dottieStirlingLeading z -
      ((∑' k, logTrapezoidError w k)-(∑' k, logTrapezoidError z k)) =
      dottieStirlingLeading w-dottieStirlingLeading z+error by dsimp [error]; ring] at hg
  have hf := hg.cexp
  apply tendsto_nhds_unique hseq
  apply hf.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change _ = GammaSeq w n / GammaSeq z n
  rw [dottie_gammaSeq_eq_exp hw hn, dottie_gammaSeq_eq_exp hz hn, ← Complex.exp_sub]
  change _ = Complex.exp (finiteExponent w n-finiteExponent z n)
  rw [finiteExponent_difference hz hw]

#print axioms dottie_gamma_ratio_with_error

end QuarticModel
