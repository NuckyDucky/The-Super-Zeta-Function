import SuperZeta.QuarterLine.QuartetShiftContinuation
import SuperZeta.QuarterLine.QuartetLeading
import Mathlib.Analysis.Complex.Liouville

namespace SuperZeta.QuartetBandCauchy
noncomputable section
open Complex Metric Set
open QuartetShiftContinuation UnitSpectrum

def leading (s : ℂ) := upper 0 ^ (-2*s)
def error (s : ℂ) := continuation s / leading s - 1

abbrev OuterBound := ∀ z : ℂ, 7/32 ≤ z.re → z.re ≤ 9/32 → 100 ≤ z.im →
    ‖continuation z / upper 0 ^ (-2*z) - 1‖ ≤ 1/128

lemma leading_ne (s : ℂ) : leading s ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl QuartetLeading.first_ne_zero)

lemma leading_deriv (s : ℂ) :
    HasDerivAt leading (leading s * Complex.log (upper 0) * (-2)) s := by
  unfold leading
  have h := ((hasDerivAt_id s).const_mul (-2:ℂ)).const_cpow (Or.inl (show upper 0 ≠ 0 from QuartetLeading.first_ne_zero))
  simpa [leading, id_eq] using h

lemma continuation_diff {s : ℂ} (ht : 0 < s.im) : DifferentiableAt ℂ continuation s := by
  apply (continuation_analytic _).differentiableAt
  intro e
  have h := congrArg Complex.im e
  simp [Complex.mul_im] at h
  linarith

lemma error_differentiable {s : ℂ} (ht : 0 < s.im) : DifferentiableAt ℂ error s :=
  ((continuation_diff ht).div (leading_deriv s).differentiableAt (leading_ne s)).sub_const _

lemma closed_disk_band {s z : ℂ} (hσ : |s.re-1/4| ≤ 1/64) (ht : 101 ≤ s.im)
    (hz : z ∈ closedBall s (1/64)) : 7/32 ≤ z.re ∧ z.re ≤ 9/32 ∧ 100 ≤ z.im := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have a := abs_le.mp ((Complex.abs_re_le_norm (z-s)).trans hz)
  have b := abs_le.mp ((Complex.abs_im_le_norm (z-s)).trans hz)
  simp only [Complex.sub_re,Complex.sub_im] at a b
  obtain ⟨h₁,h₂⟩ := abs_le.mp hσ
  exact ⟨by linarith [a.1],by linarith [a.2],by linarith [b.1]⟩

lemma error_deriv_norm {s : ℂ} (H : OuterBound)
    (hσ : |s.re-1/4| ≤ 1/64) (ht : 101 ≤ s.im) : ‖deriv error s‖ ≤ 1/2 := by
  have hC : DiffContOnCl ℂ error (ball s (1/64)) := by
    apply DifferentiableOn.diffContOnCl_ball (U:=closedBall s (1/64)) _ Subset.rfl
    intro z hz
    have hi := (closed_disk_band hσ ht hz).2.2
    exact (error_differentiable (by linarith)).differentiableWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0:ℝ)<1/64) hC
    (C:=1/128) (fun z hz => by
      obtain ⟨h₁,h₂,h₃⟩ := closed_disk_band hσ ht (sphere_subset_closedBall hz)
      exact H z h₁ h₂ h₃)
  norm_num at h ⊢
  exact h

lemma error_small {s : ℂ} (H : OuterBound) (hσ : |s.re-1/4| ≤ 1/64) (ht : 101 ≤ s.im) :
    ‖error s‖ ≤ 1/128 := by
  obtain ⟨h₁,h₂,h₃⟩ := closed_disk_band hσ ht (mem_closedBall_self (by norm_num))
  exact H s h₁ h₂ h₃

lemma continuation_ne {s : ℂ} (H : OuterBound) (hσ : |s.re-1/4| ≤ 1/64)
    (ht : 101 ≤ s.im) : continuation s ≠ 0 := by
  intro hz
  have h := error_small H hσ ht
  norm_num [error,hz] at h

/-- The entire complex logarithmic derivative stays in one explicit disk
around the leading root's logarithmic derivative. -/
theorem log_deriv_estimate {s : ℂ} (H : OuterBound)
    (hσ : |s.re-1/4| ≤ 1/64) (ht : 101 ≤ s.im) :
    ‖deriv continuation s / continuation s - (-2*Complex.log (upper 0))‖ ≤ 64/127 := by
  have hl := leading_ne s
  have hz := continuation_ne H hσ ht
  have hs := error_small H hσ ht
  have hend : (127/128:ℝ) ≤ ‖error s + 1‖ := by
    have h := norm_add_le (error s + 1) (-error s)
    rw [show error s + 1 + -error s = 1 by ring, norm_one, norm_neg] at h
    linarith
  have hden : error s + 1 ≠ 0 := fun e => by rw [e,norm_zero] at hend; norm_num at hend
  have hD := (((continuation_diff (show 0 < s.im by linarith)).hasDerivAt.div (leading_deriv s) hl).sub_const 1).deriv
  change deriv error s = _ at hD
  have eqn : deriv continuation s / continuation s =
      -2*Complex.log (upper 0) + deriv error s / (error s + 1) := by
    rw [hD]
    simp only [error,sub_add_cancel]
    field_simp
    ring
  have er : ‖deriv error s / (error s + 1)‖ ≤ 64/127 := by
    rw [norm_div,div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0:ℝ)<127/128) hend)]
    linarith [error_deriv_norm H hσ ht]
  rw [eqn,add_sub_cancel_left]
  exact er

/-- A uniform error estimate on the adjoining strip controls the *horizontal*
logarithmic slope of the original continuation at every input in the inner strip. -/
theorem log_slope {s : ℂ} (H : OuterBound) (hσ : |s.re-1/4| ≤ 1/64) (ht : 101 ≤ s.im) :
    (deriv continuation s / continuation s).re < -(62/381:ℝ) := by
  have hnorm : (3/2:ℝ) < ‖upper 0‖ := by
    have hi : (upper 0).im = UnitSpectrum.levelHeight 0 := rfl
    linarith [Complex.im_le_norm (upper 0),QuartetLeading.height_interval.1]
  have hinv : ‖upper 0‖⁻¹ < (2/3:ℝ) := by
    exact (inv_lt_comm₀ (by linarith) (by norm_num)).mpr (by norm_num; linarith)
  have hlog := Real.one_sub_inv_le_log_of_pos (show 0 < ‖upper 0‖ by linarith)
  have h := log_deriv_estimate H hσ ht
  have hreal := (Complex.re_le_norm _).trans h
  rw [Complex.sub_re] at hreal
  have log_re : (-2*Complex.log (upper 0)).re = -2*Real.log ‖upper 0‖ := by
    simp [Complex.mul_re,Complex.log_re]
  rw [log_re] at hreal
  linarith

/-- Along a vertical input line, this negative imaginary part gives positive
radial growth for the full function via the logarithmic derivative. -/
theorem vertical_log_growth {s : ℂ} (H : OuterBound) (hσ : |s.re-1/4| ≤ 1/64)
    (ht : 101 ≤ s.im) : 379/508 < -(deriv continuation s / continuation s).im := by
  have h := log_deriv_estimate H hσ ht
  have him := (Complex.im_le_norm _).trans h
  have ha : 5/8 < (upper 0).arg := QuartetLeading.bounds.1
  rw [Complex.sub_im] at him
  have log_im : (-2*Complex.log (upper 0)).im = -2*(upper 0).arg := by
    simp [Complex.mul_im,Complex.log_im]
  rw [log_im] at him
  linarith

end
end SuperZeta.QuartetBandCauchy
