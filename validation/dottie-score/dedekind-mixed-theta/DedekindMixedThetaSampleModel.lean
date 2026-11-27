import ContourCircleSamples
import DedekindMixedThetaCompletedRings

namespace FieldTarget

open Complex Metric MeasureTheory Set
open DedekindZetaZeroFree.AbelianQuotient
open scoped NNReal

noncomputable section

private theorem contour_relative_error {f p : ℂ} {q : ℝ} (hp : p ≠ 0)
    (h : ‖f - p‖ ≤ q * ‖p‖) : ‖1 - f / p‖ ≤ q := by
  rw [show 1 - f / p = (p - f) / p by rw [sub_div, div_self hp], norm_div, norm_sub_rev]
  exact (div_le_iff₀ (norm_pos_iff.mpr hp)).2 h

/-- The reciprocal of a nonzero reference reading provides the phase correction.
The relative approximation error gives the signed margin. -/
theorem contour_model_weight_im_le {f p : ℂ} {q : ℝ} (hp : p ≠ 0)
    (h : ‖f - p‖ ≤ q * ‖p‖) : ((-I / p) * f).im ≤ q - 1 := by
  have hRe := (abs_le.mp ((abs_re_le_norm _).trans (contour_relative_error hp h))).2
  simp only [sub_re, one_re] at hRe
  rw [show (-I / p) * f = -I * (f / p) by simp [div_eq_mul_inv, mul_comm, mul_left_comm]]
  simp only [mul_im, neg_im, I_re, I_im, zero_mul, neg_mul, one_mul, zero_add]
  linarith

/-- A reference function checked separately on the disk turns a relative
boundary error below one into exclusion on the whole closed disk. -/
theorem contour_ne_zero_of_relative_boundary_error {F P : ℂ → ℂ} {c w : ℂ} {r q : ℝ}
    (hr : 0 < r) (hq : q < 1)
    (hF : DifferentiableOn ℂ F (closedBall c r))
    (hP : DifferentiableOn ℂ P (closedBall c r))
    (hPne : ∀ z ∈ closedBall c r, P z ≠ 0)
    (hError : ∀ z ∈ sphere c r, ‖F z - P z‖ ≤ q * ‖P z‖)
    (hw : w ∈ closedBall c r) : F w ≠ 0 := by
  let g := fun z : ℂ => 1 - F z / P z
  have hreg : DifferentiableOn ℂ g (closure (ball c r)) := by
    rw [closure_ball c hr.ne']
    exact (differentiableOn_const (1 : ℂ)).sub (hF.div hP hPne)
  have hb : ∀ z ∈ frontier (ball c r), ‖g z‖ ≤ q := by
    intro z hz
    rw [frontier_ball c hr.ne'] at hz
    exact contour_relative_error (hPne z (sphere_subset_closedBall hz)) (hError z hz)
  have hw' : w ∈ closure (ball c r) := by rwa [closure_ball c hr.ne']
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    Metric.isBounded_ball hreg.diffContOnCl hb hw'
  intro hz
  exact (not_le_of_gt hq) (by simpa [g, hz] using hmax)

private theorem contour_disk_re_bounds {c w : ℂ} {R : ℝ} (hw : w ∈ closedBall c R) :
    c.re - R ≤ w.re ∧ 1 - c.re - R ≤ 1 - w.re := by
  have hdist : ‖w - c‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hw
  have h := (abs_re_le_norm (w - c)).trans hdist
  rw [sub_re, abs_le] at h
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The absolute theta mass controls the folded integral. The disk's distances
from the edges of the strip bound the separate pole term. -/
def mixedThetaDiskMajorant (K : Type) [Field K] [NumberField K] (c : ℂ) (R : ℝ) : ℝ :=
  2 * (∫ t : ℝ in Ioi 1, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖) +
    ‖(Theta.mixedThetaPair K).f₀‖ / ((c.re - R) * (1 - c.re - R))

theorem mixedThetaCompletedReading_norm_le_on_disk (K : Type) [Field K] [NumberField K]
    {c w : ℂ} {R : ℝ} (hleft : 0 < c.re - R) (hright : 0 < 1 - c.re - R)
    (hw : w ∈ closedBall c R) :
    ‖mixedThetaCompletedReading K w‖ ≤ mixedThetaDiskMajorant K c R := by
  obtain ⟨hlo, hhi⟩ := contour_disk_re_bounds hw
  have hw₀ := hleft.trans_le hlo
  have hw₁ := sub_pos.mp (hright.trans_le hhi)
  have hM := mixedTheta_mellin_tail_le K 1 le_rfl w hw₀.le hw₁.le
  simp only [mixedThetaTruncation, intervalIntegral.integral_same, sub_zero] at hM
  have hd₀ := hlo.trans ((le_abs_self w.re).trans (abs_re_le_norm w))
  have hR₁ : 1 - w.re ≤ ‖1 - w‖ := by
    have habs := abs_re_le_norm (1 - w)
    rw [sub_re, one_re] at habs
    exact (le_abs_self _).trans habs
  have hd : (c.re - R) * (1 - c.re - R) ≤ ‖w * (1 - w)‖ := by
    rw [norm_mul]
    exact mul_le_mul hd₀ (hhi.trans hR₁) hright.le (norm_nonneg _)
  rw [mixedThetaCompletedReading_eq_mellin K w hw₀ hw₁, mixedThetaDiskMajorant]
  refine (norm_sub_le _ _).trans (add_le_add hM ?_)
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hleft hright) hd

/-- The existing circle reconstruction error with the completed mixed-theta
majorant on the outer circle. -/
def mixedThetaContourSampleError (K : Type) [Field K] [NumberField K] (c : ℂ)
    (R h r ε : ℝ) (N n : ℕ) : ℝ :=
  let M := mixedThetaDiskMajorant K c R
  M * (r / R) ^ n / (1 - r / R) +
    (ε + M * (h / R) ^ N / (1 - h / R)) / (1 - r / h)

theorem mixedThetaCompletedReading_sample_error_le (K : Type) [Field K] [NumberField K]
    {c w ω : ℂ} {R : ℝ≥0} {h r ε : ℝ} {N n : ℕ} (samples : ℕ → ℂ)
    (hleft : 0 < c.re - R) (hright : 0 < 1 - c.re - R)
    (hN : 0 < N) (hn : n ≤ N) (hω : IsPrimitiveRoot ω N) (hunit : ‖ω‖ = 1)
    (hr : r < h) (hh : h < (R : ℝ)) (hw : w ∈ closedBall c r)
    (hSamples : ∀ j < N,
      ‖samples j - mixedThetaCompletedReading K (c + (h : ℂ) * ω ^ j)‖ ≤ ε) :
    ‖mixedThetaCompletedReading K w -
        contourSamplePolynomial samples ω N n ((w - c) / (h : ℂ))‖ ≤
      mixedThetaContourSampleError K c R h r ε N n := by
  have hstrip : closedBall c (R : ℝ) ⊆ Complex.re ⁻¹' Ioo (0 : ℝ) 1 := by
    intro z hz
    obtain ⟨h₀, h₁⟩ := contour_disk_re_bounds hz
    exact ⟨hleft.trans_le h₀, sub_pos.mp (hright.trans_le h₁)⟩
  have hx : ‖w - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hw
  have hError := contourSamplePolynomial_error_le
    ((mixedThetaCompletedReading_differentiableOn K).mono hstrip)
    (fun z hz => mixedThetaCompletedReading_norm_le_on_disk K hleft hright
      (sphere_subset_closedBall hz)) hN hn hω hunit hr hh hx hSamples
  simpa only [mixedThetaContourSampleError, add_sub_cancel] using hError

/-- A sampled Dedekind disk can use any independently certified reference
function, with a strict budget for the relative boundary error. -/
theorem mixedThetaContinuation_ne_zero_of_sample_model (K : Type) [Field K] [NumberField K]
    {c w ω : ℂ} {P : ℂ → ℂ} {R : ℝ≥0} {h r ε q : ℝ} {N n : ℕ} (samples : ℕ → ℂ)
    (hleft : 0 < c.re - R) (hright : 0 < 1 - c.re - R)
    (hN : 0 < N) (hn : n ≤ N) (hω : IsPrimitiveRoot ω N) (hunit : ‖ω‖ = 1)
    (hr₀ : 0 < r) (hr : r < h) (hh : h < (R : ℝ)) (hq : q < 1)
    (hSamples : ∀ j < N,
      ‖samples j - mixedThetaCompletedReading K (c + (h : ℂ) * ω ^ j)‖ ≤ ε)
    (hP : DifferentiableOn ℂ P (closedBall c r))
    (hPne : ∀ z ∈ closedBall c r, P z ≠ 0)
    (hBoundary : ∀ z ∈ sphere c r,
      ‖contourSamplePolynomial samples ω N n ((z - c) / (h : ℂ)) - P z‖ +
        mixedThetaContourSampleError K c R h r ε N n ≤ q * ‖P z‖)
    (hw : w ∈ closedBall c r) : mixedThetaContinuation K w ≠ 0 := by
  have hSub : closedBall c r ⊆ Complex.re ⁻¹' Ioo (0 : ℝ) 1 := by
    intro z hz
    have hzR := closedBall_subset_closedBall (hr.trans hh).le hz
    obtain ⟨h₀, h₁⟩ := contour_disk_re_bounds hzR
    exact ⟨hleft.trans_le h₀, sub_pos.mp (hright.trans_le h₁)⟩
  have hF := (mixedThetaCompletedReading_differentiableOn K).mono hSub
  have hError (z : ℂ) (hz : z ∈ sphere c r) :
      ‖mixedThetaCompletedReading K z - P z‖ ≤ q * ‖P z‖ := by
    refine (norm_sub_le_norm_sub_add_norm_sub _
      (contourSamplePolynomial samples ω N n ((z - c) / (h : ℂ))) _).trans ?_
    have he := mixedThetaCompletedReading_sample_error_le K samples hleft hright
      hN hn hω hunit hr hh (sphere_subset_closedBall hz) hSamples
    rw [add_comm]
    exact (add_le_add le_rfl he).trans (hBoundary z hz)
  have hne := contour_ne_zero_of_relative_boundary_error hr₀ hq hF hP hPne hError hw
  exact fun hz => hne ((mixedThetaCompletedReading_zero_iff K w (hSub hw).1 (hSub hw).2).2 hz)

#check @mixedThetaContinuation_ne_zero_of_sample_model
#print axioms contour_model_weight_im_le
#print axioms contour_ne_zero_of_relative_boundary_error
#print axioms mixedThetaCompletedReading_norm_le_on_disk
#print axioms mixedThetaCompletedReading_sample_error_le
#print axioms mixedThetaContinuation_ne_zero_of_sample_model

end

end FieldTarget
