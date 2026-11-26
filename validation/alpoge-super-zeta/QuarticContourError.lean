import WeightedContourTransfer
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCircleArgumentPrinciple
import ArchivedQuarticZeroTransport

/-! Apply Alpöge's full weighted argument principle to a uniform error
bound for the continued Gaussian prime detector. -/
noncomputable section

namespace SuperZeta.WeightedContour

open Complex Metric Set
open scoped Real ComplexConjugate
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

/-- A holomorphic approximation to the continued signed detector gives a
gap test for the exact zero count. The approximation error is measured on
the circle, in the same coordinate as the Gaussian factor. -/
theorem zero_free_of_detector_error {O : Set ℂ} {c : ℂ} {r e : ℝ}
    {G H S P : ℂ → ℂ} (hr : 0 < r) (hO : IsOpen O) (hD : closedBall c r ⊆ O)
    (hg : DifferentiableOn ℂ G O) (hh : DifferentiableOn ℂ H O)
    (hp : DifferentiableOn ℂ P O) (hn : ∀ z ∈ sphere c r, G z ≠ 0)
    (identity : ∀ z ∈ sphere c r, 2*S z*G z = deriv H z*G z - deriv G z)
    (error : ∀ z ∈ sphere c r, ‖S z - P z‖ ≤ e) (small : 2*r*e < 1) :
    ∀ z ∈ closedBall c r, G z ≠ 0 := by
  have hSc : ContinuousOn S (sphere c r) := by
    refine ContinuousOn.congr (f := fun z => (deriv H z - logDeriv G z)/2) ?_ ?_
    · intro z hz
      have hloc := hO.mem_nhds (hD (sphere_subset_closedBall hz))
      have hu := ((hg.deriv hO).differentiableAt hloc).div (hg.differentiableAt hloc) (hn z hz)
      exact (((hh.deriv hO).differentiableAt hloc).sub hu).div_const (2:ℂ)
        |>.continuousAt.continuousWithinAt
    · intro z hz
      have he := (eq_div_iff (hn z hz)).2 (identity z hz)
      rw [sub_div, mul_div_cancel_right₀ _ (hn z hz)] at he
      change S z = (deriv H z - logDeriv G z)/2
      rw [logDeriv_apply]
      linear_combination he / 2
  have hPc : ContinuousOn P (closedBall c r) := hp.continuousOn.mono hD
  have hPcontour : (∮ z in C(c,r), P z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty hPc
      (fun z hz => hp.differentiableAt (hO.mem_nhds (hD (ball_subset_closedBall hz.1))))
  have hsub := circleIntegral.integral_sub (hSc.circleIntegrable hr.le)
    ((hPc.mono sphere_subset_closedBall).circleIntegrable hr.le)
  rw [hPcontour, sub_zero] at hsub
  have hS := moment_from_signed_detector hr.le hO hD (differentiableOn_const (1:ℂ)) hg hh hn identity
  simp only [one_mul] at hS
  have hE := circleIntegral.norm_integral_le_of_norm_le_const hr.le error
  have hscale : ‖-(π * I : ℂ)⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_neg, norm_inv, norm_mul, norm_I, mul_one, norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hM : ‖moment c r G (fun _ => 1)‖ < 1 := by
    rw [hS, ← hsub, norm_mul, hscale]
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left hE (by positivity))
    rwa [show Real.pi⁻¹ * (2*Real.pi*r*e) = 2*r*e by
      field_simp [Real.pi_ne_zero]]
  obtain ⟨Z, u, -, -, hu, hfactor, hmoment⟩ :=
    CircleArgumentPrinciple.proof G O c r hr hO hD hg hn
  have hsum : (Z.map fun _ => (1:ℂ)).sum = (Z.card:ℂ) := by
    induction Z using Multiset.induction_on with
    | empty => simp
    | cons a Z ih =>
      simp [add_comm]
  have hm : moment c r G (fun _ => 1) = (Z.card:ℂ) := by
    rw [← hsum]
    simpa [moment, logDeriv_apply] using hmoment (fun _ => 1) (differentiableOn_const (1:ℂ))
  rw [hm, Complex.norm_natCast] at hM
  have hz : Z.card < 1 := by exact_mod_cast hM
  have hZ : Z = 0 := Multiset.card_eq_zero.mp (by omega)
  intro z hz
  rw [hfactor z (hD hz), hZ]
  simpa using hu z hz

end SuperZeta.WeightedContour

namespace QuarticModel

open Complex Metric Set SuperZeta.WeightedContour
open scoped ComplexConjugate

/-- The exact archived right disk and its same-height mirror. The error
threshold is for the continued detector in the original variable w. -/
theorem archivedRightDisk_exclusion_of_detector_error {T : ℝ} {H S P : ℂ → ℂ}
    (hh : DifferentiableOn ℂ H {w : ℂ | 1/2 < w.re}) (hp : Differentiable ℂ P)
    (hn : ∀ w ∈ sphere (archivedRightCenter T) (31/2048), archivedGaussianFactor w ≠ 0)
    (identity : ∀ w ∈ sphere (archivedRightCenter T) (31/2048),
      2*S w*archivedGaussianFactor w = deriv H w*archivedGaussianFactor w -
        deriv archivedGaussianFactor w)
    {e : ℝ}
    (error : ∀ w ∈ sphere (archivedRightCenter T) (31/2048), ‖S w-P w‖ ≤ e)
    (small : e < 1024/31)
    {w : ℂ} (hw : w ∈ closedBall (archivedRightCenter T) (31/2048)) :
    archivedGaussianFactor w ≠ 0 ∧ archivedGaussianFactor (1-conj w) ≠ 0 := by
  have hsmall : 2*(31/2048:ℝ)*e < 1 := by linarith only [small]
  have hO : IsOpen {w : ℂ | 1/2 < w.re} := isOpen_lt continuous_const continuous_re
  have hD : closedBall (archivedRightCenter T) (31/2048) ⊆ {w : ℂ | 1/2 < w.re} := by
    intro z hz
    change (1/2:ℝ) < z.re
    linarith [archivedRightDisk_horizontal_gap hz]
  have hn' := zero_free_of_detector_error (by norm_num) hO hD
    (archivedGaussianFactor_differentiable archivedTheta_reflection).differentiableOn
    hh hp.differentiableOn hn identity error hsmall w hw
  have hre : 0 < w.re := by linarith [archivedRightDisk_horizontal_gap hw]
  have hupper : w.re < 1 := by
    have h := (abs_re_le_norm (w-archivedRightCenter T)).trans (by
      simpa only [mem_closedBall, dist_eq_norm] using hw)
    have h' := (abs_le.mp h).2
    change w.re-33/64 ≤ 31/2048 at h'
    linarith
  refine ⟨hn', fun hm => ?_⟩
  apply hn'
  apply (archivedGaussianFactor_zero_iff_mellin hre).mpr
  have hmir : 0 < (1-conj w).re := by simp only [sub_re, one_re, conj_re]; linarith
  have hz := (archivedGaussianFactor_zero_iff_mellin hmir).mp hm
  have hc : conj (archivedMellin w) = conj 0 := by
    rw [← archivedMellin_mirror, hz, map_zero]
  exact (starRingEnd ℂ).injective hc

#print axioms GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.CircleArgumentPrinciple.proof
#print axioms zero_free_of_detector_error
#print axioms archivedRightDisk_exclusion_of_detector_error
#check archivedRightDisk_exclusion_of_detector_error

end QuarticModel
end
