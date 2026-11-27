import DedekindMixedThetaCompletedRings
import DedekindMixedThetaDerivative
import ContourTaylor
import MellinFixedPolynomialDisk

/-! An explicit Taylor error for the actual completed Dedekind reading on
a disk whose outer circle stays in the critical strip. -/

namespace FieldTarget

open Complex Metric Set
open DedekindZetaZeroFree.AbelianQuotient
open DottieOriented.NativeSpectrum.MellinFixed
open scoped BigOperators Interval NNReal

noncomputable section

private theorem closedBall_re_inside {c w : ℂ} {ρ : ℝ} (hLeft : ρ < c.re)
    (hRight : ρ < 1 - c.re) (hw : w ∈ closedBall c ρ) : 0 < w.re ∧ w.re < 1 := by
  have hd := mem_closedBall.mp hw
  rw [dist_eq_norm] at hd
  have hx := abs_le.mp ((Complex.abs_re_le_norm (w - c)).trans hd)
  rw [Complex.sub_re] at hx
  exact ⟨by linarith only [hx.1, hLeft], by linarith only [hx.2, hRight]⟩

/-- The norm allowance on an outer circle. The pole term uses distances
from the center to zero and one. -/
def mixedThetaCompletedCircleAllowance (K : Type) [Field K] [NumberField K]
    (cut : ℝ) (c : ℂ) (ρ : ℝ) : ℝ :=
  mixedThetaWeightedTail K 1 0 + mixedThetaWeightedTail K cut 0 +
    ‖(Theta.mixedThetaPair K).f₀‖ / ((‖c‖ - ρ) * (‖1 - c‖ - ρ))

private theorem pole_norm_le_of_radius (a : ℂ) {c w : ℂ} {ρ : ℝ}
    (hLeft : ρ < c.re) (hRight : ρ < 1 - c.re) (hd : ‖w - c‖ ≤ ρ) :
    ‖a / (w * (1 - w))‖ ≤ ‖a‖ / ((‖c‖ - ρ) * (‖1 - c‖ - ρ)) := by
  have hNorm₀ : c.re ≤ ‖c‖ := (le_abs_self _).trans (Complex.abs_re_le_norm c)
  have hNorm₁ : 1 - c.re ≤ ‖1 - c‖ := by
    simpa only [Complex.sub_re, Complex.one_re] using
      (le_abs_self (1 - c).re).trans (Complex.abs_re_le_norm (1 - c))
  have hp₀ : 0 < ‖c‖ - ρ := by linarith only [hLeft, hNorm₀]
  have hp₁ : 0 < ‖1 - c‖ - ρ := by linarith only [hRight, hNorm₁]
  have h₀ : ‖c‖ - ρ ≤ ‖w‖ := by
    have h := norm_sub_le w (w - c)
    rw [show w - (w - c) = c by ring] at h
    linarith only [h, hd]
  have h₁ : ‖1 - c‖ - ρ ≤ ‖1 - w‖ := by
    have h := norm_add_le (1 - w) (w - c)
    rw [show 1 - w + (w - c) = 1 - c by ring] at h
    linarith only [h, hd]
  rw [norm_div, norm_mul]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hp₀ hp₁)
    (mul_le_mul h₀ h₁ hp₁.le (norm_nonneg _))

theorem mixedThetaCompletedTruncation_norm_le_circleAllowance (K : Type)
    [Field K] [NumberField K] {cut ρ : ℝ} {c w : ℂ}
    (hcut : 1 ≤ cut) (hLeft : ρ < c.re) (hRight : ρ < 1 - c.re) (hw : w ∈ closedBall c ρ) :
    ‖mixedThetaCompletedTruncation K cut w‖ ≤ mixedThetaCompletedCircleAllowance K cut c ρ := by
  obtain ⟨hlo, hhi⟩ := closedBall_re_inside hLeft hRight hw
  have hl : -(0 : ℝ) ≤ w.re := by simpa only [neg_zero] using hlo.le
  have hh : w.re ≤ 1 + (0 : ℝ) := by simpa only [add_zero] using hhi.le
  have hWhole := mixedTheta_mellin_error_le_wide K (R := 1) (ρ := 0) le_rfl w hl hh
  have hAtOne : mixedThetaTruncation K 1 w = 0 := by simp [mixedThetaTruncation]
  rw [hAtOne, sub_zero] at hWhole
  have hTail := mixedTheta_mellin_error_le_wide K hcut w hl hh
  have hTrunc : ‖mixedThetaTruncation K cut w‖ ≤
      mixedThetaWeightedTail K 1 0 + mixedThetaWeightedTail K cut 0 := by
    let full := (Theta.mixedThetaPair K).Λ₀ w
    let part := mixedThetaTruncation K cut w
    calc
      _ = ‖full + (part - full)‖ := by rw [show full + (part - full) = part by ring]
      _ ≤ ‖full‖ + ‖part - full‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hWhole (by rw [norm_sub_rev]; exact hTail)
  have hd := mem_closedBall.mp hw
  rw [dist_eq_norm] at hd
  exact (norm_sub_le _ _).trans
    (add_le_add hTrunc (pole_norm_le_of_radius (Theta.mixedThetaPair K).f₀ hLeft hRight hd))

private theorem pole_denominator_ne_zero {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) :
    w * (1 - w) ≠ 0 := by
  have hw₀ : w ≠ 0 := by rintro rfl; norm_num at hlo
  have hw₁ : w ≠ 1 := by rintro rfl; norm_num at hhi
  exact mul_ne_zero hw₀ (sub_ne_zero.mpr hw₁.symm)

theorem mixedThetaCompletedTruncation_differentiableOn_strip (K : Type)
    [Field K] [NumberField K] {cut : ℝ} (hcut : 1 ≤ cut) :
    DifferentiableOn ℂ (mixedThetaCompletedTruncation K cut) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
  have hden : Differentiable ℂ (fun w : ℂ ↦ w * (1 - w)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  apply (mixedThetaTruncation_differentiable K hcut).differentiableOn.sub
  exact (differentiable_const (Theta.mixedThetaPair K).f₀).differentiableOn.div hden.differentiableOn
    (fun _ hw ↦ pole_denominator_ne_zero hw.1 hw.2)

theorem mixedThetaCompletedTruncation_differentiableOn_disk (K : Type)
    [Field K] [NumberField K] {cut ρ : ℝ} {c : ℂ} (hcut : 1 ≤ cut)
    (hLeft : ρ < c.re) (hRight : ρ < 1 - c.re) :
    DifferentiableOn ℂ (mixedThetaCompletedTruncation K cut) (closedBall c ρ) :=
  (mixedThetaCompletedTruncation_differentiableOn_strip K hcut).mono
    (fun _ hw ↦ closedBall_re_inside hLeft hRight hw)

def mixedThetaCompletedTaylorAllowance (K : Type) [Field K] [NumberField K]
    (cut : ℝ) (c : ℂ) (ρ r : ℝ) (n : ℕ) : ℝ :=
  mixedThetaWeightedTail K cut 0 +
    mixedThetaCompletedCircleAllowance K cut c ρ * (r / ρ) ^ n / (1 - r / ρ)

/-- Take the Taylor coefficients from the finite, pole-adjusted Mellin
reading. The total error is the radial tail plus the geometric Taylor tail. -/
theorem mixedTheta_completed_disk_taylor_error_le (K : Type) [Field K] [NumberField K]
    {cut r : ℝ} {ρ : ℝ≥0} {c z : ℂ} (hcut : 1 ≤ cut)
    (hLeft : (ρ : ℝ) < c.re) (hRight : (ρ : ℝ) < 1 - c.re)
    (hr : r < (ρ : ℝ)) (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖mixedThetaCompletedReading K (c + z) -
      ∑ k ∈ Finset.range n, contourTaylorCoeff (mixedThetaCompletedTruncation K cut) c ρ k * z ^ k‖ ≤
      mixedThetaCompletedTaylorAllowance K cut c ρ r n := by
  have hF := mixedThetaCompletedTruncation_differentiableOn_disk K hcut hLeft hRight
  have hP := contourTaylor_tail_le hF (fun w hw ↦
      mixedThetaCompletedTruncation_norm_le_circleAllowance K hcut hLeft hRight
        (sphere_subset_closedBall hw)) hr hz n
  have hw : c + z ∈ closedBall c (ρ : ℝ) := by
    rw [mem_closedBall, dist_eq_norm, show c + z - c = z by ring]
    exact hz.trans hr.le
  obtain ⟨hlo, hhi⟩ := closedBall_re_inside hLeft hRight hw
  have hT : ‖mixedThetaCompletedReading K (c + z) - mixedThetaCompletedTruncation K cut (c + z)‖ ≤
      mixedThetaWeightedTail K cut 0 := by
    rw [mixedThetaCompletedReading_eq_mellin K _ hlo hhi, mixedThetaCompletedTruncation,
      sub_sub_sub_cancel_right]
    exact mixedTheta_mellin_error_le_wide K hcut _
      (by simpa only [neg_zero] using hlo.le) (by simpa only [add_zero] using hhi.le)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (mixedThetaCompletedTruncation K cut (c + z)) _).trans
    (add_le_add hT hP)

/-- Supply checked coefficient boxes and integer budgets on a rational
disk to get a certificate for the actual completed field reading. -/
def mixedTheta_polynomialDiskCertificate (K : Type) [Field K] [NumberField K]
    {cut : ℝ} {ρ : ℝ≥0} {c direction : ℂ} {p q n : ℕ} {approximation tail : ℤ}
    (hcut : 1 ≤ cut) (hLeft : (ρ : ℝ) < c.re) (hRight : (ρ : ℝ) < 1 - c.re)
    (hq : 0 < q) (hn : 1 ≤ n) (hr : (p : ℝ) / (q : ℝ) < ρ) (hDir : ‖direction‖ = 1)
    (boxes : ℕ → ComplexBox)
    (hBoxes : ∀ k < n, ComplexBox.Contains (boxes k)
      (direction * contourTaylorCoeff (mixedThetaCompletedTruncation K cut) c ρ k))
    (hApprox : mixedThetaCompletedTaylorAllowance K cut c ρ ((p : ℝ) / (q : ℝ)) n ≤
      (approximation : ℝ) / (scale : ℝ))
    (hTail : ComplexBox.weightedTailMass boxes p q 1 n ≤ tail * (q : ℤ) ^ n)
    (hMargin : approximation + tail < (boxes 0).re.lo) :
    PolynomialDiskCertificate (mixedThetaCompletedReading K) c p q where
  denominator_pos := hq
  terms := n
  terms_pos := hn
  direction := direction
  coefficient k := direction * contourTaylorCoeff (mixedThetaCompletedTruncation K cut) c ρ k
  boxes := boxes
  enclosure := hBoxes
  approximationBudget := approximation
  tailBudget := tail
  weighted_tail := hTail
  margin := hMargin
  approximation z hz := by
    let a := contourTaylorCoeff (mixedThetaCompletedTruncation K cut) c ρ
    change ‖direction * mixedThetaCompletedReading K (c + z) -
      ∑ k ∈ Finset.range n, (direction * a k) * z ^ k‖ ≤ _
    simp only [mul_assoc, ← Finset.mul_sum, ← mul_sub, norm_mul, hDir, one_mul]
    exact (mixedTheta_completed_disk_taylor_error_le K hcut hLeft hRight hr hz n).trans hApprox

#check @mixedTheta_polynomialDiskCertificate
#print axioms mixedThetaCompletedTruncation_norm_le_circleAllowance
#print axioms mixedTheta_completed_disk_taylor_error_le
#print axioms mixedTheta_polynomialDiskCertificate

end

end FieldTarget
