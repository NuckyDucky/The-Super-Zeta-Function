import DottieRationalWeightBounds
import DedekindWeightedDottieSamples
import DedekindMixedThetaSampleModel

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex MeasureTheory Metric Set
open DedekindZetaZeroFree.AbelianQuotient SuperZeta.StirlingCorrection

noncomputable section

/-- Place the outer disk halfway from the measuring circumference to the
next scaled horizontal edge. This radius stays in the strip at every scale. -/
def dottieWeightOuterRadius (n : ℕ) : ℝ := (63 / 4096) * dottieRingScale n

theorem dottieWeightOuterRadius_geometry (T : ℝ) (n : ℕ) :
    dottieScaledRadius n < dottieWeightOuterRadius n ∧
    0 < (dottieScaledRightCenter T n).re - dottieWeightOuterRadius n ∧
    0 < 1 - (dottieScaledRightCenter T n).re - dottieWeightOuterRadius n := by
  have hs := dottieRingScale_pos n
  have hsMax : dottieRingScale n ≤ 16 := by
    have h : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    unfold dottieRingScale
    linarith only [h]
  change (31 / 2048) * dottieRingScale n < (63 / 4096) * dottieRingScale n ∧
    0 < (1 / 2 + dottieRingScale n / 64) - (63 / 4096) * dottieRingScale n ∧
    0 < 1 - (1 / 2 + dottieRingScale n / 64) - (63 / 4096) * dottieRingScale n
  exact ⟨by linarith only [hs], by linarith only [hs], by linarith only [hsMax]⟩

/-- The real coordinate and the outer radius are independent of the reference
height, so the theta mass and pole bound are reusable across heights. -/
def mixedThetaDottieOuterMajorant (K : Type) [Field K] [NumberField K] (n : ℕ) : ℝ :=
  mixedThetaDiskMajorant K (dottieScaledRightCenter 0 n) (dottieWeightOuterRadius n)

theorem norm_mixedThetaCompletedReading_le_on_dottie_weight_disk
    (K : Type) [Field K] [NumberField K] {T : ℝ} {n : ℕ} {w : ℂ}
    (hw : w ∈ closedBall (dottieScaledRightCenter T n) (dottieWeightOuterRadius n)) :
    ‖mixedThetaCompletedReading K w‖ ≤ mixedThetaDottieOuterMajorant K n := by
  obtain ⟨_, hl, hu⟩ := dottieWeightOuterRadius_geometry T n
  exact mixedThetaCompletedReading_norm_le_on_disk K (c := dottieScaledRightCenter T n) hl hu hw

/-- Use the field norm bound on the outer disk, a Mellin tail bound, and
enclosed values of the finite Mellin reading to certify the measuring disk.
The coefficient bound pays for motion between samples, and the two sample
errors are multiplied by the absolute real and imaginary parts of the weight. -/
theorem dottie_weighted_certificate_of_enclosures
    (K : Type) [Field K] [NumberField K] {T cutoff B tail margin : ℝ} {n m N : ℕ}
    (a : Fin N → ℚ × ℚ) (value : ℂ → ℕ → ℂ) (error : ℂ → ℕ → ℝ)
    (hcut : 1 ≤ cutoff) (hm : 0 < m) (hmargin : 0 < margin)
    (hBound : ∀ v ∈ closedBall (dottieScaledRightCenter T n) (dottieWeightOuterRadius n),
      ‖mixedThetaCompletedReading K v‖ ≤ B)
    (hTail : 2 * ∫ t : ℝ in Ioi cutoff, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖
      ≤ tail)
    (hError : ∀ q ∈ contourQuarterTurns, ∀ j ≤ m,
      let v := rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) q m j
      ‖mixedThetaCompletedTruncation K cutoff v - value q j‖ ≤ error q j)
    (hSign : ∀ q ∈ contourQuarterTurns, ∀ j ≤ m,
      let v := rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) q m j
      let Wv := dottieRationalWeight (dottieScaledRightCenter T n) a v
      (Wv * value q j).im + 124 * dottieWeightCoefficientBound a (dottieWeightOuterRadius n) * B / m +
        (|Wv.re| + |Wv.im|) * (error q j + tail) ≤ -margin) :
    IsDottieCompletedWeightedSampleCertificate K T n (dottieRationalWeight (dottieScaledRightCenter T n) a) := by
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  let ρ := dottieWeightOuterRadius n
  let F := mixedThetaCompletedReading K
  let W := dottieRationalWeight c a
  let C := dottieWeightCoefficientBound a ρ
  let M := C * B / (ρ - r)
  let S := Complex.re ⁻¹' Ioo (0 : ℝ) 1
  have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
  obtain ⟨hrρ, hleft, hright⟩ := dottieWeightOuterRadius_geometry T n
  have hρ : 0 ≤ ρ := hr.le.trans hrρ.le
  have hPositiveB : 0 ≤ B := (norm_nonneg _).trans (hBound c (mem_closedBall_self hρ))
  have hOuter : closedBall c ρ ⊆ S := by
    intro z hz
    have hDist : ‖z - c‖ ≤ ρ := (dist_eq_norm z c) ▸ mem_closedBall.mp hz
    have hRe := abs_le.mp ((Complex.abs_re_le_norm (z - c)).trans hDist)
    change 0 < z.re ∧ z.re < 1
    rw [sub_re] at hRe
    exact ⟨by linarith only [hleft, hRe.1], by linarith only [hright, hRe.2]⟩
  have hS : IsOpen S := continuous_re.isOpen_preimage _ isOpen_Ioo
  have hF : DifferentiableOn ℂ F S := mixedThetaCompletedReading_differentiableOn K
  have hWF : DifferentiableOn ℂ (W * F) S :=
    (dottieRationalWeight_differentiable c a).differentiableOn.mul hF
  have hAt (z : ℂ) (hz : z ∈ closedBall c r) : DifferentiableAt ℂ (W * F) z := by
    have hzS := hOuter (closedBall_subset_closedBall hrρ.le hz)
    exact (hWF z hzS).differentiableAt (hS.mem_nhds hzS)
  have hDeriv (z : ℂ) (hz : z ∈ closedBall c r) : ‖deriv (W * F) z‖ ≤ M :=
    norm_deriv_dottieRationalWeight_mul_le a hr.le hrρ (hF.mono hOuter) hBound hz
  have hM : 0 ≤ M := div_nonneg (mul_nonneg (dottieWeightCoefficientBound_nonneg a hρ) hPositiveB)
    (sub_nonneg.mpr hrρ.le)
  have hMesh : M * (2 * r / (m : ℝ)) = 124 * C * B / m := by
    have hWidth : 2 * r = 124 * (ρ - r) := by
      dsimp [r, ρ, dottieScaledRadius, dottieWeightOuterRadius]
      ring
    have hd : ρ - r ≠ 0 := (sub_pos.mpr hrρ).ne'
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    change C * B / (ρ - r) * (2 * r / (m : ℝ)) = _
    rw [hWidth]
    field_simp [hd, hmreal]
  have hNonnegTail : 0 ≤ tail := (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    (integral_nonneg (fun _ ↦ norm_nonneg _))).trans hTail
  refine ⟨cutoff, M, margin, tail, m, hcut, hm, hM, hmargin, hAt, hDeriv, hTail, ?_⟩
  intro q hq j hj
  let v := rationalContourSample c r q m j
  have hErrV : ‖mixedThetaCompletedTruncation K cutoff v - value q j‖ ≤ error q j :=
    hError q hq j hj
  have hErrNonneg := (norm_nonneg _).trans hErrV
  have hSignedError : (W v * mixedThetaCompletedTruncation K cutoff v).im -
      (W v * value q j).im ≤ ‖W v‖ * error q j := by
    rw [← sub_im, ← mul_sub]
    refine (le_abs_self _).trans ((abs_im_le_norm _).trans ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left hErrV (norm_nonneg _)
  have hSum := mul_le_mul_of_nonneg_right (norm_le_abs_re_add_abs_im (W v))
    (add_nonneg hErrNonneg hNonnegTail)
  rw [mul_add ‖W v‖] at hSum
  have hSignV : (W v * value q j).im + 124 * C * B / m +
      (|(W v).re| + |(W v).im|) * (error q j + tail) ≤ -margin := hSign q hq j hj
  change (W v * mixedThetaCompletedTruncation K cutoff v).im +
    M * (2 * r / (m : ℝ)) + ‖W v‖ * tail ≤ -margin
  rw [hMesh]
  linarith only [hSignedError, hSum, hSignV]

#check @dottie_weighted_certificate_of_enclosures
#print axioms dottieWeightOuterRadius_geometry
#print axioms norm_mixedThetaCompletedReading_le_on_dottie_weight_disk
#print axioms dottie_weighted_certificate_of_enclosures

end
end FieldTarget
