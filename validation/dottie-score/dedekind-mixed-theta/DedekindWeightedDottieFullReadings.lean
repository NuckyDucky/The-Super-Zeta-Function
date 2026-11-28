import DedekindWeightedDottieEnclosures
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Filter MeasureTheory Metric Set
open DedekindZetaZeroFree.AbelianQuotient SuperZeta.StirlingCorrection

set_option maxHeartbeats 1000000 in
/-- A strict weighted test of independently enclosed completed readings
produces a truncated Mellin certificate. The cutoff is chosen afterwards. -/
theorem dottie_weighted_certificate_of_completed_enclosures
    (K : Type) [Field K] [NumberField K] {T B margin : ℝ} {n m N : ℕ}
    (a : Fin N → ℚ × ℚ) (value : ℂ → ℕ → ℂ) (error : ℂ → ℕ → ℝ)
    (hm : 0 < m) (hmargin : 0 < margin)
    (hBound : ∀ v ∈ closedBall (dottieScaledRightCenter T n) (dottieWeightOuterRadius n),
      ‖mixedThetaCompletedReading K v‖ ≤ B)
    (hError : ∀ q ∈ contourQuarterTurns, ∀ j ≤ m,
      let v := rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) q m j
      ‖mixedThetaCompletedReading K v - value q j‖ ≤ error q j)
    (hSign : ∀ q ∈ contourQuarterTurns, ∀ j ≤ m,
      let v := rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) q m j
      let Wv := dottieRationalWeight (dottieScaledRightCenter T n) a v
      (Wv * value q j).im + 124 * dottieWeightCoefficientBound a (dottieWeightOuterRadius n) * B / m +
        (|Wv.re| + |Wv.im|) * error q j ≤ -margin) :
    IsDottieCompletedWeightedSampleCertificate K T n
      (dottieRationalWeight (dottieScaledRightCenter T n) a) := by
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  let W := dottieRationalWeight c a
  let H := max 1 (2 * dottieWeightCoefficientBound a r)
  let τ := margin / (4 * H)
  have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
  have hH : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  have hτ : 0 < τ := div_pos hmargin (mul_pos (by norm_num) hH)
  let tail (s : ℝ) := 2 * ∫ t : ℝ in Ioi s,
    ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖
  have hlim : Tendsto tail atTop (nhds 0) := by
    have h := tendsto_integral_Ioi_zero
      (f := fun t : ℝ ↦ ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖)
      (μ := volume) (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop)
    simpa only [tail, id_eq, mul_zero] using h.const_mul (2 : ℝ)
  obtain ⟨s, hs, hTail⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (hlim.eventually (gt_mem_nhds hτ))).exists
  refine dottie_weighted_certificate_of_enclosures a value (fun q j ↦ error q j + τ)
    (cutoff := s) (B := B) (tail := τ) (margin := margin / 2)
    (K := K) hs hm (by positivity) hBound hTail.le ?_ ?_
  · intro q hq j hj
    let v := rationalContourSample c r q m j
    have hv : v ∈ closedBall c r := sphere_subset_closedBall (rationalContourSample_mem_sphere hr hq)
    have hS := dottieScaledRightDisk_strip hv
    have hv₀ : 0 < v.re := (by norm_num : (0 : ℝ) < 1 / 2).trans hS.1
    have hCut := (mixedThetaCompletedTruncation_error_le K s hs v hv₀ hS.2).trans hTail.le
    rw [norm_sub_rev] at hCut
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add hCut (hError q hq j hj)).trans_eq (add_comm _ _))
  · intro q hq j hj
    let v := rationalContourSample c r q m j
    have hv : v ∈ closedBall c r := sphere_subset_closedBall (rationalContourSample_mem_sphere hr hq)
    have hAbs : |(W v).re| + |(W v).im| ≤ H := by
      calc
        _ ≤ 2 * ‖W v‖ := by linarith only [abs_re_le_norm (W v), abs_im_le_norm (W v)]
        _ ≤ 2 * dottieWeightCoefficientBound a r :=
          mul_le_mul_of_nonneg_left (norm_dottieRationalWeight_le a hv) (by norm_num)
        _ ≤ H := le_max_right _ _
    have hPenalty : (|(W v).re| + |(W v).im|) * (2 * τ) ≤ margin / 2 := by
      refine (mul_le_mul_of_nonneg_right hAbs (by positivity)).trans_eq ?_
      change H * (2 * (margin / (4 * H))) = margin / 2
      field_simp [hH.ne']
      norm_num
    have hSignV := hSign q hq j hj
    change (W v * value q j).im + 124 * dottieWeightCoefficientBound a (dottieWeightOuterRadius n) * B / m +
      (|(W v).re| + |(W v).im|) * error q j ≤ -margin at hSignV
    change (W v * value q j).im + 124 * dottieWeightCoefficientBound a (dottieWeightOuterRadius n) * B / m +
      (|(W v).re| + |(W v).im|) * (error q j + τ + τ) ≤ -(margin / 2)
    rw [show error q j + τ + τ = error q j + 2 * τ by ring, mul_add]
    linarith only [hSignV, hPenalty]

/-- A single enclosure for a model polynomial supplies all the completed
sample values. A coefficient bound on the weighted model residual supplies
the sign tests for the entire mesh. -/
theorem dottie_weighted_certificate_of_uniform_model
    (K : Type) [Field K] [NumberField K] {T B C E D margin : ℝ} {n m N : ℕ}
    (a : Fin N → ℚ × ℚ) (P : ℂ → ℂ) (hm : 0 < m) (hmargin : 0 < margin)
    (hBound : ∀ z ∈ closedBall (dottieScaledRightCenter T n) (dottieWeightOuterRadius n),
      ‖mixedThetaCompletedReading K z‖ ≤ B)
    (hCoeff : dottieWeightCoefficientBound a (dottieWeightOuterRadius n) ≤ C)
    (hError : ∀ z ∈ closedBall (dottieScaledRightCenter T n) (dottieWeightOuterRadius n),
      ‖mixedThetaCompletedReading K z - P z‖ ≤ E)
    (hResidual : ∀ z ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n),
      ‖dottieRationalWeight (dottieScaledRightCenter T n) a z * P z + I‖ ≤ D)
    (hBudget : D + 124 * C * B / m + 2 * C * E ≤ 1 - margin) :
    IsDottieCompletedWeightedSampleCertificate K T n
      (dottieRationalWeight (dottieScaledRightCenter T n) a) := by
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  let ρ := dottieWeightOuterRadius n
  let W := dottieRationalWeight c a
  have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
  have hrρ : r < ρ := (dottieWeightOuterRadius_geometry T n).1
  have hc : c ∈ closedBall c ρ := mem_closedBall_self (hr.le.trans hrρ.le)
  have hB : 0 ≤ B := (norm_nonneg _).trans (hBound c hc)
  have hE : 0 ≤ E := (norm_nonneg _).trans (hError c hc)
  have hMesh : 124 * dottieWeightCoefficientBound a ρ * B / (m : ℝ) ≤ 124 * C * B / m :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCoeff (by norm_num)) hB)
      (by positivity)
  refine dottie_weighted_certificate_of_completed_enclosures K a
    (fun q j ↦ P (rationalContourSample c r q m j)) (fun _ _ ↦ E) hm hmargin hBound ?_ ?_
  · intro q hq j _
    exact hError _ (closedBall_subset_closedBall hrρ.le
      (sphere_subset_closedBall (rationalContourSample_mem_sphere hr hq)))
  · intro q hq j _
    let v := rationalContourSample c r q m j
    have hv : v ∈ closedBall c r := sphere_subset_closedBall (rationalContourSample_mem_sphere hr hq)
    have hW := (norm_dottieRationalWeight_le a (closedBall_subset_closedBall hrρ.le hv)).trans hCoeff
    have hAbs : |(W v).re| + |(W v).im| ≤ 2 * C := by
      linarith only [hW, abs_im_le_norm (W v), abs_re_le_norm (W v)]
    have hLocal := mul_le_mul_of_nonneg_right hAbs hE
    have hIm := (le_abs_self (W v * P v + I).im).trans
      ((abs_im_le_norm _).trans (hResidual v hv))
    rw [add_im, I_im] at hIm
    change (W v * P v).im + 124 * dottieWeightCoefficientBound a ρ * B / m +
      (|(W v).re| + |(W v).im|) * E ≤ -margin
    linarith only [hIm, hMesh, hLocal, hBudget]

#print axioms dottie_weighted_certificate_of_completed_enclosures
#print axioms dottie_weighted_certificate_of_uniform_model

end FieldTarget
