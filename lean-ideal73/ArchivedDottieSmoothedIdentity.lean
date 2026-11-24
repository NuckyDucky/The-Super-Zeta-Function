import ArchivedDottieContourShift
import ArchivedGaussianStripBound
import ArchivedQuarticOrders

/-! The exact two-sided smoothed identity used in the Dottie circle
calculation, with the same field, coefficients, weights, and normalization. -/

open Complex Filter MeasureTheory Set
open scoped ComplexConjugate Topology

namespace QuarticModel

open SuperZeta.StirlingCorrection
open private verticalPoint horizontalPoint verticalPoint_ne_zero from ArchivedDottieContourShift
open private dottieContour from ArchivedDottieTailPartition

private noncomputable def tilt (z : ℂ) : ℂ :=
  Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)

private noncomputable def contourNumerator (w z : ℂ) : ℂ := archivedMellin (w+z) * tilt z

private theorem contourNumerator_differentiable (w : ℂ) :
    Differentiable ℂ (contourNumerator w) := by
  unfold contourNumerator
  exact ((archivedMellin_differentiable archivedTheta_reflection).comp
    ((differentiable_const w).add differentiable_id)).mul (by unfold tilt; fun_prop)

private theorem contourNumerator_bound {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ z : ℂ, |z.re| ≤ 1 →
      ‖contourNumerator w z‖ ≤ D * Real.exp (-(1/2 : ℝ)*z.im^2) := by
  obtain ⟨C, hC, hm⟩ := archivedMellin_strip_bound
  refine ⟨C*Real.exp (1+Real.pi^2/8), by positivity, ?_⟩
  intro z hz
  have hz' := abs_le.mp hz
  have hr : |(w+z).re-1/2| ≤ 2 := by
    rw [add_re]
    exact abs_le.mpr ⟨by linarith [hz'.1], by linarith [hz'.2]⟩
  have hs : z.re^2 ≤ 1 := by
    have := sq_le_sq₀ (abs_nonneg z.re) (by norm_num : (0 : ℝ) ≤ 1) |>.mpr hz
    simpa only [sq_abs, one_pow] using this
  have hTilt : ‖tilt z‖ ≤ Real.exp (1+Real.pi^2/8) * Real.exp (-(1/2 : ℝ)*z.im^2) := by
    rw [tilt, Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
    have hRe : (z^2-I*(Real.pi : ℂ)*z/2).re = z.re^2-z.im^2+Real.pi*z.im/2 := by
      simp [pow_two, Complex.mul_re, Complex.mul_im]
      ring
    rw [hRe]
    nlinarith only [hs, sq_nonneg (z.im-Real.pi/2)]
  rw [contourNumerator, norm_mul, mul_assoc]
  exact mul_le_mul (hm _ hr) hTilt (norm_nonneg _) hC

private theorem dottieVertical_integrable {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1)
    {c : ℝ} (hc : |c| = 1) :
    Integrable (fun t => contourNumerator w (verticalPoint c t) / verticalPoint c t) := by
  obtain ⟨D, hD, hbound⟩ := contourNumerator_bound hw₀ hw₁
  have hInt := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).const_mul D
  refine hInt.mono' ?_ (Eventually.of_forall fun t => ?_)
  · have hp : Continuous (verticalPoint c) := by unfold verticalPoint; fun_prop
    have hcNe : c ≠ 0 := by intro hz; simp [hz] at hc
    exact (((contourNumerator_differentiable w).continuous.comp hp).div hp
      (verticalPoint_ne_zero hcNe)).aestronglyMeasurable
  · let z := verticalPoint c t
    have hRe : z.re = c := by simp [z, verticalPoint, Complex.mul_re]
    have hIm : z.im = t := by simp [z, verticalPoint, Complex.mul_im]
    have hn : 1 ≤ ‖z‖ := by simpa only [hRe,hc] using abs_re_le_norm z
    change ‖contourNumerator w z / z‖ ≤ _
    rw [norm_div]
    exact (div_le_self (norm_nonneg _) hn).trans (by
      simpa only [hIm] using hbound z (by rw [hRe,hc]))

private theorem dottieHorizontal_decay {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1)
    {direction : ℝ} (hd : |direction| = 1) :
    Tendsto (fun T => ∫ x in (-1 : ℝ)..1,
      dslope (contourNumerator w) 0 (horizontalPoint (direction*T) x)) atTop (𝓝 0) := by
  obtain ⟨D,hD,hbound⟩ := contourNumerator_bound hw₀ hw₁
  let C := D+‖contourNumerator w 0‖
  have hC : 0 ≤ C := by unfold C; positivity
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (h := fun T : ℝ => 2*C/T)
    tendsto_const_nhds ?_
    (Eventually.of_forall fun _ => norm_nonneg _) ?_
  · have hc := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (2*C)
    simpa only [mul_zero, ← div_eq_mul_inv] using hc
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hTpos : 0 < T := zero_lt_one.trans_le hT
    have hmag := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := (1 : ℝ)) (C := C/T)
      (f := fun x => dslope (contourNumerator w) 0 (horizontalPoint (direction*T) x)) ?_
    · have he : (C/T)*|(1 : ℝ)-(-1)| = 2*C/T := by
        rw [show |(1 : ℝ)-(-1)| = 2 by norm_num]
        ring
      rw [he] at hmag
      exact hmag
    · intro x hx
      rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      let z := horizontalPoint (direction*T) x
      have hRe : z.re = x := by simp [z, horizontalPoint, Complex.mul_re]
      have hIm : z.im = direction*T := by simp [z, horizontalPoint, Complex.mul_im]
      have hAbs : |z.re| ≤ 1 := by rw [hRe]; exact abs_le.mpr ⟨hx.1.le,hx.2⟩
      have hn : T ≤ ‖z‖ := by
        simpa only [hIm,abs_mul,hd,one_mul,abs_of_pos hTpos] using abs_im_le_norm z
      have hz : z ≠ 0 := norm_pos_iff.mp (hTpos.trans_le hn)
      have hu : ‖contourNumerator w z‖ ≤ D := by
        refine (hbound z hAbs).trans ?_
        exact mul_le_of_le_one_right hD (Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg _)))
      change ‖dslope (contourNumerator w) 0 z‖ ≤ C/T
      rw [dslope_of_ne _ hz, slope_def_field, sub_zero, norm_div]
      apply (div_le_div_of_nonneg_right (norm_sub_le _ _) (norm_nonneg z)).trans
      have hSum : ‖contourNumerator w z‖ + ‖contourNumerator w 0‖ ≤ C := by
        unfold C
        linarith
      exact (div_le_div_of_nonneg_right hSum (norm_nonneg z)).trans
        (div_le_div_of_nonneg_left hC hTpos hn)

private theorem contourNumerator_reflect (w : ℂ) (u : ℝ) :
    contourNumerator w (verticalPoint (-1) u) / verticalPoint (-1) u =
      -conj (contourNumerator (1-conj w) (verticalPoint 1 u) / verticalPoint 1 u) := by
  have hz : verticalPoint (-1) u = -conj (verticalPoint 1 u) := by
    simp [verticalPoint, map_mul, conj_I]
    ring
  have hw : w+verticalPoint (-1) u = 1-conj ((1-conj w)+verticalPoint 1 u) := by
    rw [hz, map_add, map_sub, map_one, conj_conj]
    ring
  have ht : tilt (verticalPoint (-1) u) = conj (tilt (verticalPoint 1 u)) := by
    rw [hz, tilt, tilt, ← Complex.exp_conj]
    congr 1
    simp only [map_sub, map_div₀, map_mul, map_pow, conj_I, map_ofNat,
      conj_ofReal, neg_sq]
    ring
  rw [contourNumerator, hw, archivedMellin_mirror, ht, hz]
  simp only [contourNumerator, map_div₀, map_mul, div_neg]

private theorem dottiePairedRawContours {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    (∫ u : ℝ, contourNumerator w (verticalPoint 1 u)/verticalPoint 1 u) +
      conj (∫ u : ℝ, contourNumerator (1-conj w) (verticalPoint 1 u)/verticalPoint 1 u) =
        2*(Real.pi : ℂ)*archivedMellin w := by
  have h := shift_vertical_one_of_decay (contourNumerator w)
    (contourNumerator_differentiable w)
    (dottieVertical_integrable hw₀ hw₁ (by norm_num))
    (dottieVertical_integrable hw₀ hw₁ (by norm_num))
    (by simpa only [neg_one_mul] using (dottieHorizontal_decay hw₀ hw₁ (direction := -1) (by norm_num)))
    (by simpa only [one_mul] using (dottieHorizontal_decay hw₀ hw₁ (direction := 1) (by norm_num)))
  simp_rw [contourNumerator_reflect w] at h
  rw [integral_neg, integral_conj, sub_neg_eq_add] at h
  simpa [contourNumerator, tilt] using h

private theorem dottieCompletedContour_eq_raw (w : ℂ) :
    (∫ u : ℝ, dottieCompletedContourIntegrand w u) =
      (∫ u : ℝ, contourNumerator w (verticalPoint 1 u) / verticalPoint 1 u) /
        (2 * (Real.pi : ℂ) * (archivedDottieCompletionScale : ℂ)) := by
  rw [← integral_div]
  refine integral_congr_ae (Eventually.of_forall (fun u => ?_))
  unfold dottieCompletedContourIntegrand contourNumerator verticalPoint dottieContour tilt
  push_cast
  ring

/-- The two actual smoothed norm series sum to the completed Gaussian
quartic factor everywhere in the open critical strip. -/
theorem dottieSmoothTerm_hasSum_normalized {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    HasSum (dottieSmoothTerm w) (archivedMellin w/(archivedDottieCompletionScale : ℂ)) := by
  have hm : 0 < (1-conj w).re := by simp [hw₁]
  have hr := dottieSmoothSide_hasSum_completed_contour hw₀
  have hl := (dottieSmoothSide_hasSum_completed_contour hm).mapL (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have h := hr.add hl
  change HasSum (dottieSmoothTerm w)
    ((∫ u : ℝ, dottieCompletedContourIntegrand w u) +
      conj (∫ u : ℝ, dottieCompletedContourIntegrand (1-conj w) u)) at h
  rw [dottieCompletedContour_eq_raw, dottieCompletedContour_eq_raw, map_div₀,
    map_mul, map_mul, map_ofNat, conj_ofReal, conj_ofReal, ← add_div,
    dottiePairedRawContours hw₀ hw₁] at h
  have hπ : (2 : ℂ) * (Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num)
    (ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [mul_div_mul_left _ _ hπ] at h
  exact h

theorem dottie_normalized_remainder_eq_signed_norm_sum {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    archivedMellin w/(archivedDottieCompletionScale : ℂ) - dottieRetained w = dottieOmitted w :=
  dottie_normalized_remainder_eq_omitted (dottieSmoothTerm_norm_summable hw₀ hw₁)
    (dottieSmoothTerm_hasSum_normalized hw₀ hw₁)

private theorem dottieBoundary_mem_strip {z : ℂ}
    (hz : z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    0 < z.re ∧ z.re < 1 := by
  have hn : ‖z-archivedRightCenter dottieHeight‖ ≤ 31/2048 := by
    simpa only [dist_eq_norm] using (Metric.mem_sphere.mp hz).le
  have hh := abs_le.mp ((Complex.abs_re_le_norm _).trans hn)
  change -(31/2048 : ℝ) ≤ z.re-33/64 ∧ z.re-33/64 ≤ 31/2048 at hh
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

/-- Apply both analytic contour results to the right measuring circle.
The remaining assumptions are the signed enclosure of the retained model
and its omitted terms in the same normalization. -/
theorem dottie_ring_zero_free_of_signed_bounds
    (hS : 0 < dottieCircleReference)
    (model : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieRetained w).im ≤ -(190*((w.re-1/2)*dottieCircleReference)))
    (tail : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieOmitted w).im ≤ 189*((w.re-1/2)*dottieCircleReference))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) :
    archivedGaussianFactor w ≠ 0 ∧ archivedGaussianFactor (1-conj w) ≠ 0 := by
  refine archivedDottieRing_zero_free_of_replay hS dottieRetained model ?_ hw
  intro z hz
  have hr := dottieBoundary_mem_strip hz
  rw [dottie_normalized_remainder_eq_signed_norm_sum hr.1 hr.2]
  exact tail z hz

open SuperZeta.QuarticOrderedTurns in
theorem dottie_ring_painted_orders_of_signed_bounds
    (hS : 0 < dottieCircleReference)
    (model : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieRetained w).im ≤ -(190*((w.re-1/2)*dottieCircleReference)))
    (tail : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieOmitted w).im ≤ 189*((w.re-1/2)*dottieCircleReference))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) (ink inkMirror : ℂ) :
    let q := paintedReading w ink
    let qm := paintedReading (1-conj w) inkMirror
    0 < (J*q).imK ∧ (J*qm).imK < 0 ∧ jk q ≠ kj q ∧ jk qm ≠ kj qm := by
  refine dottie_ring_painted_orders_of_replay hS dottieRetained model ?_ hw ink inkMirror
  intro z hz
  have hr := dottieBoundary_mem_strip hz
  rw [dottie_normalized_remainder_eq_signed_norm_sum hr.1 hr.2]
  exact tail z hz

#print axioms dottieSmoothTerm_hasSum_normalized
#print axioms dottie_normalized_remainder_eq_signed_norm_sum
#print axioms dottie_ring_zero_free_of_signed_bounds
#print axioms dottie_ring_painted_orders_of_signed_bounds

end QuarticModel
