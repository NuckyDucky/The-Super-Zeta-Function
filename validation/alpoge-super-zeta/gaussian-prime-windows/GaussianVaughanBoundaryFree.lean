import GaussianVaughanReflectionDescent
import GaussianVaughanDetectedPoles
import GaussianVaughanInertExcess

/-! The same signed window excludes the detected poles. Reflection then
excludes all upper-right zeros, using the real-axis positivity input. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory QuarticModel FieldTarget Set ArtinPrimitiveRootsConjecture
open scoped Topology

noncomputable section

private def vaughanLogReading (e a u : ℝ) : ℝ :=
  (e * archivedGaussianVaughanSum (Real.exp u)) * Real.exp (-a * u)

private def vaughanShiftedPoles (a : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z + (a : ℂ) ∈ archivedGaussianVaughanDetectedPoles}

private theorem vaughan_shift_tendsto (a : ℝ) (z : ℂ) :
    Tendsto (fun w => w + (a : ℂ)) (𝓝[≠] z) (𝓝[≠] (z + (a : ℂ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuousAt_id.add continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact fun he => hw (add_right_cancel he)

private theorem vaughan_log_reading_growth (e : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, ∀ u ≥ (0 : ℝ), |vaughanLogReading e a u| ≤ C * Real.exp (2 * u) := by
  obtain ⟨C, _, hGrow⟩ := archivedGaussianVaughanSum_growth
  refine ⟨|e| * C, fun u hu => ?_⟩
  have hExp : Real.exp (-a * u) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha hu])
  have hPower : (Real.exp u) ^ (2 : ℝ) = Real.exp (2 * u) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm u 2]
  rw [vaughanLogReading, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    (|e| * |archivedGaussianVaughanSum (Real.exp u)|) * Real.exp (-a * u) ≤
        |e| * |archivedGaussianVaughanSum (Real.exp u)| :=
      mul_le_of_le_one_right
        (mul_nonneg (abs_nonneg e) (abs_nonneg (archivedGaussianVaughanSum (Real.exp u)))) hExp
    _ ≤ (|e| * C) * Real.exp (2 * u) := by
      rw [mul_assoc, ← hPower]
      exact mul_le_mul_of_nonneg_left (hGrow _ (Real.one_le_exp hu)) (abs_nonneg _)

private theorem vaughan_log_reading_laplace (e : ℝ) {a : ℝ} (ha : 0 ≤ a)
    {z : ℂ} (hz : 2 < z.re) :
    (e : ℂ) * (archivedGaussianVaughanMellinNormal (z + (a : ℂ)) -
      archivedGaussianVaughanEndpoint (z + (a : ℂ))) =
      ∫ u in Ioi (0 : ℝ), (vaughanLogReading e a u : ℂ) * exp (-z * u) := by
  let w := z + (a : ℂ)
  have hw : 2 < w.re := by
    change 2 < z.re + a
    linarith
  change (e : ℂ) * (archivedGaussianVaughanMellinNormal w - archivedGaussianVaughanEndpoint w) = _
  rw [archivedGaussianVaughanMellinNormal_eq (archivedGaussianFactor_ne_zero_of_re_gt_one
    (one_lt_two.trans hw)), ← archivedGaussianVaughanSum_mellin_above_one (one_lt_two.trans hw),
    ← Deduction.poleData_change (fun x => (archivedGaussianVaughanSum x : ℂ)) w,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  change (e : ℂ) * ((archivedGaussianVaughanSum (Real.exp u) : ℂ) * exp (-w * u)) =
    (vaughanLogReading e a u : ℂ) * exp (-z * u)
  have hExp : exp (-w * (u : ℂ)) = exp ((-(a : ℂ)) * u) * exp (-z * u) := by
    rw [← exp_add]
    congr 1
    dsimp [w]
    ring
  rw [hExp]
  simp only [vaughanLogReading, ofReal_mul, ofReal_exp, ofReal_neg]
  ring

private theorem vaughan_log_reading_pole_data {e a : ℝ} (he : e ≠ 0) (ha : 1 / 2 < a)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re) :
    Deduction.PoleData (vaughanLogReading e a)
      (fun z => (e : ℂ) * (archivedGaussianVaughanMellinNormal (z + (a : ℂ)) -
        archivedGaussianVaughanEndpoint (z + (a : ℂ)))) (vaughanShiftedPoles a) := by
  obtain ⟨_, _, _, _, hIso⟩ := gaussian_regularized_transform
  have ha₀ : 0 ≤ a := by linarith
  have hReal := gaussian_poles_nonreal_of_mellin_pos (fun σ _ =>
    archivedMellin_eq_quartic_real_formula ▸ hpos σ)
  have hg : Measurable (vaughanLogReading e a) :=
    (measurable_const.mul (archivedGaussianVaughanSum_measurable.comp Real.measurable_exp)).mul
      (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  refine ⟨hg, vaughan_log_reading_growth e ha₀, fun _ => vaughan_log_reading_laplace e ha₀,
    fun _ h => h.1, ?_, ?_, ?_⟩
  · rintro z ⟨hz, hnot⟩
    have hShift : AnalyticAt ℂ (fun w : ℂ => w + (a : ℂ)) z := analyticAt_id.add analyticAt_const
    have h := (archivedGaussianVaughanMellinNormal_analytic (fun h => hnot ⟨hz, h⟩)).sub
      (archivedGaussianVaughanEndpoint_entire.analyticAt (z + (a : ℂ)))
    exact ((analyticAt_const.mul h).comp (f := fun w : ℂ => w + (a : ℂ)) (x := z)
      hShift).differentiableAt.differentiableWithinAt
  · intro z _
    filter_upwards [(vaughan_shift_tendsto a z).eventually (hIso (z + (a : ℂ)))] with w hw
    exact fun h => hw h.2.1
  · intro z hz
    have hw₀ : 0 < (z + (a : ℂ)).re := by
      have hZ : 0 < z.re := hz.1
      simp only [add_re, ofReal_re]
      linarith
    have hReal' := hReal (z + (a : ℂ)) ⟨hw₀, hz.2.1⟩
    obtain ⟨c, hc, b, hb, hnear⟩ := archivedGaussianVaughanMellinNormal_pole hz.2
    have hShift : AnalyticAt ℂ (fun w : ℂ => w + (a : ℂ)) z := analyticAt_id.add analyticAt_const
    have hReg := hb.sub (archivedGaussianVaughanEndpoint_entire.analyticAt (z + (a : ℂ)))
    refine ⟨(e : ℂ) * c, mul_ne_zero (ofReal_ne_zero.mpr he) hc, fun him =>
      (hReal' (by simp [him])).elim,
      fun w => (e : ℂ) * (b (w + (a : ℂ)) - archivedGaussianVaughanEndpoint (w + (a : ℂ))),
      (analyticAt_const.mul hReg).comp (f := fun w : ℂ => w + (a : ℂ)) (x := z) hShift, ?_⟩
    filter_upwards [(vaughan_shift_tendsto a z).eventually hnear] with w hw
    rw [hw, add_sub_add_right_eq_sub, mul_div_assoc]
    ring

theorem archivedGaussianVaughan_no_detected_pole_of_windows {e : ℝ} (he : e ≠ 0)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound (fun X => e * archivedGaussianVaughanSum X))
    {w : ℂ} (hleft : 1 / 2 < w.re) (hright : w.re < 1) :
    w ∉ archivedGaussianVaughanDetectedPoles := by
  intro hw
  let a : ℝ := (1 / 2 + w.re) / 2
  let θ : ℝ := (a + w.re) / 2
  have ha : 1 / 2 < a := by dsimp [a]; linarith
  have ha' : a < w.re := by dsimp [a]; linarith
  have ht : a < θ := by dsimp [θ]; linarith
  have ht' : θ < w.re := by dsimp [θ]; linarith
  obtain ⟨δ, hδ, C, hC, hW⟩ := hcut θ (ha.trans ht) (ht'.trans hright)
  let f (y : ℝ) := (e * archivedGaussianVaughanSum y) * y ^ (-a)
  have hF : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      f y ≤ C * y ^ (θ - a) := by
    intro Y₀
    obtain ⟨Y, hY, hb⟩ := hW (max Y₀ 1)
    refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
    have hy₁ : 1 ≤ y := (le_max_right Y₀ 1).trans (hY.trans hy.1)
    have hy₀ := zero_lt_one.trans_le hy₁
    dsimp [f]
    calc
      _ ≤ (C * y ^ θ) * y ^ (-a) :=
        mul_le_mul_of_nonneg_right (hb y hy) (Real.rpow_nonneg hy₀.le _)
      _ = _ := by rw [mul_assoc, ← Real.rpow_add hy₀, sub_eq_add_neg]
  have hfun : (fun u => f (Real.exp u)) = vaughanLogReading e a := by
    funext u
    simp only [f, vaughanLogReading, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [mul_comm u (-a)]
  have hh := logWindow_of_pointwise_norm_windows f (θ := θ - a) (δ := δ) hδ hC hF
  rw [hfun] at hh
  have hshift : w - (a : ℂ) ∈ vaughanShiftedPoles a := by
    refine ⟨?_, ?_⟩
    · simp only [sub_re, ofReal_re]; linarith
    · rwa [sub_add_cancel]
  have hle := Deduction.landau_window (vaughan_log_reading_pole_data he ha hpos)
    (show 0 < θ - a by linarith) (show θ - a < 1 by linarith) hδ hh _ hshift
  simp only [sub_re, ofReal_re] at hle
  linarith

theorem quartic_rh_of_archived_vaughan_scaled_windows_by_reflection
    (hDir : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    {e : ℝ} (he : e ≠ 0)
    (hcut : GaussianCutoffWindowBound (fun X => e * archivedGaussianVaughanSum X)) :
    DedekindZetaRH QuarticModel.K := by
  obtain ⟨hR, hB⟩ := cofactors_on_line hDir
  apply archivedQuarticRH_iff_upper_right.mpr
  refine ⟨hR, hB, ?_⟩
  intro w hl hr _ hw
  have hGw := (archivedGaussianFactor_zero_iff_mellin (by linarith [hl])).mpr hw
  obtain ⟨z, hzl, hzr, hG, hM⟩ :=
    archivedGaussianVaughan_detects_some_zero_of_real_pos hpos hl hr hGw
  exact archivedGaussianVaughan_no_detected_pole_of_windows he hpos hcut hzl hzr ⟨hG, hM⟩

theorem quartic_rh_of_archived_vaughan_signed_windows_by_reflection
    (hDir : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (W : ℝ → ℝ) (hW : ∀ u ≥ 0, |W u| ≤ 1)
    (hUnit : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → W u = 1) (hSupport : ∀ u ≥ 2, W u = 0)
    (hcut : GaussianCutoffWindowBound (archivedGaussianVaughanLowerSum W)) :
    DedekindZetaRH QuarticModel.K := by
  obtain ⟨A, hA, hError⟩ := archivedGaussianVaughanLowerPrimeSum_error hDir W hW hUnit hSupport
  apply quartic_rh_of_archived_vaughan_scaled_windows_by_reflection hDir hpos (e := 1) (by norm_num)
  simpa only [one_mul] using gaussianLogWindow_error_transfer hA hError hcut

theorem quartic_rh_of_archived_vaughan_inert_windows_by_reflection
    (hDir : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianVaughanInertExcess) :
    DedekindZetaRH QuarticModel.K := by
  obtain ⟨A, hA, hError⟩ := archivedGaussianVaughanPrimeBand_approx hDir
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hDiff : ∀ᶠ X : ℝ in atTop,
      |(-archivedGaussianVaughanSum X) - archivedGaussianVaughanInertExcess X| ≤
        A * (X ^ (3 / 8 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hError, hLog,
      archivedGaussianVaughanInertExcess_eventually_eq_neg] with X hX hError hLog hEq
    rw [hEq, neg_sub_neg, abs_sub_comm]
    have hP : 0 ≤ X ^ (3 / 8 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hX.le) _
    have hL : 1 ≤ (Real.log X) ^ (8 / 3 : ℝ) := Real.one_le_rpow hLog (by norm_num)
    exact hError.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hP hL) hA)
  have h := gaussianLogWindow_error_transfer hA hDiff hcut
  apply quartic_rh_of_archived_vaughan_scaled_windows_by_reflection hDir hpos (e := -1)
    (by norm_num)
  simpa only [neg_one_mul] using h

#check quartic_rh_of_archived_vaughan_signed_windows_by_reflection
#check quartic_rh_of_archived_vaughan_inert_windows_by_reflection
#print axioms archivedGaussianVaughan_no_detected_pole_of_windows
#print axioms quartic_rh_of_archived_vaughan_scaled_windows_by_reflection
#print axioms quartic_rh_of_archived_vaughan_signed_windows_by_reflection
#print axioms quartic_rh_of_archived_vaughan_inert_windows_by_reflection

end
end AlpogeSuperZeta
