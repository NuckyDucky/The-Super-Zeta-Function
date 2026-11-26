import GaussianRawWindowRounding

/-! The centered, un-inverted window is a sufficient condition for
the same quartic target. The factor at one is regularized before the
window criterion is applied. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory Set QuarticModel FieldTarget ArtinPrimitiveRootsConjecture
open scoped Topology

noncomputable section

/-- The factor `(w-1)ζ(w)`, with value one at the removable point. -/
def gaussianWindowZetaFactor (w : ℂ) : ℂ :=
  ((w - 1) * completedRiemannZeta₀ w - (w - 1) / w + 1) * (Gammaℝ w)⁻¹

private theorem gaussianWindowZetaFactor_eq {w : ℂ} (h0 : w ≠ 0) (h1 : w ≠ 1) :
    gaussianWindowZetaFactor w = (w - 1) * riemannZeta w := by
  rw [gaussianWindowZetaFactor, riemannZeta_def_of_ne_zero h0, completedRiemannZeta_eq,
    div_eq_mul_inv _ (Gammaℝ w), ← mul_assoc]
  congr 1
  have h01 : 1 - w ≠ 0 := sub_ne_zero.mpr h1.symm
  field_simp
  ring

private theorem gaussianWindowZetaFactor_analytic {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ gaussianWindowZetaFactor w := by
  have h0 : w ≠ 0 := by rintro rfl; simp at hw
  have h₁ : AnalyticAt ℂ (fun z : ℂ => z - 1) w := analyticAt_id.sub analyticAt_const
  exact (((h₁.mul (differentiable_completedZeta₀.analyticAt _)).sub
    (h₁.div analyticAt_id h0)).add analyticAt_const).mul (differentiable_Gammaℝ_inv.analyticAt _)

private theorem gaussianWindowZetaFactor_ne_zero (hD : DirichletLZerosOnLine)
    {w : ℂ} (hw : 1 / 2 < w.re) : gaussianWindowZetaFactor w ≠ 0 := by
  by_cases h1 : w = 1
  · simp [h1, gaussianWindowZetaFactor, Gammaℝ_one]
  have h0 : 0 < w.re := by linarith
  have hw0 : w ≠ 0 := by rintro rfl; simp at h0
  rw [gaussianWindowZetaFactor_eq hw0 h1]
  apply mul_ne_zero (sub_ne_zero.mpr h1)
  by_cases hRe : 1 ≤ w.re
  · exact riemannZeta_ne_zero_of_one_le_re hRe
  · intro hz
    have he := (cofactors_on_line hD).1 w h0 (lt_of_not_ge hRe) hz
    linarith

private def rawWindowMultiplier (w : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (-w)) * gaussianWindowZetaFactor w

private theorem rawWindowMultiplier_analytic {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ rawWindowMultiplier w := by
  have hExp : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ (-z)) w := by
    simp_rw [cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    exact (analyticAt_const.mul analyticAt_id.neg).cexp'
  exact (analyticAt_const.sub hExp).mul (gaussianWindowZetaFactor_analytic hw)

private theorem rawWindowMultiplier_ne_zero (hD : DirichletLZerosOnLine)
    {w : ℂ} (hw : 1 / 2 < w.re) : rawWindowMultiplier w ≠ 0 := by
  refine mul_ne_zero (sub_ne_zero.mpr ?_) (gaussianWindowZetaFactor_ne_zero hD hw)
  intro h
  have hh := norm_two_cpow_neg_lt_one (show 0 < w.re by linarith)
  rw [← h, norm_one] at hh
  exact lt_irrefl _ hh

private def rawWindowContinuation (Ψ : ℂ → ℂ) (w : ℂ) : ℂ :=
  rawWindowMultiplier w * (Ψ w - (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w)

private theorem rawWindowContinuation_analytic {Ψ : ℂ → ℂ} {w : ℂ}
    (hw : 0 < w.re) (hΨ : AnalyticAt ℂ Ψ w) :
    AnalyticAt ℂ (rawWindowContinuation Ψ) w := by
  have h0 : w ≠ 0 := by rintro rfl; simp at hw
  exact (rawWindowMultiplier_analytic hw).mul (hΨ.sub (analyticAt_const.div analyticAt_id h0))

private theorem rawWindowContinuation_pole (hD : DirichletLZerosOnLine)
    {Ψ b : ℂ → ℂ} {ρ c : ℂ} (hρ : 1 / 2 < ρ.re) (hc : c ≠ 0)
    (hb : AnalyticAt ℂ b ρ)
    (hp : ∀ᶠ w in 𝓝[≠] ρ, Ψ w = c / (w - ρ) + b w) :
    ∃ d : ℂ, d ≠ 0 ∧ ∃ b' : ℂ → ℂ, AnalyticAt ℂ b' ρ ∧
      ∀ᶠ w in 𝓝[≠] ρ, rawWindowContinuation Ψ w = d / (w - ρ) + b' w := by
  have hρ₀ : 0 < ρ.re := by linarith
  have h0 : ρ ≠ 0 := by rintro rfl; simp at hρ₀
  have hM := rawWindowMultiplier_analytic hρ₀
  have hb' := hb.sub (analyticAt_const.div analyticAt_id h0 :
    AnalyticAt ℂ (fun w => (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w) ρ)
  refine ⟨rawWindowMultiplier ρ * c, mul_ne_zero (rawWindowMultiplier_ne_zero hD hρ) hc,
    fun w => dslope rawWindowMultiplier ρ w * c +
      rawWindowMultiplier w * (b w - (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w),
    ((Deduction.poleData_dslope hM).mul analyticAt_const).add (hM.mul hb'), ?_⟩
  filter_upwards [hp, self_mem_nhdsWithin] with w hw hne
  change w ≠ ρ at hne
  rw [rawWindowContinuation, hw, dslope_of_ne _ hne, slope_def_field]
  ring

private def rawLogWindow (a : ℝ) (u : ℝ) : ℝ :=
  archivedGaussianRawWindow (Real.exp u) * Real.exp (-a * u)

private theorem rawLogWindow_measurable (a : ℝ) : Measurable (rawLogWindow a) :=
  (archivedGaussianRawWindow_measurable.comp Real.measurable_exp).mul
    (Real.measurable_exp.comp (measurable_const.mul measurable_id))

private theorem rawLogWindow_growth {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |rawLogWindow a u| ≤ C * Real.exp (2 * u) := by
  obtain ⟨C, -, hC⟩ := archivedGaussianRawWindow_growth
  refine ⟨C, fun u hu => ?_⟩
  have hn : Real.exp (-a * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha hu])
  unfold rawLogWindow
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ |archivedGaussianRawWindow (Real.exp u)| :=
      mul_le_of_le_one_right (abs_nonneg _) hn
    _ ≤ C * (Real.exp u) ^ (2 : ℝ) := hC _ (Real.one_le_exp hu)
    _ = _ := by rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm u 2]

private theorem rawLogWindow_laplace {Ψ : ℂ → ℂ}
    (hΨ : ∀ w : ℂ, 2 < w.re → Ψ w = archivedGaussianPrimitiveIndexMellin w)
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 2 < z.re) :
    rawWindowContinuation Ψ (z + (a : ℂ)) =
      ∫ u in Ioi (0 : ℝ), (rawLogWindow a u : ℂ) * exp (-z * u) := by
  let w := z + (a : ℂ)
  have hw : 2 < w.re := by change 2 < z.re + a; linarith
  have h1 : w ≠ 1 := fun h => by rw [h, one_re] at hw; linarith
  have h0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; linarith
  change rawWindowContinuation Ψ w = _
  rw [rawWindowContinuation, hΨ w hw, rawWindowMultiplier, gaussianWindowZetaFactor_eq h0 h1,
    ← archivedGaussianRawWindow_mellin (show 1 < w.re by linarith),
    ← Deduction.poleData_change (fun x => (archivedGaussianRawWindow x : ℂ))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [rawLogWindow, ofReal_mul, ofReal_exp, ofReal_neg]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  dsimp [w]
  ring

private def shiftedGaussianPoles (a : ℝ) : Set ℂ :=
  {z | 0 < z.re ∧ z + (a : ℂ) ∈ gaussianPoles}

private theorem add_real_tendsto_punctured (a : ℝ) (z : ℂ) :
    Tendsto (fun w => w + (a : ℂ)) (𝓝[≠] z) (𝓝[≠] (z + (a : ℂ))) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuousAt_id.add continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  exact fun he => hw (add_right_cancel he)

private theorem rawLogWindow_hasPoleData (hD : DirichletLZerosOnLine)
    (hReal : ∀ ρ ∈ gaussianPoles, ρ.im ≠ 0) {a : ℝ} (ha : 1 / 2 < a) :
    ∃ Φ : ℂ → ℂ, Deduction.PoleData (rawLogWindow a) Φ (shiftedGaussianPoles a) := by
  obtain ⟨Ψ, hΨ, hAt, hPole⟩ := archivedGaussianPrimitiveIndexMellin_same_pole
  obtain ⟨_, _, _, _, hIso⟩ := gaussian_regularized_transform
  have ha0 : 0 ≤ a := by linarith
  have hs {z : ℂ} (hz : 0 < z.re) : 1 / 2 < (z + (a : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith
  refine ⟨fun z => rawWindowContinuation Ψ (z + (a : ℂ)),
    ⟨rawLogWindow_measurable a, rawLogWindow_growth ha0, fun _ => rawLogWindow_laplace hΨ ha0,
      fun _ hz => hz.1, ?_, ?_, ?_⟩⟩
  · rintro z ⟨hz, hnot⟩
    have hhalf := hs (show 0 < z.re from hz)
    have hz0 : 0 < (z + (a : ℂ)).re := by linarith
    have hnon : archivedGaussianFactor (z + (a : ℂ)) ≠ 0 :=
      fun h => hnot ⟨hz, hz0, h⟩
    have hF := rawWindowContinuation_analytic hz0 (hAt _ hhalf hnon)
    have hshift : AnalyticAt ℂ (fun v : ℂ => v + (a : ℂ)) z := analyticAt_id.add analyticAt_const
    exact (hF.comp (f := fun v => v + (a : ℂ)) (x := z) hshift).differentiableAt.differentiableWithinAt
  · intro z _
    filter_upwards [(add_real_tendsto_punctured a z).eventually (hIso (z + (a : ℂ)))] with w hw
    exact fun h => hw h.2.2
  · intro z hz
    have hhalf := hs hz.1
    obtain ⟨c, hc, b, hb, hp⟩ := hPole _ hz.2 hhalf
    obtain ⟨d, hd, b', hb', hp'⟩ := rawWindowContinuation_pole hD hhalf hc hb hp
    have hshift : AnalyticAt ℂ (fun v : ℂ => v + (a : ℂ)) z := analyticAt_id.add analyticAt_const
    refine ⟨d, hd, fun him => (hReal _ hz.2 (by simpa only [add_im, ofReal_im, add_zero] using him)).elim,
      fun w => b' (w + (a : ℂ)), hb'.comp (f := fun v => v + (a : ℂ)) (x := z) hshift, ?_⟩
    filter_upwards [(add_real_tendsto_punctured a z).eventually hp'] with w hw
    rw [show rawWindowContinuation Ψ (w + (a : ℂ)) =
      d / ((w + (a : ℂ)) - (z + (a : ℂ))) + b' (w + (a : ℂ)) from hw,
      add_sub_add_right_eq_sub]

/-- The direct determinant window bound in the original norm variable. -/
def ArchivedGaussianRawWindowBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      ∀ y ∈ Icc Y (Y ^ (1 + δ)), archivedGaussianRawWindow y ≤ C * y ^ θ

theorem quartic_rh_of_archived_gaussian_raw_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : ArchivedGaussianRawWindowBound) : DedekindZetaRH QuarticModel.K := by
  obtain ⟨hR, hB⟩ := cofactors_on_line hD
  apply archivedQuarticRH_iff_upper_right.mpr
  refine ⟨hR, hB, ?_⟩
  intro w hright hleft _ hz
  have hp : 0 < w.re := by linarith
  have hw : w ∈ gaussianPoles := ⟨hp, (archivedGaussianFactor_zero_iff_mellin hp).mpr hz⟩
  have hReal := gaussian_poles_nonreal_of_mellin_pos (fun σ _ =>
    archivedMellin_eq_quartic_real_formula ▸ hpos σ)
  let a : ℝ := (1 / 2 + w.re) / 2
  let θ : ℝ := (a + w.re) / 2
  have ha : 1 / 2 < a := by dsimp [a]; linarith
  have ht : a < θ := by dsimp [θ, a]; linarith
  have ht' : θ < w.re := by dsimp [θ, a]; linarith
  obtain ⟨δ, hδ, C, hC, hW⟩ := hcut θ (ha.trans ht) (ht'.trans hleft)
  obtain ⟨Φ, hData⟩ := rawLogWindow_hasPoleData hD hReal ha
  let f : ℝ → ℝ := fun y => archivedGaussianRawWindow y * y ^ (-a)
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
  have hfun : (fun u => f (Real.exp u)) = rawLogWindow a := by
    funext u
    simp only [f, rawLogWindow, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    rw [mul_comm u (-a)]
  have hh := logWindow_of_pointwise_norm_windows f (θ := θ - a) (δ := δ) hδ hC hF
  rw [hfun] at hh
  have hθ₀ : 0 < θ - a := by linarith
  have hθ₁ : θ - a < 1 := by linarith
  have hz' : w - (a : ℂ) ∈ shiftedGaussianPoles a := by
    refine ⟨?_, ?_⟩
    · simp only [sub_re, ofReal_re]; linarith
    · rwa [sub_add_cancel]
  have hle := Deduction.landau_window hData hθ₀ hθ₁ hδ hh (w - (a : ℂ)) hz'
  simp only [sub_re, ofReal_re] at hle
  linarith

theorem quartic_rh_of_archived_gaussian_large_address_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
        archivedGaussianLargeAddressWindow y ≤ C * y ^ θ) : DedekindZetaRH QuarticModel.K := by
  apply quartic_rh_of_archived_gaussian_raw_windows hD hpos
  intro θ hθ hθ₁
  obtain ⟨δ, hδ, C, hC, hW⟩ := hcut θ hθ hθ₁
  obtain ⟨D, hD₀, hE⟩ := archivedGaussianLargeAddressWindow_error hθ
  refine ⟨δ, hδ, C + D, add_nonneg hC hD₀, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hb⟩ := hW (max Y₀ 1)
  refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
  have hy₁ : 1 ≤ y := (le_max_right Y₀ 1).trans (hY.trans hy.1)
  linarith [(abs_le.mp (hE y hy₁)).2, hb y hy]

#print axioms gaussianWindowZetaFactor_analytic
#print axioms rawLogWindow_hasPoleData
#print ArchivedGaussianRawWindowBound
#check quartic_rh_of_archived_gaussian_raw_windows
#print axioms quartic_rh_of_archived_gaussian_raw_windows
#check quartic_rh_of_archived_gaussian_large_address_windows
#print axioms quartic_rh_of_archived_gaussian_large_address_windows

end
end AlpogeSuperZeta
