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

theorem halfWindowFactor_analytic (w : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => 1 - (2 : ℂ) ^ (-z)) w := by
  have hExp : AnalyticAt ℂ (fun z : ℂ => (2 : ℂ) ^ (-z)) w := by
    simp_rw [cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    exact (analyticAt_const.mul analyticAt_id.neg).cexp'
  exact analyticAt_const.sub hExp

theorem halfWindowFactor_ne_zero {w : ℂ} (hw : 0 < w.re) :
    1 - (2 : ℂ) ^ (-w) ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  have hh := norm_two_cpow_neg_lt_one hw
  rw [← h, norm_one] at hh
  exact lt_irrefl _ hh

private def gaussianCutoffMultiplier (M : ℂ → ℂ) (w : ℂ) : ℂ :=
  M w * gaussianWindowZetaFactor w

private def gaussianCutoffContinuation (M Ψ : ℂ → ℂ) (w : ℂ) : ℂ :=
  gaussianCutoffMultiplier M w * (Ψ w - (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w)

private theorem gaussianCutoffContinuation_analytic {M Ψ : ℂ → ℂ} {w : ℂ}
    (hw : 0 < w.re) (hM : AnalyticAt ℂ M w) (hΨ : AnalyticAt ℂ Ψ w) :
    AnalyticAt ℂ (gaussianCutoffContinuation M Ψ) w := by
  have h0 : w ≠ 0 := by rintro rfl; simp at hw
  exact (hM.mul (gaussianWindowZetaFactor_analytic hw)).mul
    (hΨ.sub (analyticAt_const.div analyticAt_id h0))

private theorem gaussianCutoffContinuation_pole (hD : DirichletLZerosOnLine)
    {M Ψ b : ℂ → ℂ} {ρ c : ℂ} (hρ : 1 / 2 < ρ.re)
    (hMa : AnalyticAt ℂ M ρ) (hM₀ : M ρ ≠ 0) (hc : c ≠ 0)
    (hb : AnalyticAt ℂ b ρ)
    (hp : ∀ᶠ w in 𝓝[≠] ρ, Ψ w = c / (w - ρ) + b w) :
    ∃ d : ℂ, d ≠ 0 ∧ ∃ b' : ℂ → ℂ, AnalyticAt ℂ b' ρ ∧
      ∀ᶠ w in 𝓝[≠] ρ, gaussianCutoffContinuation M Ψ w = d / (w - ρ) + b' w := by
  have hρ₀ : 0 < ρ.re := by linarith
  have h0 : ρ ≠ 0 := by rintro rfl; simp at hρ₀
  have hM : AnalyticAt ℂ (gaussianCutoffMultiplier M) ρ :=
    hMa.mul (gaussianWindowZetaFactor_analytic hρ₀)
  have hMne : gaussianCutoffMultiplier M ρ ≠ 0 :=
    mul_ne_zero hM₀ (gaussianWindowZetaFactor_ne_zero hD hρ)
  have hb' := hb.sub (analyticAt_const.div analyticAt_id h0 :
    AnalyticAt ℂ (fun w => (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w) ρ)
  refine ⟨gaussianCutoffMultiplier M ρ * c, mul_ne_zero hMne hc,
    fun w => dslope (gaussianCutoffMultiplier M) ρ w * c +
      gaussianCutoffMultiplier M w * (b w - (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w),
    ((Deduction.poleData_dslope hM).mul analyticAt_const).add (hM.mul hb'), ?_⟩
  filter_upwards [hp, self_mem_nhdsWithin] with w hw hne
  change w ≠ ρ at hne
  rw [gaussianCutoffContinuation, hw, dslope_of_ne _ hne, slope_def_field]
  ring

private def gaussianLogCutoff (A : ℝ → ℝ) (a : ℝ) (u : ℝ) : ℝ :=
  A (Real.exp u) * Real.exp (-a * u)

private theorem gaussianLogCutoff_measurable {A : ℝ → ℝ} (hA : Measurable A) (a : ℝ) :
    Measurable (gaussianLogCutoff A a) :=
  (hA.comp Real.measurable_exp).mul
    (Real.measurable_exp.comp (measurable_const.mul measurable_id))

private theorem gaussianLogCutoff_growth {A : ℝ → ℝ}
    (hA : ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), |A x| ≤ C * x ^ (2 : ℝ)) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |gaussianLogCutoff A a u| ≤ C * Real.exp (2 * u) := by
  obtain ⟨C, -, hC⟩ := hA
  refine ⟨C, fun u hu => ?_⟩
  have hn : Real.exp (-a * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg ha hu])
  unfold gaussianLogCutoff
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ |A (Real.exp u)| :=
      mul_le_of_le_one_right (abs_nonneg _) hn
    _ ≤ C * (Real.exp u) ^ (2 : ℝ) := hC _ (Real.one_le_exp hu)
    _ = _ := by rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm u 2]

private theorem gaussianLogCutoff_laplace {A : ℝ → ℝ} {Φ : ℂ → ℂ}
    (hTransform : ∀ w : ℂ, 2 < w.re →
      ∫ x in Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 1) = Φ w)
    {a : ℝ} (ha : 0 ≤ a) {z : ℂ} (hz : 2 < z.re) :
    Φ (z + (a : ℂ)) =
      ∫ u in Ioi (0 : ℝ), (gaussianLogCutoff A a u : ℂ) * exp (-z * u) := by
  let w := z + (a : ℂ)
  have hw : 2 < w.re := by change 2 < z.re + a; linarith
  change Φ w = _
  rw [← hTransform w hw, ← Deduction.poleData_change (fun x => (A x : ℂ))]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [gaussianLogCutoff, ofReal_mul, ofReal_exp, ofReal_neg]
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

private theorem gaussianLogCutoff_hasPoleData
    {A : ℝ → ℝ} {Φ : ℂ → ℂ} (hA : Measurable A)
    (hGrowth : ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), |A x| ≤ C * x ^ (2 : ℝ))
    (hAnalytic : ∀ w : ℂ, 1 / 2 < w.re → archivedGaussianFactor w ≠ 0 → AnalyticAt ℂ Φ w)
    (hPole : ∀ ρ ∈ gaussianPoles, 1 / 2 < ρ.re → ∃ c : ℂ, c ≠ 0 ∧
      (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧ ∃ b : ℂ → ℂ, AnalyticAt ℂ b ρ ∧
        ∀ᶠ w in 𝓝[≠] ρ, Φ w = c / (w - ρ) + b w)
    (hTransform : ∀ w : ℂ, 2 < w.re →
      ∫ x in Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 1) = Φ w)
    {a : ℝ} (ha : 1 / 2 < a) :
    Deduction.PoleData (gaussianLogCutoff A a) (fun z => Φ (z + (a : ℂ))) (shiftedGaussianPoles a) := by
  obtain ⟨_, _, _, _, hIso⟩ := gaussian_regularized_transform
  have ha0 : 0 ≤ a := by linarith
  have hs {z : ℂ} (hz : 0 < z.re) : 1 / 2 < (z + (a : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith
  refine ⟨gaussianLogCutoff_measurable hA a, gaussianLogCutoff_growth hGrowth ha0,
    fun _ => gaussianLogCutoff_laplace hTransform ha0,
    fun _ hz => hz.1, ?_, ?_, ?_⟩
  · rintro z ⟨hz, hnot⟩
    have hhalf := hs (show 0 < z.re from hz)
    have hz0 : 0 < (z + (a : ℂ)).re := by linarith
    have hnon : archivedGaussianFactor (z + (a : ℂ)) ≠ 0 :=
      fun h => hnot ⟨hz, hz0, h⟩
    have hF := hAnalytic _ hhalf hnon
    have hshift : AnalyticAt ℂ (fun v : ℂ => v + (a : ℂ)) z := analyticAt_id.add analyticAt_const
    exact (hF.comp (f := fun v => v + (a : ℂ)) (x := z) hshift).differentiableAt.differentiableWithinAt
  · intro z _
    filter_upwards [(add_real_tendsto_punctured a z).eventually (hIso (z + (a : ℂ)))] with w hw
    exact fun h => hw h.2.2
  · intro z hz
    have hhalf := hs hz.1
    obtain ⟨c, hc, hReal, b, hb, hp⟩ := hPole _ hz.2 hhalf
    have hshift : AnalyticAt ℂ (fun v : ℂ => v + (a : ℂ)) z := analyticAt_id.add analyticAt_const
    refine ⟨c, hc, fun him => hReal (by simpa only [add_im, ofReal_im, add_zero] using him),
      fun w => b (w + (a : ℂ)), hb.comp (f := fun v => v + (a : ℂ)) (x := z) hshift, ?_⟩
    filter_upwards [(add_real_tendsto_punctured a z).eventually hp] with w hw
    simpa only [add_sub_add_right_eq_sub] using hw

def GaussianCutoffWindowBound (A : ℝ → ℝ) : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      ∀ y ∈ Icc Y (Y ^ (1 + δ)), A y ≤ C * y ^ θ

/-- One integrated window estimate at exponent θ bounds the real part of each
Gaussian pole by θ. The shift into the Landau half-plane leaves the weighted
majorant integral unchanged. -/
theorem gaussianPole_re_le_of_mellin_log_window
    {A : ℝ → ℝ} {Φ : ℂ → ℂ} (hA : Measurable A)
    (hGrowth : ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), |A x| ≤ C * x ^ (2 : ℝ))
    (hAnalytic : ∀ w : ℂ, 1 / 2 < w.re → archivedGaussianFactor w ≠ 0 → AnalyticAt ℂ Φ w)
    (hPole : ∀ ρ ∈ gaussianPoles, 1 / 2 < ρ.re → ∃ c : ℂ, c ≠ 0 ∧
      (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧ ∃ b : ℂ → ℂ, AnalyticAt ℂ b ρ ∧
        ∀ᶠ w in 𝓝[≠] ρ, Φ w = c / (w - ρ) + b w)
    (hTransform : ∀ w : ℂ, 2 < w.re →
      ∫ x in Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 1) = Φ w)
    {θ δ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ)
    (hWindow : Deduction.WindowHypU (fun u => A (Real.exp u)) θ δ)
    {w : ℂ} (hw : w ∈ gaussianPoles) : w.re ≤ θ := by
  by_contra! hright
  let a : ℝ := (1 / 2 + θ) / 2
  have ha : 1 / 2 < a := by dsimp [a]; linarith
  have haθ : a < θ := by dsimp [a]; linarith
  have hData := gaussianLogCutoff_hasPoleData hA hGrowth hAnalytic hPole hTransform ha
  have hWindowShifted : Deduction.WindowHypU (gaussianLogCutoff A a) (θ - a) δ := by
    intro η hη U₀
    obtain ⟨U, hU, R, hR, hUpper, hIntegral⟩ := hWindow η hη U₀
    let R' (u : ℝ) := R u * Real.exp (-a * u)
    have hEq : (fun u => R' u * Real.exp (-(θ - a) * u)) =
        fun u => R u * Real.exp (-θ * u) := by
      funext u
      dsimp only [R']
      rw [mul_assoc, ← Real.exp_add, show -a * u + -(θ - a) * u = -θ * u by ring]
    refine ⟨U, hU, R', ?_, ?_, ?_⟩
    · rw [hEq]
      exact hR
    · intro u hu
      obtain ⟨hR₀, hg⟩ := hUpper u hu
      exact ⟨mul_nonneg hR₀ (Real.exp_nonneg _), mul_le_mul_of_nonneg_right hg (Real.exp_nonneg _)⟩
    · rw [hEq]
      exact hIntegral
  have hz : w - (a : ℂ) ∈ shiftedGaussianPoles a := by
    refine ⟨?_, ?_⟩
    · simp only [sub_re, ofReal_re]; linarith
    · rwa [sub_add_cancel]
  have hle := Deduction.landau_window hData (show 0 < θ - a by linarith)
    (show θ - a < 1 by linarith) hδ hWindowShifted (w - (a : ℂ)) hz
  simp only [sub_re, ofReal_re] at hle
  linarith

/-- A cutoff whose Mellin transform detects the actual Gaussian poles gives the quartic
window test, with the sign of any real residue supplied explicitly. -/
theorem quartic_rh_of_gaussian_mellin_windows (hD : DirichletLZerosOnLine)
    {A : ℝ → ℝ} {Φ : ℂ → ℂ} (hA : Measurable A)
    (hGrowth : ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), |A x| ≤ C * x ^ (2 : ℝ))
    (hAnalytic : ∀ w : ℂ, 1 / 2 < w.re → archivedGaussianFactor w ≠ 0 → AnalyticAt ℂ Φ w)
    (hPole : ∀ ρ ∈ gaussianPoles, 1 / 2 < ρ.re → ∃ c : ℂ, c ≠ 0 ∧
      (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧ ∃ b : ℂ → ℂ, AnalyticAt ℂ b ρ ∧
        ∀ᶠ w in 𝓝[≠] ρ, Φ w = c / (w - ρ) + b w)
    (hTransform : ∀ w : ℂ, 2 < w.re →
      ∫ x in Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 1) = Φ w)
    (hcut : GaussianCutoffWindowBound A) : DedekindZetaRH QuarticModel.K := by
  obtain ⟨hR, hB⟩ := cofactors_on_line hD
  apply archivedQuarticRH_iff_upper_right.mpr
  refine ⟨hR, hB, ?_⟩
  intro w hright hleft _ hz
  have hp : 0 < w.re := by linarith
  have hw : w ∈ gaussianPoles := ⟨hp, (archivedGaussianFactor_zero_iff_mellin hp).mpr hz⟩
  obtain ⟨θ, hθ, hwθ⟩ := exists_between hright
  obtain ⟨δ, hδ, C, hC, hW⟩ := hcut θ hθ (hwθ.trans hleft)
  exact (not_le_of_gt hwθ) (gaussianPole_re_le_of_mellin_log_window
    hA hGrowth hAnalytic hPole hTransform hθ (hwθ.trans hleft) hδ
    (logWindow_of_pointwise_norm_windows A hδ hC hW) hw)

/-- The original cutoff test uses a multiplier that survives at the Gaussian poles. -/
theorem quartic_rh_of_gaussian_cutoff_windows_of_nonzero_at_poles (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    {A : ℝ → ℝ} {M : ℂ → ℂ} (hA : Measurable A)
    (hGrowth : ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), |A x| ≤ C * x ^ (2 : ℝ))
    (hAnalytic : ∀ w : ℂ, 1 / 2 < w.re → AnalyticAt ℂ M w)
    (hNonzero : ∀ w ∈ gaussianPoles, 1 / 2 < w.re → M w ≠ 0)
    (hTransform : ∀ w : ℂ, 2 < w.re →
      ∫ x in Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 1) =
        M w * ((w - 1) * riemannZeta w) *
          (archivedGaussianPrimitiveIndexMellin w - (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w))
    (hcut : GaussianCutoffWindowBound A) : DedekindZetaRH QuarticModel.K := by
  obtain ⟨Ψ, hΨ, hAt, hPole⟩ := archivedGaussianPrimitiveIndexMellin_same_pole
  have hReal := gaussian_poles_nonreal_of_mellin_pos (fun σ _ =>
    archivedMellin_eq_quartic_real_formula ▸ hpos σ)
  refine quartic_rh_of_gaussian_mellin_windows hD (Φ := gaussianCutoffContinuation M Ψ) hA hGrowth
    (fun w hw hne => gaussianCutoffContinuation_analytic (by linarith) (hAnalytic w hw) (hAt w hw hne))
    ?_ ?_ hcut
  · intro ρ hρ hhalf
    obtain ⟨c, hc, b, hb, hEq⟩ := hPole ρ hρ hhalf
    obtain ⟨d, hd, b', hb', hEq'⟩ :=
      gaussianCutoffContinuation_pole hD hhalf (hAnalytic ρ hhalf) (hNonzero ρ hρ hhalf) hc hb hEq
    exact ⟨d, hd, fun him => (hReal ρ hρ him).elim, b', hb', hEq'⟩
  · intro w hw
    have h0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw; linarith
    have h1 : w ≠ 1 := fun h => by rw [h, one_re] at hw; linarith
    rw [gaussianCutoffContinuation, gaussianCutoffMultiplier,
      gaussianWindowZetaFactor_eq h0 h1, hΨ w hw, hTransform w hw]

/-- A cutoff with a nonvanishing multiplier on the half-plane can use the window test. -/
theorem quartic_rh_of_gaussian_cutoff_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    {A : ℝ → ℝ} {M : ℂ → ℂ} (hA : Measurable A)
    (hGrowth : ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), |A x| ≤ C * x ^ (2 : ℝ))
    (hAnalytic : ∀ w : ℂ, 1 / 2 < w.re → AnalyticAt ℂ M w)
    (hNonzero : ∀ w : ℂ, 1 / 2 < w.re → M w ≠ 0)
    (hTransform : ∀ w : ℂ, 1 < w.re →
      ∫ x in Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 1) =
        M w * ((w - 1) * riemannZeta w) *
          (archivedGaussianPrimitiveIndexMellin w - (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w))
    (hcut : GaussianCutoffWindowBound A) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_gaussian_cutoff_windows_of_nonzero_at_poles hD hpos hA hGrowth hAnalytic
    (fun w _ hw => hNonzero w hw) (fun w hw => hTransform w (one_lt_two.trans hw)) hcut

/-- The direct determinant window bound in the original norm variable. -/
def ArchivedGaussianRawWindowBound : Prop :=
  GaussianCutoffWindowBound archivedGaussianRawWindow

theorem quartic_rh_of_archived_gaussian_raw_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : ArchivedGaussianRawWindowBound) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_gaussian_cutoff_windows hD hpos (M := fun w => 1 - (2 : ℂ) ^ (-w))
    archivedGaussianRawWindow_measurable archivedGaussianRawWindow_growth (fun w _ => halfWindowFactor_analytic w)
    (fun _ hw => halfWindowFactor_ne_zero (by linarith))
    (fun _ hw => archivedGaussianRawWindow_mellin hw) hcut

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
#print axioms gaussianLogCutoff_hasPoleData
#print axioms gaussianPole_re_le_of_mellin_log_window
#print axioms quartic_rh_of_gaussian_mellin_windows
#print axioms quartic_rh_of_gaussian_cutoff_windows_of_nonzero_at_poles
#print axioms quartic_rh_of_gaussian_cutoff_windows
#print GaussianCutoffWindowBound
#print ArchivedGaussianRawWindowBound
#check quartic_rh_of_archived_gaussian_raw_windows
#print axioms quartic_rh_of_archived_gaussian_raw_windows
#check quartic_rh_of_archived_gaussian_large_address_windows
#print axioms quartic_rh_of_archived_gaussian_large_address_windows

end
end AlpogeSuperZeta
