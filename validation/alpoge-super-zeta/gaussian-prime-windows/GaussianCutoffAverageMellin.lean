import GaussianDivisorSquaredWindow
import Mathlib.MeasureTheory.Integral.Prod

/-! Mellin transport for averaging the squared cutoff before subtracting its endpoint. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory Set QuarticModel FieldTarget ArtinPrimitiveRootsConjecture
open scoped Classical

noncomputable section

/-- Averaging with coefficient two and subtracting the endpoint kills a linear term. -/
def averagedCutoff (A : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 / x) * (∫ t in Ioc (1 : ℝ) x, A t) - A x

theorem averagedCutoff_eq_interval (A : ℝ → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    averagedCutoff A x = (2 / x) * (∫ t in 1..x, A t) - A x := by
  rw [averagedCutoff, intervalIntegral.integral_of_le hx]

theorem averagedCutoff_measurable {A : ℝ → ℝ} (hA : Measurable A) : Measurable (averagedCutoff A) := by
  let F (z : ℝ × ℝ) := if z.2 ≤ z.1 then A z.2 else 0
  have hF : Measurable F := Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    (hA.comp measurable_snd) measurable_const
  have hmeas := hF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (1 : ℝ)))
  have heq : (fun x : ℝ => ∫ t in Ioc (1 : ℝ) x, A t) =
      fun x => ∫ t in Ioi (1 : ℝ), F (x, t) := by
    funext x
    have h : (fun t => F (x, t)) = (Iic x).indicator A := by
      funext t
      simp [F, indicator, mem_Iic]
    rw [h, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]
  have hI : Measurable (fun x : ℝ => ∫ t in Ioc (1 : ℝ) x, A t) := by
    rw [heq]
    exact hmeas.measurable
  exact ((measurable_const.div measurable_id).mul hI).sub hA

theorem averagedCutoff_abs_le {A : ℝ → ℝ} {e C x : ℝ} (hx : 1 ≤ x)
    (he : 0 ≤ e) (hC : 0 ≤ C) (hA : ∀ y ≥ (1 : ℝ), |A y| ≤ C * y ^ e) :
    |averagedCutoff A x| ≤ (3 * C) * x ^ e := by
  have hx₀ := one_pos.trans_le hx
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := A) (a := 1) (b := x) (C := C * x ^ e) (fun t ht => by
      have htx : t ∈ Ioc (1 : ℝ) x := by rwa [uIoc_of_le hx] at ht
      rw [Real.norm_eq_abs]
      exact (hA t htx.1.le).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (zero_le_one.trans htx.1.le) htx.2 he) hC))
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx)] at h
  rw [averagedCutoff_eq_interval A hx]
  calc
    _ ≤ |2 / x * (∫ t in 1..x, A t)| + |A x| := abs_sub _ _
    _ ≤ (2 / x) * ((C * x ^ e) * (x - 1)) + C * x ^ e := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 / x)]
      exact add_le_add (mul_le_mul_of_nonneg_left h (by positivity)) (hA x hx)
    _ ≤ (2 / x) * ((C * x ^ e) * x) + C * x ^ e := by
      exact add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sub_le_self x zero_le_one) (by positivity : 0 ≤ C * x ^ e))
        (by positivity : 0 ≤ (2 : ℝ) / x)) le_rfl
    _ = _ := by field_simp; ring

private theorem cutoff_cpow_measurable (z : ℂ) :
    Measurable ((Ioi (1 : ℝ)).piecewise (fun x => (x : ℂ) ^ z) (fun _ => 0)) := by
  apply ContinuousOn.measurable_piecewise _ continuous_zero.continuousOn measurableSet_Ioi
  intro x hx
  exact (Complex.continuousAt_ofReal_cpow_const x z
    (Or.inr (one_pos.trans (show 1 < x from hx)).ne')).continuousWithinAt

private theorem cutoff_mellin_integrable {A : ℝ → ℝ} (hA : Measurable A)
    {C : ℝ} (hbound : ∀ x ≥ (1 : ℝ), |A x| ≤ C * x ^ (2 : ℝ))
    {w : ℂ} (hw : 2 < w.re) :
    IntegrableOn (fun x : ℝ => (A x : ℂ) * (x : ℂ) ^ (-w - 1)) (Ioi 1) := by
  let μ : Measure ℝ := volume.restrict (Ioi 1)
  let G := (Ioi (1 : ℝ)).piecewise (fun x => (x : ℂ) ^ (-w - 1)) (fun _ => 0)
  have hmaj : Integrable (fun x : ℝ => C * x ^ (1 - w.re)) μ :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : 1 - w.re < -1) one_pos).const_mul C
  have heq : ∀ᵐ x ∂μ, G x = (x : ℂ) ^ (-w - 1) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun x hx => piecewise_eq_of_mem _ _ _ hx
  have hmeas : AEStronglyMeasurable (fun x => (A x : ℂ) * G x) μ :=
    ((Complex.continuous_ofReal.measurable.comp hA).mul
      (cutoff_cpow_measurable (-w - 1))).aestronglyMeasurable
  apply hmaj.mono' (hmeas.congr (heq.mono fun x hx => by simp only [hx]))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx₁ : 1 < x := hx
  have hx₀ := one_pos.trans hx₁
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hx₀]
  calc
    _ ≤ (C * x ^ (2 : ℝ)) * x ^ (-w - 1).re :=
      mul_le_mul_of_nonneg_right (hbound x hx₁.le) (Real.rpow_nonneg hx₀.le _)
    _ = C * x ^ (1 - w.re) := by
      rw [mul_assoc, ← Real.rpow_add hx₀]
      congr 2
      simp only [sub_re, neg_re, one_re]
      ring

theorem averagedCutoff_mellin {A : ℝ → ℝ} (hA : Measurable A)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x ≥ (1 : ℝ), |A x| ≤ C * x ^ (2 : ℝ))
    {w : ℂ} (hw : 2 < w.re) :
    ∫ x in Ioi (1 : ℝ), (averagedCutoff A x : ℂ) * (x : ℂ) ^ (-w - 1) =
      ((1 - w) / (w + 1)) *
        ∫ x in Ioi (1 : ℝ), (A x : ℂ) * (x : ℂ) ^ (-w - 1) := by
  let μ : Measure ℝ := volume.restrict (Ioi 1)
  let G := (Ioi (1 : ℝ)).piecewise (fun x => (x : ℂ) ^ (-w - 2)) (fun _ => 0)
  let F (x t : ℝ) := if t ≤ x then (A t : ℂ) * (x : ℂ) ^ (-w - 2) else 0
  let F' (z : ℝ × ℝ) := if z.2 ≤ z.1 then (A z.2 : ℂ) * G z.1 else 0
  have hFm : Measurable F' := Measurable.ite (measurableSet_le measurable_snd measurable_fst)
    ((Complex.continuous_ofReal.measurable.comp (hA.comp measurable_snd)).mul
      ((cutoff_cpow_measurable (-w - 2)).comp measurable_fst)) measurable_const
  have hpair : ∀ᵐ z ∂μ.prod μ, z ∈ Ioi (1 : ℝ) ×ˢ Ioi (1 : ℝ) := by
    dsimp only [μ]
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
  have hFeq : F' =ᵐ[μ.prod μ] Function.uncurry F := hpair.mono fun z hz => by
    simp only [F', G, piecewise_eq_of_mem _ _ _ hz.1, Function.uncurry, F]
  let e := -w.re / 2
  have he : e < -1 := by dsimp [e]; linarith
  have hpow : Integrable (fun x : ℝ => x ^ e) μ := integrableOn_Ioi_rpow_of_lt he one_pos
  have hmaj := (hpow.const_mul C).mul_prod hpow
  have hFint : Integrable (Function.uncurry F) (μ.prod μ) := by
    apply hmaj.mono' (hFm.aestronglyMeasurable.congr hFeq)
    filter_upwards [hpair] with z hz
    have hx : 1 < z.1 := hz.1
    have ht : 1 < z.2 := hz.2
    have hx₀ := one_pos.trans hx
    have ht₀ := one_pos.trans ht
    simp only [Function.uncurry, F]
    split
    · rename_i htx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cpow_eq_rpow_re_of_pos hx₀]
      have heq : (-w - 2).re = 2 * e - 2 := by
        simp only [sub_re, neg_re, show (2 : ℂ).re = 2 from rfl]; dsimp [e]; ring
      rw [heq]
      calc
        _ ≤ (C * z.2 ^ (2 : ℝ)) * z.1 ^ (2 * e - 2) :=
          mul_le_mul_of_nonneg_right (hbound z.2 ht.le) (Real.rpow_nonneg hx₀.le _)
        _ = (C * (z.2 ^ (2 - e) * z.2 ^ e)) * z.1 ^ (2 * e - 2) := by
          rw [← Real.rpow_add ht₀, show 2 - e + e = 2 by ring]
        _ ≤ (C * (z.1 ^ (2 - e) * z.2 ^ e)) * z.1 ^ (2 * e - 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow ht₀.le htx (by linarith)) (Real.rpow_nonneg ht₀.le _)) hC)
            (Real.rpow_nonneg hx₀.le _)
        _ = (C * z.1 ^ e) * z.2 ^ e := by
          calc
            _ = C * (z.1 ^ (2 - e) * z.1 ^ (2 * e - 2)) * z.2 ^ e := by ring
            _ = _ := by rw [← Real.rpow_add hx₀, show 2 - e + (2 * e - 2) = e by ring]
    · rw [norm_zero]
      exact mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hx₀.le _)) (Real.rpow_nonneg ht₀.le _)
  let I (x : ℝ) := ∫ t in Ioc (1 : ℝ) x, A t
  let M (x : ℝ) := (A x : ℂ) * (x : ℂ) ^ (-w - 1)
  let N (x : ℝ) := (I x : ℂ) * (x : ℂ) ^ (-w - 2)
  have hleft (x : ℝ) : (∫ t, F x t ∂μ) = N x := by
    have h : F x = (Iic x).indicator (fun t => (A t : ℂ) * (x : ℂ) ^ (-w - 2)) := by
      funext t
      simp [F, indicator, mem_Iic]
    rw [h]
    change (∫ t in Ioi (1 : ℝ), _) = _
    rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic, integral_mul_const]
    unfold N I
    rw [integral_complex_ofReal]
  have hright (t : ℝ) (ht : 1 < t) : (∫ x, F x t ∂μ) = M t / (w + 1) := by
    have h : (fun x => F x t) = (Ici t).indicator (fun x => (A t : ℂ) * (x : ℂ) ^ (-w - 2)) := by
      funext x
      simp [F, indicator, mem_Ici]
    have hset : Ioi (1 : ℝ) ∩ Ici t = Ici t :=
      inter_eq_right.mpr fun _ hx => ht.trans_le hx
    have hs : (-w - 2).re < -1 := by
      simp only [sub_re, neg_re, show (2 : ℂ).re = 2 from rfl]
      linarith
    rw [h]
    change (∫ x in Ioi (1 : ℝ), _) = _
    rw [setIntegral_indicator measurableSet_Ici, hset, integral_const_mul, integral_Ici_eq_integral_Ioi,
      integral_Ioi_cpow_of_lt hs (one_pos.trans ht)]
    dsimp [M]
    rw [show -w - 2 + 1 = -(w + 1) by ring, div_neg, neg_div, neg_neg,
      show -(w + 1) = -w - 1 by ring]
    ring
  have hNM : (∫ x, N x ∂μ) = (∫ x, M x ∂μ) / (w + 1) := by
    calc
      _ = ∫ x, ∫ t, F x t ∂μ ∂μ := integral_congr_ae (Eventually.of_forall fun x => (hleft x).symm)
      _ = ∫ t, ∫ x, F x t ∂μ ∂μ := integral_integral_swap hFint
      _ = ∫ t, M t / (w + 1) ∂μ := integral_congr_ae
        ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hright t ht)
      _ = _ := MeasureTheory.integral_div _ _
  have hN : Integrable N μ := hFint.integral_prod_left.congr (Eventually.of_forall hleft)
  have hM : Integrable M μ := cutoff_mellin_integrable hA hbound hw
  have hs (x : ℝ) (hx : 1 < x) :
      (averagedCutoff A x : ℂ) * (x : ℂ) ^ (-w - 1) = 2 * N x - M x := by
    have hx₀ : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (one_pos.trans hx).ne'
    have hpow' : (x : ℂ) ^ (-w - 2) = (x : ℂ) ^ (-w - 1) * (x : ℂ)⁻¹ := by
      rw [show -w - 2 = (-w - 1) + (-1) by ring, cpow_add _ _ hx₀, cpow_neg_one]
    unfold averagedCutoff
    push_cast
    dsimp only [N, M, I]
    rw [hpow']
    ring
  change (∫ x, (_ : ℂ) ∂μ) = ((1 - w) / (w + 1)) * (∫ x, M x ∂μ)
  rw [integral_congr_ae ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => hs x hx),
    integral_sub (hN.const_mul 2) hM, integral_const_mul, hNM]
  have hden : w + 1 ≠ 0 := by
    intro h
    have heq := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at heq
    linarith
  field_simp
  ring

theorem quartic_rh_of_averaged_squared_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound (averagedCutoff archivedGaussianSquaredWindow)) :
    DedekindZetaRH QuarticModel.K := by
  let M (w : ℂ) := ((1 - w) / (w + 1)) * (2 / ((w + 1) * (w + 2)))
  have hm : Measurable archivedGaussianSquaredWindow := indexedSquaredRamp_measurable _ _
  have h₁ (w : ℂ) (hw : 1 / 2 < w.re) : w + 1 ≠ 0 := by
    intro h
    have heq := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at heq
    linarith
  have h₂ (w : ℂ) (hw : 1 / 2 < w.re) : w + 2 ≠ 0 := by
    intro h
    have heq := congrArg Complex.re h
    simp only [add_re, show (2 : ℂ).re = 2 from rfl, zero_re] at heq
    linarith
  obtain ⟨C, hC, hb⟩ := archivedGaussianSquaredWindow_growth
  apply quartic_rh_of_gaussian_cutoff_windows_of_nonzero_at_poles hD hpos
    (M := M) (averagedCutoff_measurable hm) ⟨3 * C, by positivity,
      fun _ hx => averagedCutoff_abs_le hx (by norm_num) hC hb⟩
  · intro w hw
    exact ((analyticAt_const.sub analyticAt_id).div (analyticAt_id.add analyticAt_const)
      (h₁ w hw)).mul (analyticAt_const.div
      ((analyticAt_id.add analyticAt_const).mul (analyticAt_id.add analyticAt_const))
      (mul_ne_zero (h₁ w hw) (h₂ w hw)))
  · intro w hw hw_re
    have hReal := gaussian_poles_nonreal_of_mellin_pos (fun σ _ =>
      archivedMellin_eq_quartic_real_formula ▸ hpos σ)
    have hw₁ : 1 ≠ w := by
      intro h
      exact hReal w hw (by rw [← h, one_im])
    exact mul_ne_zero (div_ne_zero (sub_ne_zero.mpr hw₁) (h₁ w hw_re))
      (div_ne_zero (by norm_num) (mul_ne_zero (h₁ w hw_re) (h₂ w hw_re)))
  · intro w hw
    rw [averagedCutoff_mellin hm hC hb hw, archivedGaussianSquaredWindow_mellin (one_lt_two.trans hw)]
    dsimp [M]
    ring
  · exact hcut

#print axioms averagedCutoff_mellin
#print axioms quartic_rh_of_averaged_squared_windows

end

end AlpogeSuperZeta
