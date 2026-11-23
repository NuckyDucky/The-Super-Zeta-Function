import ArchivedDottieTailPartition
import Batteries.Tactic.OpenPrivate
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Absolute majorants for the smoothed Gaussian contour, grouped by the
actual integer coefficient at each norm. -/

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace QuarticModel

open ArithmeticFunction
open private quarterNormFiberEquiv from ArchivedGaussianSeries
open private dottieContour dottieContourMajorant norm_dottieContourIntegrand_le
  from ArchivedDottieTailPartition

private theorem archivedFiber_eq_coefficient (n : ℕ) :
    (∑' p : {p : ℕ × ℕ // archivedQuarterNorm p = n}, archivedQuarterWeight p.val) =
      (archivedLatticeCoeff n : ℂ) := by
  by_cases hn : n = 0
  · let : IsEmpty {p : ℕ × ℕ // archivedQuarterNorm p = n} :=
      ⟨fun p => (archivedQuarterNorm_pos p.val).ne' (p.property.trans hn)⟩
    simp [hn, archivedLatticeCoeff]
  · have hr (p : {p : ℕ × ℕ // archivedQuarterNorm p = n}) :
        archivedQuarterWeight p.val = (archivedIdealCharacter ((quarterNormFiberEquiv n hn p).val) : ℂ) :=
      congrArg (Int.cast : ℤ → ℂ) (gaussianQuarterIdeal_signed_weight p.val).symm
    simp_rw [hr]
    rw [(quarterNormFiberEquiv n hn).tsum_eq
      (fun I : GaussianNormFiber n => (archivedIdealCharacter I.val : ℂ)),
      ← signedIdealCoefficients_eq_archivedLatticeCoeff]
    simp [signedIdealCoefficients, toArithmeticFunction, signedIdealNormSum, hn]

/-- Absolute convergence of the grouped Dirichlet series at the same
completion scale as the archived contour. -/
theorem archivedWeightedCoeff_summable {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖(archivedLatticeCoeff n : ℂ)‖ *
      (archivedThetaScale/(n : ℝ))^σ) := by
  let f (p : ℕ × ℕ) : ℂ := archivedQuarterWeight p *
    ((archivedThetaScale/(archivedQuarterNorm p : ℝ))^σ : ℝ)
  have H : Summable (fun p => ‖f p‖) := by
    refine (archivedQuarter_dirichlet_abs_summable hσ archivedThetaScale_pos).congr ?_
    intro p
    have ht : 0 ≤ archivedThetaScale/(archivedQuarterNorm p : ℝ) :=
      div_nonneg archivedThetaScale_pos.le (Nat.cast_nonneg _)
    have hr : 0 ≤ (archivedQuarterNorm p : ℝ)/archivedThetaScale :=
      div_nonneg (Nat.cast_nonneg _) archivedThetaScale_pos.le
    unfold f
    rw [norm_mul, Complex.norm_of_nonneg (Real.rpow_nonneg ht _),
      show archivedThetaScale/(archivedQuarterNorm p : ℝ) =
        ((archivedQuarterNorm p : ℝ)/archivedThetaScale)⁻¹ by rw [inv_div],
      Real.inv_rpow hr, div_eq_mul_inv]
  have hg := (H.hasSum.tsum_fiberwise archivedQuarterNorm).summable
  apply Summable.of_norm_bounded hg
  intro n
  have hf : Summable (fun p : {p : ℕ × ℕ // archivedQuarterNorm p = n} =>
      ‖f p.val‖) := H.subtype _
  have he : (∑' p : {p : ℕ × ℕ // archivedQuarterNorm p = n}, f p.val) =
      (archivedLatticeCoeff n : ℂ) * ((archivedThetaScale/(n : ℝ))^σ : ℝ) := by
    simp_rw [f, fun p : {p : ℕ × ℕ // archivedQuarterNorm p = n} => p.property]
    rw [tsum_mul_right, archivedFiber_eq_coefficient]
  have hh := norm_tsum_le_tsum_norm hf
  have ht := Real.rpow_nonneg (div_nonneg archivedThetaScale_pos.le (Nat.cast_nonneg (α := ℝ) n)) σ
  rw [he, norm_mul, Complex.norm_of_nonneg ht] at hh
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) ht)]
  exact hh

noncomputable def dottieWeightedContourTerm (w : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  if n = 0 then 0 else
    (archivedLatticeCoeff n : ℂ) /
      (2 * (Real.pi : ℂ) * (archivedDottieCompletionScale : ℂ)) *
    dottieContourIntegrand w n u

theorem dottieSmoothSide_eq_integral (w : ℂ) (n : ℕ) :
    dottieSmoothSide w n = ∫ u : ℝ, dottieWeightedContourTerm w n u := by
  by_cases hn : n = 0
  · simp [dottieSmoothSide, dottieWeightedContourTerm, hn]
  · simp [dottieSmoothSide, dottieWeightedContourTerm, hn, integral_const_mul]

theorem dottieWeightedContourTerm_integrable {w : ℂ} (hw : 0 < w.re+1) (n : ℕ) :
    Integrable (dottieWeightedContourTerm w n) := by
  by_cases hn : n = 0
  · subst n
    change Integrable (fun _ : ℝ => (0 : ℂ))
    exact integrable_zero _ _ _
  · unfold dottieWeightedContourTerm
    simp only [if_neg hn]
    exact (dottieContourIntegrand_integrable hw hn).const_mul _

private noncomputable def dottieContourFactor (w : ℂ) : ℝ :=
  Real.Gamma (w.re+1) * Real.exp (1+Real.pi^2/8) /
    (2*Real.pi*archivedDottieCompletionScale)

private theorem dottieContourFactor_nonneg {w : ℂ} (hw : 0 < w.re+1) :
    0 ≤ dottieContourFactor w := by
  unfold dottieContourFactor
  have hg := Real.Gamma_pos_of_pos hw
  have hs := archivedDottieCompletionScale_pos
  positivity

theorem norm_dottieWeightedContourTerm_le {w : ℂ} (hw : 0 < w.re+1) (n : ℕ) (u : ℝ) :
    ‖dottieWeightedContourTerm w n u‖ ≤
      (‖(archivedLatticeCoeff n : ℂ)‖ * (archivedThetaScale/(n : ℝ))^(w.re+1)) *
        (dottieContourFactor w * Real.exp (-(1/2 : ℝ)*u^2)) := by
  by_cases hn : n = 0
  · simp only [dottieWeightedContourTerm, if_pos hn, norm_zero]
    exact mul_nonneg
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg
        (div_nonneg archivedThetaScale_pos.le (Nat.cast_nonneg _)) _))
      (mul_nonneg (dottieContourFactor_nonneg hw) (Real.exp_pos _).le)
  · have hs := archivedDottieCompletionScale_pos
    have hN : ‖(2 : ℂ)*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)‖ =
        2*Real.pi*archivedDottieCompletionScale := by
      rw [norm_mul, norm_mul, Complex.norm_of_nonneg Real.pi_pos.le,
        Complex.norm_of_nonneg hs.le]
      norm_num
    rw [dottieWeightedContourTerm, if_neg hn, norm_mul, norm_div, hN]
    refine (mul_le_mul_of_nonneg_left (norm_dottieContourIntegrand_le hw hn u) (by positivity)).trans_eq ?_
    unfold dottieContourMajorant dottieContourFactor
    rw [neg_mul]
    ring

theorem dottieWeightedContourTerm_integral_norm_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n => ∫ u : ℝ, ‖dottieWeightedContourTerm w n u‖) := by
  have hw₁ : 0 < w.re+1 := by linarith
  let k := fun u : ℝ => dottieContourFactor w * Real.exp (-(1/2 : ℝ)*u^2)
  have hk : Integrable k := (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)).const_mul _
  have h := (archivedWeightedCoeff_summable (σ := w.re+1) (by linarith)).mul_right (∫ u : ℝ, k u)
  apply Summable.of_norm_bounded h
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  rw [← integral_const_mul]
  exact integral_mono (dottieWeightedContourTerm_integrable hw₁ n).norm
    (hk.const_mul _) (norm_dottieWeightedContourTerm_le hw₁ n)

theorem dottieSmoothSide_norm_summable {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n => ‖dottieSmoothSide w n‖) := by
  apply Summable.of_norm_bounded (dottieWeightedContourTerm_integral_norm_summable hw)
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), dottieSmoothSide_eq_integral]
  exact norm_integral_le_integral_norm _

theorem dottieSmoothTerm_norm_summable {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    Summable (fun n => ‖dottieSmoothTerm w n‖) := by
  have hm : 0 < (1-conj w).re := by simp [hw₁]
  apply Summable.of_norm_bounded ((dottieSmoothSide_norm_summable hw₀).add
    (dottieSmoothSide_norm_summable hm))
  intro n
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simpa only [dottieSmoothTerm, norm_conj] using
    (norm_add_le (dottieSmoothSide w n) (conj (dottieSmoothSide (1-conj w) n)))

/-- The single vertical contour in the archived completed evaluation. -/
noncomputable def dottieCompletedContourIntegrand (w : ℂ) (u : ℝ) : ℂ :=
  let z := dottieContour u
  archivedMellin (w+z) / (2 * (Real.pi : ℂ) * (archivedDottieCompletionScale : ℂ)) *
    Complex.exp (z^2-I*(Real.pi : ℂ)*z/2) / z

private theorem dottieWeightedContourTerm_hasSum {w : ℂ} (hw : 0 < w.re) (u : ℝ) :
    HasSum (fun n => dottieWeightedContourTerm w n u) (dottieCompletedContourIntegrand w u) := by
  let z := dottieContour u
  let s := w+z
  let denominator := (2 : ℂ) * (Real.pi : ℂ) * (archivedDottieCompletionScale : ℂ)
  let weight := Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)
  let multiplier := (archivedThetaScale : ℂ)^s * Gamma s / denominator * weight / z
  have hsre : s.re = w.re+1 := by simp [s, z, dottieContour]
  have hs : 1 < s.re := by rw [hsre]; linarith
  have hΓ := Complex.Gamma_ne_zero_of_re_pos (zero_lt_one.trans hs)
  have hB : (archivedThetaScale : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'))
  have hcompletion : archivedGaussianFactor s * multiplier =
      dottieCompletedContourIntegrand w u := by
    change archivedMellin s * ((archivedThetaScale : ℂ)^s)⁻¹ * (Gamma s)⁻¹ *
      ((archivedThetaScale : ℂ)^s * Gamma s / denominator * weight / z) =
        archivedMellin s / denominator * weight / z
    simp only [div_eq_mul_inv]
    rw [show archivedMellin s * ((archivedThetaScale : ℂ)^s)⁻¹ * (Gamma s)⁻¹ *
      ((archivedThetaScale : ℂ)^s * Gamma s * denominator⁻¹ * weight * z⁻¹) =
      (((archivedThetaScale : ℂ)^s)⁻¹ * (archivedThetaScale : ℂ)^s) *
        ((Gamma s)⁻¹ * Gamma s) * (archivedMellin s * denominator⁻¹ * weight * z⁻¹) by ring]
    rw [inv_mul_cancel₀ hB, inv_mul_cancel₀ hΓ, one_mul, one_mul]
  have h := (archivedGaussianFactor_hasSum hs).mul_right multiplier
  rw [hcompletion] at h
  refine h.congr_fun ?_
  intro n
  by_cases hn : n = 0
  · simp [hn, dottieWeightedContourTerm, LSeries.term_zero]
  · have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hd : 0 < archivedThetaScale / (n : ℝ) := div_pos archivedThetaScale_pos hp
    have hN : (n : ℂ)^s ≠ 0 := Complex.cpow_ne_zero_iff.mpr
      (Or.inl (by exact_mod_cast hn))
    have he : ((archivedThetaScale/(n : ℝ) : ℝ) : ℂ)^s * (n : ℂ)^s =
        (archivedThetaScale : ℂ)^s := by
      rw [← Complex.ofReal_natCast, ← Complex.mul_cpow_ofReal_nonneg hd.le hp.le,
        ← Complex.ofReal_mul, div_mul_cancel₀ _ hp.ne']
    have he' := ((eq_div_iff hN).mpr he)
    rw [LSeries.term_of_ne_zero hn, signedIdealCoefficients_eq_archivedLatticeCoeff]
    simp only [dottieWeightedContourTerm, if_neg hn, dottieContourIntegrand]
    change (archivedLatticeCoeff n : ℂ) / denominator *
      (((archivedThetaScale/(n : ℝ) : ℝ) : ℂ)^s * Gamma s * weight / z) =
        ((archivedLatticeCoeff n : ℂ) / (n : ℂ)^s) * multiplier
    rw [he']
    unfold multiplier
    ring

/-- The contour integral of the completion on the right-hand line equals
the sum of the original smoothed positive-height norm terms. -/
theorem dottieSmoothSide_hasSum_completed_contour {w : ℂ} (hw : 0 < w.re) :
    HasSum (dottieSmoothSide w) (∫ u : ℝ, dottieCompletedContourIntegrand w u) := by
  have hw₁ : 0 < w.re+1 := by linarith
  have h := MeasureTheory.hasSum_integral_of_summable_integral_norm
    (dottieWeightedContourTerm_integrable hw₁) (dottieWeightedContourTerm_integral_norm_summable hw)
  have he : (∫ u : ℝ, ∑' n, dottieWeightedContourTerm w n u) =
      ∫ u : ℝ, dottieCompletedContourIntegrand w u :=
    integral_congr_ae (Filter.Eventually.of_forall fun u =>
      (dottieWeightedContourTerm_hasSum hw u).tsum_eq)
  rw [he] at h
  exact h.congr_fun (dottieSmoothSide_eq_integral w)

#print axioms archivedWeightedCoeff_summable
#print axioms dottieWeightedContourTerm_integral_norm_summable
#print axioms dottieSmoothTerm_norm_summable
#print axioms dottieSmoothSide_hasSum_completed_contour

end QuarticModel
