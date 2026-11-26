import GaussianVaughanHigherContinuation
import GaussianVaughanGammaStrip
import Mathlib.Analysis.Complex.PhragmenLindelof

/-! Polynomial strip growth for the actual Gaussian factor, via its
theta reflection and the absolutely convergent right edge. -/

namespace AlpogeSuperZeta

open Asymptotics Complex Filter MeasureTheory QuarticModel Set
open scoped Topology

noncomputable section

private def scaledTheta (t : ℝ) : ℂ := archivedTheta (t / archivedThetaScale)

private theorem scaledTheta_mellinConvergent {w : ℂ} (hw : 0 < w.re) :
    MellinConvergent scaledTheta w := by
  have hcont : ContinuousOn scaledTheta (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn (archivedTheta_continuous_positive.comp
      (continuous_id.div_const _).continuousOn (fun t ht => div_pos ht archivedThetaScale_pos))
  have hC : 0 < 2 * archivedThetaScale := by positivity [archivedThetaScale_pos]
  have hb : scaledTheta =O[𝓝[>] (0 : ℝ)] (fun t => t ^ (-(0 : ℝ))) := by
    apply IsBigO.of_bound (2 * archivedThetaScale)
    have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < (2 * archivedThetaScale)⁻¹ :=
      nhdsWithin_le_nhds (Iio_mem_nhds (inv_pos.mpr hC))
    filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ)), hsmall] with t ht hsmall
    let y := t⁻¹ / archivedThetaScale
    have hy : 2 ≤ y := (le_div_iff₀ archivedThetaScale_pos).2
      ((le_inv_comm₀ hC ht).2 hsmall.le)
    have hty : t⁻¹ = archivedThetaScale * y := by
      dsimp [y]
      field_simp [archivedThetaScale_pos.ne']
    have hye : y * Real.exp (-y) ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), one_mul]
      linarith [Real.add_one_le_exp y]
    have ht₀ : 0 < t := ht
    simp only [scaledTheta, Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero,
      abs_one, mul_one, archivedTheta_reflection t ht₀, abs_mul, abs_of_pos (inv_pos.mpr ht₀)]
    calc
      _ ≤ t⁻¹ * (2 * Real.exp (-y)) :=
        mul_le_mul_of_nonneg_left (archivedTheta_exp_bound hy) (inv_nonneg.mpr ht.le)
      _ = (2 * archivedThetaScale) * (y * Real.exp (-y)) := by rw [hty]; ring
      _ ≤ _ := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hye hC.le
  exact mellinConvergent_of_isBigO_rpow_exp (one_div_pos.mpr archivedThetaScale_pos)
    (hcont.locallyIntegrableOn measurableSet_Ioi) archivedTheta_exponential_decay hb hw

private theorem norm_mellin_le_endpoints {f : ℝ → ℂ} {a b : ℝ} {z : ℂ}
    (ha : MellinConvergent f (a : ℂ)) (hb : MellinConvergent f (b : ℂ))
    (hz₁ : a ≤ z.re) (hz₂ : z.re ≤ b) :
    ‖mellin f z‖ ≤
      ∫ t in Ioi (0 : ℝ), (‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖ +
        ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖) := by
  unfold mellin
  apply norm_integral_le_of_norm_le (ha.norm.add hb.norm)
  apply (ae_restrict_iff' measurableSet_Ioi).2
  filter_upwards with t ht
  have ht₀ : 0 < t := ht
  change ‖(t : ℂ) ^ (z - 1) • f t‖ ≤
    ‖(t : ℂ) ^ ((a : ℂ) - 1) • f t‖ + ‖(t : ℂ) ^ ((b : ℂ) - 1) • f t‖
  simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht₀, sub_re, one_re, ofReal_re]
  by_cases hc : t ≤ 1
  · exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge ht₀ hc (by linarith))
      (norm_nonneg _)).trans (le_add_of_nonneg_right (by positivity))
  · exact (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (le_of_not_ge hc) (by linarith))
      (norm_nonneg _)).trans (le_add_of_nonneg_left (by positivity))

theorem archivedMellin_bounded_on_strip :
    ∃ A ≥ 0, ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 → ‖archivedMellin z‖ ≤ A := by
  let A := ∫ t in Ioi (0 : ℝ), (‖(t : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - 1) • scaledTheta t‖ +
    ‖(t : ℂ) ^ (((2 : ℝ) : ℂ) - 1) • scaledTheta t‖)
  have hb {z : ℂ} (h₁ : 1 / 2 ≤ z.re) (h₂ : z.re ≤ 2) :
      ‖archivedMellin z‖ ≤ A :=
    norm_mellin_le_endpoints (scaledTheta_mellinConvergent (by norm_num))
      (scaledTheta_mellinConvergent (by norm_num)) h₁ h₂
  refine ⟨A, (norm_nonneg _).trans (hb (z := 1) (by norm_num) (by norm_num)),
    fun z hz₁ hz₂ => ?_⟩
  by_cases h : 1 / 2 ≤ z.re
  · exact hb h hz₂
  rw [← archivedMellin_functional_equation z]
  exact hb (by simp [sub_re]; linarith) (by simp [sub_re]; linarith)

private theorem gaussianFactor_right_bound :
    ∃ B ≥ 0, ∀ z : ℂ, 2 ≤ z.re → ‖archivedGaussianFactor z‖ ≤ B := by
  let b := fun n : ℕ => ‖LSeries.term QuarticModel.signedIdealCoefficients (2 : ℂ) n‖
  have hb : Summable b := (archivedGaussianFactor_hasSum (w := 2) (by norm_num)).LSeriesSummable.norm
  refine ⟨∑' n, b n, tsum_nonneg (fun _ => norm_nonneg _), fun z hz => ?_⟩
  have hnorm : ∀ n, ‖LSeries.term signedIdealCoefficients z n‖ ≤ b n :=
    fun n => LSeries.norm_term_le_of_re_le_re _ (s := (2 : ℂ)) (by simpa using hz) n
  have h := hb.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
  rw [← (archivedGaussianFactor_hasSum (w := z) (by linarith)).LSeries_eq]
  exact (norm_tsum_le_tsum_norm h).trans (h.tsum_le_tsum hnorm hb)

theorem archivedMellin_eq_gaussian_completion {z : ℂ} (hz : 0 < z.re) :
    archivedMellin z =
      archivedGaussianFactor z * (archivedThetaScale : ℂ) ^ z * Complex.Gamma z := by
  have hc : (archivedThetaScale : ℂ) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'))
  have hΓ := Complex.Gamma_ne_zero_of_re_pos hz
  unfold archivedGaussianFactor
  field_simp

private theorem gaussianFactor_reflect {z : ℂ} (hz : z.re < 1) :
    archivedGaussianFactor z =
      (archivedThetaScale : ℂ) ^ (1 - 2 * z) * (Complex.Gamma (1 - z) / Complex.Gamma z) *
        archivedGaussianFactor (1 - z) := by
  let c : ℂ := archivedThetaScale
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have hpow : c ^ (1 - z) * (c ^ z)⁻¹ = c ^ (1 - 2 * z) := by
    rw [← cpow_neg, ← cpow_add _ _ hc]
    congr 1
    ring
  conv_lhs =>
    rw [archivedGaussianFactor, ← archivedMellin_functional_equation z,
      archivedMellin_eq_gaussian_completion (by simp [sub_re]; linarith : 0 < (1 - z).re)]
  rw [← hpow]
  ring

private theorem one_le_norm_add_two {z : ℂ} (hz : -1 ≤ z.re) : 1 ≤ ‖z + 2‖ := by
  have h := Complex.re_le_norm (z + 2)
  norm_num [add_re] at h
  linarith

private def normalizedGaussianFactor (z : ℂ) : ℂ := archivedGaussianFactor z / (z + 2) ^ 3

private theorem norm_normalizedGaussianFactor_le {z : ℂ} (hz : -1 ≤ z.re) :
    ‖normalizedGaussianFactor z‖ ≤ ‖archivedGaussianFactor z‖ := by
  rw [normalizedGaussianFactor, norm_div, norm_pow]
  exact div_le_self (norm_nonneg _) (one_le_pow₀ (one_le_norm_add_two hz))

private theorem gaussianFactor_normalized_left {z : ℂ} (hz : z.re = -1) :
    ‖normalizedGaussianFactor z‖ ≤ archivedThetaScale ^ (3 : ℕ) * ‖archivedGaussianFactor (1 - z)‖ := by
  have hr := gaussianFactor_reflect (by linarith : z.re < 1)
  have hcpow : ‖(archivedThetaScale : ℂ) ^ (1 - 2 * z)‖ = archivedThetaScale ^ (3 : ℕ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos archivedThetaScale_pos, sub_re, one_re, mul_re, hz]
    norm_num [Real.rpow_natCast]
  have he : z = -(1 : ℂ) + (z.im : ℂ) * I := by
    apply Complex.ext
    · simp [hz, mul_re]
    · simp [mul_im]
  have hγratio : ‖Complex.Gamma (1 - z) / Complex.Gamma z‖ = |z.im| * (1 + z.im ^ 2) := by
    have hArg : 1 + (1 : ℂ) - (z.im : ℂ) * I = 1 - z := by
      calc
        _ = 1 - (-(1 : ℂ) + (z.im : ℂ) * I) := by ring
        _ = _ := by rw [← he]
    have hh := gaussianGamma_left_ratio_norm 1 z.im
    simpa only [Nat.cast_one, hArg, ← he, Finset.prod_range_one, Nat.cast_zero, zero_add, one_pow] using hh
  have hnorm : ‖z + 2‖ ^ 2 = 1 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [add_re, add_im, hz]
    ring
  have hγbd : ‖Complex.Gamma (1 - z) / Complex.Gamma z‖ ≤ ‖z + 2‖ ^ 3 := by
    have hi : |z.im| ≤ ‖z + 2‖ := by simpa [add_im] using Complex.abs_im_le_norm (z + 2)
    rw [hγratio, ← hnorm]
    exact (mul_le_mul_of_nonneg_right hi (by positivity : 0 ≤ ‖z + 2‖ ^ 2)).trans
      (by ring_nf; exact le_rfl)
  have hden : 0 < ‖z + 2‖ ^ 3 := by linarith [one_le_pow₀ (n := 3) (one_le_norm_add_two hz.ge)]
  rw [normalizedGaussianFactor, norm_div, norm_pow, div_le_iff₀ hden]
  conv_lhs => rw [hr, norm_mul, norm_mul, hcpow]
  have hc : 0 ≤ archivedThetaScale ^ (3 : ℕ) := by positivity [archivedThetaScale_pos]
  calc
    _ ≤ (archivedThetaScale ^ (3 : ℕ) * ‖z + 2‖ ^ 3) * ‖archivedGaussianFactor (1 - z)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hγbd hc) (norm_nonneg _)
    _ = _ := by ring

private theorem norm_scale_inv_le {z : ℂ} (hz₁ : -1 ≤ z.re) (hz₂ : z.re ≤ 2) :
    ‖((archivedThetaScale : ℂ) ^ z)⁻¹‖ ≤
      max (archivedThetaScale ^ (-2 : ℝ)) archivedThetaScale := by
  rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos archivedThetaScale_pos,
    ← Real.rpow_neg archivedThetaScale_pos.le]
  by_cases hc : 1 ≤ archivedThetaScale
  · exact (Real.rpow_le_rpow_of_exponent_le hc (by linarith : -z.re ≤ 1)).trans
      (by rw [Real.rpow_one]; exact le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge archivedThetaScale_pos (le_of_not_ge hc)
      (by linarith : (-2 : ℝ) ≤ -z.re)).trans (le_max_left _ _)

set_option maxHeartbeats 800000 in
/-- The same archived Gaussian factor used in the field theorem grows
at most cubically on the strip needed for the contour and the derivative. -/
theorem archivedGaussianFactor_polynomial_on_strip :
    ∃ C ≥ 0, ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 →
      ‖archivedGaussianFactor z‖ ≤ C * ‖z + 2‖ ^ 3 := by
  obtain ⟨A, hA, hM⟩ := archivedMellin_bounded_on_strip
  obtain ⟨B, hB, hR⟩ := gaussianFactor_right_bound
  obtain ⟨J, hJ, hΓ⟩ := inv_gamma_bound_on_strip
  let P := max (archivedThetaScale ^ (-2 : ℝ)) archivedThetaScale
  have hP : 0 ≤ P := archivedThetaScale_pos.le.trans (le_max_right _ _)
  let C := max (archivedThetaScale ^ (3 : ℕ) * B) B
  have hC : 0 ≤ C := hB.trans (le_max_right _ _)
  have hdiff : DiffContOnCl ℂ normalizedGaussianFactor (re ⁻¹' Ioo (-1 : ℝ) 2) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    have hclosure : closure (re ⁻¹' Ioo (-1 : ℝ) 2) ⊆ re ⁻¹' Icc (-1 : ℝ) 2 :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self)
        (isClosed_Icc.preimage Complex.continuous_re)
    have hz' : -1 ≤ z.re := (hclosure hz).1
    have hden : (z + 2 : ℂ) ≠ 0 := by
      intro he
      have := one_le_norm_add_two hz'
      rw [he, norm_zero] at this
      norm_num at this
    have hlin : DifferentiableAt ℂ (fun w : ℂ => w + 2) z := differentiableAt_id.add_const 2
    have hq : DifferentiableAt ℂ normalizedGaussianFactor z :=
      (archivedGaussianFactor_entire z).div (hlin.pow 3) (pow_ne_zero 3 hden)
    exact hq.differentiableWithinAt
  have hBig (z : ℂ) (hz₁ : -1 ≤ z.re) (hz₂ : z.re ≤ 2) (ht : 1 ≤ |z.im|) :
      ‖normalizedGaussianFactor z‖ ≤ (A * P * J) * Real.exp (Real.pi * |z.im|) := by
    refine (norm_normalizedGaussianFactor_le hz₁).trans ?_
    unfold archivedGaussianFactor
    simp only [norm_mul]
    calc
      _ ≤ (A * P) * (J * Real.exp (Real.pi * |z.im|)) :=
        mul_le_mul (mul_le_mul (hM z hz₁ hz₂) (norm_scale_inv_le hz₁ hz₂)
          (norm_nonneg _) hA) (hΓ z hz₁ hz₂ ht) (norm_nonneg _) (mul_nonneg hA hP)
      _ = _ := by ring
  have hgrowth : ∃ c < Real.pi / (2 - (-1 : ℝ)), ∃ D,
      normalizedGaussianFactor =O[comap (|·.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo (-1 : ℝ) 2)]
        (fun z => Real.exp (D * Real.exp (c * |z.im|))) := by
    refine ⟨1 / 2, by linarith [Real.pi_gt_three], 2 * Real.pi, ?_⟩
    apply IsBigO.of_bound (A * P * J)
    have hLate : ∀ᶠ z : ℂ in comap (|·.im|) atTop, 1 ≤ |z.im| :=
      (eventually_ge_atTop (1 : ℝ)).comap _
    have hInside : ∀ᶠ z : ℂ in comap (|·.im|) atTop ⊓ 𝓟 (re ⁻¹' Ioo (-1 : ℝ) 2),
        z ∈ re ⁻¹' Ioo (-1 : ℝ) 2 :=
      eventually_inf_principal.mpr (Eventually.of_forall fun _ hz => hz)
    filter_upwards [hLate.filter_mono inf_le_left, hInside] with z ht hz
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine (hBig z hz.1.le hz.2.le ht).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    apply Real.exp_le_exp.mpr
    have hle : |z.im| ≤ 2 * Real.exp (1 / 2 * |z.im|) := by
      linarith [Real.add_one_le_exp (1 / 2 * |z.im|)]
    nlinarith [mul_le_mul_of_nonneg_left hle Real.pi_pos.le]
  have hLeft (z : ℂ) (hz : z.re = -1) : ‖normalizedGaussianFactor z‖ ≤ C :=
    (gaussianFactor_normalized_left hz).trans
      ((mul_le_mul_of_nonneg_left (hR (1 - z) (by rw [sub_re, one_re, hz]; norm_num))
        (by positivity [archivedThetaScale_pos])).trans (le_max_left _ _))
  have hRight (z : ℂ) (hz : z.re = 2) : ‖normalizedGaussianFactor z‖ ≤ C :=
    ((norm_normalizedGaussianFactor_le (by linarith)).trans (hR z hz.ge)).trans (le_max_right _ _)
  refine ⟨C, hC, fun z hz₁ hz₂ => ?_⟩
  have h := PhragmenLindelof.vertical_strip hdiff hgrowth hLeft hRight hz₁ hz₂
  rw [normalizedGaussianFactor, norm_div, norm_pow] at h
  exact (div_le_iff₀ (by linarith [one_le_pow₀ (n := 3) (one_le_norm_add_two hz₁)])).mp h

#check archivedGaussianFactor_polynomial_on_strip
#print axioms archivedMellin_bounded_on_strip
#print axioms archivedGaussianFactor_polynomial_on_strip

end
end AlpogeSuperZeta
