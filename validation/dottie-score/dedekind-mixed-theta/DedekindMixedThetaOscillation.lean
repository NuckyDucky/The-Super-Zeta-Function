import DedekindMixedThetaTail
import Mathlib.Analysis.Calculus.MeanValue

/-! The retained folded integral has a finite Lipschitz bound on the critical
strip. It only needs a scalar integral of the field's theta kernel. -/

namespace FieldTarget

open Complex MeasureTheory Set
open DedekindZetaZeroFree.AbelianQuotient

private theorem exp_difference_le_of_re_nonpos {a b : ℂ} (ha : a.re ≤ 0) (hb : b.re ≤ 0) :
    ‖exp a - exp b‖ ≤ ‖a - b‖ := by
  let S : Set ℂ := {z | z.re ≤ 0}
  have hS : Convex ℝ S := by
    intro x hx y hy a b ha hb _
    change (a • x + b • y).re ≤ 0
    rw [add_re, smul_re, smul_re]
    exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
      (mul_nonpos_of_nonneg_of_nonpos hb hy)
  have h := hS.norm_image_sub_le_of_norm_hasDerivWithin_le (C := (1 : ℝ))
    (fun z _ => (Complex.hasDerivAt_exp z).hasDerivWithinAt)
    (fun z hz => by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      exact hz)
    (show b ∈ S from hb) (show a ∈ S from ha)
  simpa only [one_mul] using h

private theorem cpow_difference_le {t : ℝ} (ht : 1 ≤ t) {a b : ℂ}
    (ha : a.re ≤ 0) (hb : b.re ≤ 0) :
    ‖(t : ℂ)^a - (t : ℂ)^b‖ ≤ Real.log t * ‖a - b‖ := by
  have hx : 0 < t := zero_lt_one.trans_le ht
  have hx0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hlog := Real.log_nonneg ht
  let L : ℂ := (Real.log t : ℂ)
  have hLa : (L * a).re ≤ 0 := by
    simpa [L, Complex.mul_re] using mul_nonpos_of_nonneg_of_nonpos hlog ha
  have hLb : (L * b).re ≤ 0 := by
    simpa [L, Complex.mul_re] using mul_nonpos_of_nonneg_of_nonpos hlog hb
  rw [Complex.cpow_def_of_ne_zero hx0, Complex.cpow_def_of_ne_zero hx0,
    ← Complex.ofReal_log hx.le]
  calc
    ‖exp (L * a) - exp (L * b)‖ ≤ ‖L * a - L * b‖ :=
      exp_difference_le_of_re_nonpos hLa hLb
    _ = _ := by
      rw [← mul_sub, norm_mul, show L = (Real.log t : ℂ) from rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]

/-- The two reflected powers each have modulus variation bounded by
`log t * ‖w - v‖` throughout the closed critical strip. -/
theorem mixedThetaIntegrand_difference_le (K : Type) [Field K] [NumberField K]
    {t : ℝ} (ht : 1 ≤ t) {w v : ℂ}
    (hw₀ : 0 ≤ w.re) (hw₁ : w.re ≤ 1) (hv₀ : 0 ≤ v.re) (hv₁ : v.re ≤ 1) :
    ‖mixedThetaIntegrand K w t - mixedThetaIntegrand K v t‖ ≤
      (2 * Real.log t * ‖w - v‖) *
        ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ := by
  have h1 := cpow_difference_le ht
    (a := w - 1) (b := v - 1)
    (by simpa [sub_re] using sub_nonpos.mpr hw₁)
    (by simpa [sub_re] using sub_nonpos.mpr hv₁)
  rw [show w - 1 - (v - 1) = w - v by ring] at h1
  have h2 := cpow_difference_le ht (a := -w) (b := -v)
    (by simpa [neg_re] using neg_nonpos.mpr hw₀)
    (by simpa [neg_re] using neg_nonpos.mpr hv₀)
  rw [show -w - -v = -(w - v) by ring, norm_neg] at h2
  let g := (Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀
  have hdiff : mixedThetaIntegrand K w t - mixedThetaIntegrand K v t =
      (((t : ℂ)^(w - 1) - (t : ℂ)^(v - 1)) + ((t : ℂ)^(-w) - (t : ℂ)^(-v))) * g := by
    simp only [mixedThetaIntegrand, g]
    ring
  rw [hdiff, norm_mul]
  refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans ?_) (norm_nonneg _)
  change ‖(t : ℂ) ^ (w - 1) - (t : ℂ) ^ (v - 1)‖ +
      ‖(t : ℂ) ^ (-w) - (t : ℂ) ^ (-v)‖ ≤ 2 * Real.log t * ‖w - v‖
  have h := add_le_add h1 h2
  linarith only [h]

private theorem mixedThetaIntegrand_intervalIntegrable (K : Type) [Field K] [NumberField K]
    {R : ℝ} (hR : 1 ≤ R) (w : ℂ) : IntervalIntegrable (mixedThetaIntegrand K w) volume 1 R := by
  let P := Theta.mixedThetaPair K
  have hk : P.k = 1 := Theta.mixedThetaPair_k K
  have hf := DedekindZetaZeroFree.Hecke.mellinSplitRemainder_f_integrable P hk w
  have hg := DedekindZetaZeroFree.Hecke.mellinSplitRemainder_g_integrable P hk w
  rw [DedekindZetaZeroFree.Hecke.mixedThetaPair_global_selfDual K,
    DedekindZetaZeroFree.Hecke.mixedThetaPair_global_g₀_eq_f₀ K] at hg
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr
  have h := (hf.add hg).mono_set (Ioc_subset_Ioi_self : Ioc (1 : ℝ) R ⊆ Ioi 1)
  convert h using 1
  funext t
  simp only [mixedThetaIntegrand, add_mul, Pi.add_apply, P]

/-- The finite Mellin integral varies by at most the input distance times a
height-independent scalar budget. This is a norm bound on the actual
pair, with both exact Mellin weights. -/
theorem mixedThetaTruncation_difference_le (K : Type) [Field K] [NumberField K]
    {R : ℝ} (hR : 1 ≤ R) {w v : ℂ}
    (hw₀ : 0 ≤ w.re) (hw₁ : w.re ≤ 1) (hv₀ : 0 ≤ v.re) (hv₁ : v.re ≤ 1) :
    ‖mixedThetaTruncation K R w - mixedThetaTruncation K R v‖ ≤
      (2 * Real.log R * ‖w - v‖) *
        ∫ t : ℝ in 1..R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ := by
  let P := Theta.mixedThetaPair K
  let D := fun t : ℝ => ‖P.f t - P.f₀‖
  let M := 2 * Real.log R * ‖w - v‖
  have hk : P.k = 1 := Theta.mixedThetaPair_k K
  have hD : IntervalIntegrable D volume 1 R := by
    have h := DedekindZetaZeroFree.Hecke.mellinSplitRemainder_f_integrable P hk 1
    have h' : IntegrableOn (fun t : ℝ => P.f t - P.f₀) (Ioi 1) := by
      simpa only [sub_self, cpow_zero, one_mul] using h
    have hnorm : IntegrableOn D (Ioi 1) := h'.norm
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr (hnorm.mono_set Ioc_subset_Ioi_self)
  have hw := mixedThetaIntegrand_intervalIntegrable K hR w
  have hv := mixedThetaIntegrand_intervalIntegrable K hR v
  rw [mixedThetaTruncation, mixedThetaTruncation, ← intervalIntegral.integral_sub hw hv]
  calc
    _ ≤ ∫ t : ℝ in 1..R, ‖mixedThetaIntegrand K w t - mixedThetaIntegrand K v t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hR
    _ ≤ ∫ t : ℝ in 1..R, M * D t := by
      apply intervalIntegral.integral_mono_on hR (hw.sub hv).norm (hD.const_mul M)
      intro t ht
      refine (mixedThetaIntegrand_difference_le K ht.1 hw₀ hw₁ hv₀ hv₁).trans ?_
      have hLog := Real.log_le_log (zero_lt_one.trans_le ht.1) ht.2
      unfold M D P
      gcongr
    _ = _ := intervalIntegral.integral_const_mul M D

#print axioms mixedThetaIntegrand_difference_le
#print axioms mixedThetaTruncation_difference_le

end FieldTarget
