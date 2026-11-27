import DedekindMixedTheta
import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.TailRemainder

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex MeasureTheory Set
open DedekindZetaZeroFree.AbelianQuotient

noncomputable section

/-- The self-dual mixed theta integrand on the positive half of the Mellin split. -/
def mixedThetaIntegrand (K : Type) [Field K] [NumberField K] (w : ℂ) (t : ℝ) : ℂ :=
  ((t : ℂ) ^ (w - 1) + (t : ℂ) ^ (-w)) *
    ((Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀)

private theorem mixedThetaIntegrand_parts (K : Type) [Field K] [NumberField K] (w : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w - 1) *
      ((Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀)) (Ioi 1) ∧
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-w) *
      ((Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀)) (Ioi 1) := by
  let P := Theta.mixedThetaPair K
  have hk : P.k = 1 := Theta.mixedThetaPair_k K
  have hg : P.g = P.f := DedekindZetaZeroFree.Hecke.mixedThetaPair_global_selfDual K
  have hg₀ : P.g₀ = P.f₀ := DedekindZetaZeroFree.Hecke.mixedThetaPair_global_g₀_eq_f₀ K
  exact ⟨DedekindZetaZeroFree.Hecke.mellinSplitRemainder_f_integrable P hk w,
    by simpa only [hg, hg₀] using
      DedekindZetaZeroFree.Hecke.mellinSplitRemainder_g_integrable P hk w⟩

theorem mixedTheta_mellin_eq_integral (K : Type) [Field K] [NumberField K] (w : ℂ) :
    (Theta.mixedThetaPair K).Λ₀ w = ∫ t : ℝ in Ioi 1, mixedThetaIntegrand K w t := by
  let P := Theta.mixedThetaPair K
  have hk : P.k = 1 := Theta.mixedThetaPair_k K
  have hg : P.g = P.f := DedekindZetaZeroFree.Hecke.mixedThetaPair_global_selfDual K
  have hg₀ : P.g₀ = P.f₀ := DedekindZetaZeroFree.Hecke.mixedThetaPair_global_g₀_eq_f₀ K
  have he : P.ε = 1 := DedekindZetaZeroFree.Hecke.mixedThetaPair_global_ε_eq_one K
  obtain ⟨ha, hb⟩ := mixedThetaIntegrand_parts K w
  change P.Λ₀ w = _
  rw [DedekindZetaZeroFree.Hecke.mellinSplitRemainder P hk w, he, one_mul, hg, hg₀]
  simpa only [mixedThetaIntegrand, add_mul] using (integral_add ha hb).symm

/-- Retain the integral from one to the stated cutoff. -/
def mixedThetaTruncation (K : Type) [Field K] [NumberField K] (R : ℝ) (w : ℂ) : ℂ :=
  ∫ t : ℝ in 1..R, mixedThetaIntegrand K w t

/-- Both Mellin weights have norm at most one on the closed critical strip.
The tail majorant is independent of height before clearing the poles. -/
theorem mixedTheta_mellin_tail_le
    (K : Type) [Field K] [NumberField K] (R : ℝ) (hR : 1 ≤ R)
    (w : ℂ) (hw₀ : 0 ≤ w.re) (hw₁ : w.re ≤ 1) :
    ‖(Theta.mixedThetaPair K).Λ₀ w - mixedThetaTruncation K R w‖ ≤
      2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ := by
  let P := Theta.mixedThetaPair K
  obtain ⟨ha, hb⟩ := mixedThetaIntegrand_parts K w
  have hi : IntegrableOn (mixedThetaIntegrand K w) (Ioi 1) := by
    convert ha.add hb using 1
    funext t
    simp only [mixedThetaIntegrand, Pi.add_apply, add_mul]
  have hiR := hi.mono_set (Ioi_subset_Ioi hR)
  have hf : IntegrableOn (fun t : ℝ => ‖P.f t - P.f₀‖) (Ioi 1) := by
    have ha₁ := (mixedThetaIntegrand_parts K (1 : ℂ)).1
    exact (by simpa only [sub_self, cpow_zero, one_mul] using ha₁ :
      IntegrableOn (fun t : ℝ => P.f t - P.f₀) (Ioi 1)).norm
  have hsplit := intervalIntegral.integral_interval_add_Ioi hi hiR
  rw [mixedTheta_mellin_eq_integral, ← hsplit, mixedThetaTruncation, add_sub_cancel_left]
  calc
    ‖∫ t : ℝ in Ioi R, mixedThetaIntegrand K w t‖ ≤
        ∫ t : ℝ in Ioi R, ‖mixedThetaIntegrand K w t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi R, 2 * ‖P.f t - P.f₀‖ := by
      apply integral_mono_ae hiR.norm ((hf.mono_set (Ioi_subset_Ioi hR)).const_mul 2)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht₁ : 1 ≤ t := hR.trans (le_of_lt (mem_Ioi.mp ht))
      have ht₀ : 0 < t := zero_lt_one.trans_le ht₁
      have h₁ : ‖(t : ℂ) ^ (w - 1)‖ ≤ 1 := by
        rw [norm_cpow_eq_rpow_re_of_pos ht₀, sub_re, one_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos ht₁ (sub_nonpos.mpr hw₁)
      have h₀ : ‖(t : ℂ) ^ (-w)‖ ≤ 1 := by
        rw [norm_cpow_eq_rpow_re_of_pos ht₀, neg_re]
        exact Real.rpow_le_one_of_one_le_of_nonpos ht₁ (neg_nonpos.mpr hw₀)
      change ‖((t : ℂ) ^ (w - 1) + (t : ℂ) ^ (-w)) * (P.f t - P.f₀)‖ ≤ _
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans ?_) (norm_nonneg _)
      linarith
    _ = _ := integral_const_mul _ _

/-- An arbitrary signed axis can use the absolute tail after multiplication by
the explicit pole-clearing and axis factors. -/
theorem mixedTheta_signed_truncation_error_le
    (K : Type) [Field K] [NumberField K] (R : ℝ) (hR : 1 ≤ R)
    (axis w : ℂ) (hw₀ : 0 ≤ w.re) (hw₁ : w.re ≤ 1) :
    (axis * (w * (1 - w) * (Theta.mixedThetaPair K).Λ₀ w - (Theta.mixedThetaPair K).f₀) -
      axis * (w * (1 - w) * mixedThetaTruncation K R w - (Theta.mixedThetaPair K).f₀)).im ≤
      ‖axis * (w * (1 - w))‖ *
        (2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖) := by
  have h := mixedTheta_mellin_tail_le K R hR w hw₀ hw₁
  have halg :
      axis * (w * (1 - w) * (Theta.mixedThetaPair K).Λ₀ w - (Theta.mixedThetaPair K).f₀) -
        axis * (w * (1 - w) * mixedThetaTruncation K R w - (Theta.mixedThetaPair K).f₀) =
      axis * (w * (1 - w)) * ((Theta.mixedThetaPair K).Λ₀ w - mixedThetaTruncation K R w) := by
    ring
  rw [halg]
  exact (le_abs_self _).trans ((abs_im_le_norm _).trans
    ((norm_mul _ _).le.trans (mul_le_mul_of_nonneg_left h (norm_nonneg _))))

/-- A signed upper bound on the finite integral plus its tail excludes a zero at
the original candidate point. -/
theorem mixedTheta_ne_zero_of_signed_truncation
    (K : Type) [Field K] [NumberField K] {Z : ℂ → ℂ} (hZ : IsDedekindZeta K Z)
    (R : ℝ) (hR : 1 ≤ R) (axis w : ℂ) (hw₀ : 0 < w.re) (hw₁ : w.re < 1)
    (hgap : (axis * (w * (1 - w) * mixedThetaTruncation K R w - (Theta.mixedThetaPair K).f₀)).im +
      ‖axis * (w * (1 - w))‖ *
        (2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖) < 0) :
    Z w ≠ 0 := by
  intro hz
  have hread := (mixedTheta_reading_eq_iff_zero K hZ w hw₀ hw₁).mpr hz
  have htail := mixedTheta_signed_truncation_error_le K R hR axis w hw₀.le hw₁.le
  rw [hread, sub_self, mul_zero, zero_sub, neg_im] at htail
  linarith

#print axioms mixedTheta_mellin_eq_integral
#print axioms mixedTheta_mellin_tail_le
#print axioms mixedTheta_signed_truncation_error_le
#print axioms mixedTheta_ne_zero_of_signed_truncation

end

end FieldTarget
