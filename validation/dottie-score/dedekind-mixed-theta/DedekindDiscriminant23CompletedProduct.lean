import DedekindDiscriminant23ClassSeries
import DedekindDiscriminant23ThetaProfiles
import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.TailRemainder
import DedekindZetaZeroFree.LFunctions.Dedekind.MixedThetaPairMellin
import DedekindZetaZeroFree.Theta.Inversion.MixedPairGlobalSelfDuality
import Mathlib.Analysis.Complex.CauchyIntegral

namespace FieldTarget

open scoped NumberField nonZeroDivisors
open NumberField NumberField.InfinitePlace MeasureTheory Set Filter
open DedekindZetaZeroFree.AbelianQuotient
open DedekindZetaZeroFree.AbelianQuotient.Theta
open DedekindZetaZeroFree.Hecke

noncomputable section

local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "C23" => ClassGroup (𝓞 F23)
local notation "L23" => Discriminant23GaloisField
local notation "c₂" => discriminant23NormTwoClass

/-- The folded Mellin weight in the positive radial variable. -/
def discriminant23FoldWeight (w : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (w - 1) + (t : ℂ) ^ (-w)

private theorem classPair_const_eq_one (C : C23) :
    (idealClassThetaPair F23 C).f₀ = 1 ∧ (idealClassThetaPair F23 C).g₀ = 1 := by
  change ((alpha F23 : ℂ) = 1) ∧ ((alpha F23 : ℂ) = 1)
  rw [discriminant23_theta_alpha_eq_one, Complex.ofReal_one]
  exact ⟨rfl, rfl⟩

theorem discriminant23_fold_integrable (C : C23) (w : ℂ) :
    IntegrableOn (fun t ↦ discriminant23FoldWeight w t * discriminant23ClassKernel C t)
      (Ioi 1) := by
  let P := idealClassThetaPair F23 C
  have ha := mellinSplitRemainder_f_integrable P rfl w
  have hb := mellinSplitRemainder_g_integrable P rfl w
  have h := ha.add hb
  refine h.congr_fun (fun t ht ↦ ?_) measurableSet_Ioi
  obtain ⟨hf₀, hg₀⟩ := classPair_const_eq_one C
  have hp : 0 < t := zero_lt_one.trans ht
  change (t : ℂ) ^ (w - 1) * (P.f t - P.f₀) +
      (t : ℂ) ^ (-w) * (P.g t - P.g₀) = _
  rw [hf₀, hg₀, discriminant23_classPair_primal C t hp, discriminant23_classPair_dual C t hp,
    discriminant23FoldWeight, add_mul]

/-- The two halves of a completed class Mellin value use the same kernel
for this quadratic field. -/
theorem discriminant23_classLambdaZero_eq_fold (C : C23) (w : ℂ) :
    (idealClassThetaPair F23 C).Λ₀ w =
      ∫ t : ℝ in Ioi 1, discriminant23FoldWeight w t * discriminant23ClassKernel C t := by
  let P := idealClassThetaPair F23 C
  have ha := mellinSplitRemainder_f_integrable P rfl w
  have hb := mellinSplitRemainder_g_integrable P rfl w
  change P.Λ₀ w = _
  rw [mellinSplitRemainder P rfl w, show P.ε = 1 from rfl, one_mul, ← integral_add ha hb]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  obtain ⟨hf₀, hg₀⟩ := classPair_const_eq_one C
  have hp : 0 < t := zero_lt_one.trans ht
  change (t : ℂ) ^ (w - 1) * (P.f t - P.f₀) +
      (t : ℂ) ^ (-w) * (P.g t - P.g₀) =
        discriminant23FoldWeight w t * discriminant23ClassKernel C t
  rw [hf₀, hg₀, discriminant23_classPair_primal C t hp, discriminant23_classPair_dual C t hp,
    discriminant23FoldWeight, add_mul]

private theorem classLambdaZero_inv_eq (w : ℂ) :
    (idealClassThetaPair F23 c₂⁻¹).Λ₀ w = (idealClassThetaPair F23 c₂).Λ₀ w := by
  rw [discriminant23_classLambdaZero_eq_fold, discriminant23_classLambdaZero_eq_fold]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact congrArg (discriminant23FoldWeight w t * ·) (discriminant23_classKernel_inv c₂ t)

/-- The sum of the three folded class readings. -/
def discriminant23TotalFold (w : ℂ) : ℂ :=
  (idealClassThetaPair F23 1).Λ₀ w + 2 * (idealClassThetaPair F23 c₂).Λ₀ w

/-- The principal reading minus one nonprincipal reading. -/
def discriminant23CharacterFold (w : ℂ) : ℂ :=
  (idealClassThetaPair F23 1).Λ₀ w - (idealClassThetaPair F23 c₂).Λ₀ w

private theorem sum_three_classes (f : C23 → ℂ) :
    (∑ C, f C) = f 1 + f c₂ + f c₂⁻¹ := by
  classical
  have hInv : c₂⁻¹ ≠ 1 := fun h ↦ discriminant23_normTwoClass_ne_one (inv_eq_one.mp h)
  have h : (Finset.univ : Finset C23) = {1, c₂, c₂⁻¹} := by
    ext C
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
    exact discriminant23_class_candidates C
  rw [h]
  simp [discriminant23_normTwoClass_ne_one.symm, discriminant23_normTwoClass_ne_inv,
    hInv.symm, add_assoc]

private theorem two_character_values {k : ℕ} (hk : k = 1 ∨ k = 2) :
    discriminant23ClassCharacter c₂ ^ k + discriminant23ClassCharacter c₂⁻¹ ^ k = -1 := by
  let u := discriminant23ClassCharacter c₂
  have hCube : u ^ 3 = 1 := discriminant23ClassCharacter_cube c₂
  have hNe : u ≠ 1 := by
    intro h
    apply discriminant23_normTwoClass_ne_one
    apply discriminant23ClassCharacter_injective
    simpa [u] using h
  have hTri : u ^ 2 + u + 1 = 0 := by
    have h := show (u - 1) * (u ^ 2 + u + 1) = 0 by linear_combination hCube
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hNe)
  have hC : c₂ ^ 3 = 1 := by
    apply discriminant23ClassCharacter_injective
    rw [map_pow, map_one]
    exact hCube
  have hInv : c₂⁻¹ = c₂ ^ 2 := by
    apply mul_left_cancel (a := c₂)
    rw [mul_inv_cancel, ← pow_succ', hC]
  rw [hInv, map_pow]
  change u ^ k + (u ^ 2) ^ k = -1
  rcases hk with rfl | rfl
  · linear_combination hTri
  · linear_combination hTri + u * hCube

private theorem lambda_sub_of_self_dual_constants (P : WeakFEPair ℂ)
    (hk : P.k = 1) (hε : P.ε = 1) (h0 : P.g₀ = P.f₀)
    (w : ℂ) (hw₀ : w ≠ 0) (hw₁ : w ≠ 1) :
    P.Λ w = P.Λ₀ w - P.f₀ / (w * (1 - w)) := by
  rw [WeakFEPair.Λ, hk, hε, h0, Complex.ofReal_one, smul_eq_mul, smul_eq_mul]
  field_simp [hw₀, sub_ne_zero.mpr hw₁.symm]
  ring

private theorem class_lambda_sub (C : C23) (w : ℂ) (hw₀ : w ≠ 0) (hw₁ : w ≠ 1) :
    (idealClassThetaPair F23 C).Λ w =
      (idealClassThetaPair F23 C).Λ₀ w - 1 / (w * (1 - w)) := by
  obtain ⟨hf₀, hg₀⟩ := classPair_const_eq_one C
  rw [lambda_sub_of_self_dual_constants _ rfl rfl (hg₀.trans hf₀.symm) w hw₀ hw₁, hf₀]

private theorem completed_base_eq_total {w : ℂ} (hw : 1 < w.re) :
    zetaGammaFactor F23 w * dedekindZeta F23 w =
      discriminant23TotalFold w - 3 / (w * (1 - w)) := by
  have h₀ : w ≠ 0 := by rintro rfl; norm_num at hw
  have h₁ : w ≠ 1 := by rintro rfl; norm_num at hw
  rw [← sum_partialDedekindZeta F23 hw, Finset.mul_sum]
  simp_rw [← idealClassThetaPair_eq_completedPartial F23 _ hw, class_lambda_sub _ _ h₀ h₁]
  rw [sum_three_classes, classLambdaZero_inv_eq, discriminant23TotalFold]
  ring

private theorem completed_character_eq_fold {k : ℕ} (hk : k = 1 ∨ k = 2) {w : ℂ}
    (hw : 1 < w.re) :
    zetaGammaFactor F23 w * discriminant23ClassSeries k w = discriminant23CharacterFold w := by
  have h₀ : w ≠ 0 := by rintro rfl; norm_num at hw
  have h₁ : w ≠ 1 := by rintro rfl; norm_num at hw
  rw [discriminant23_classSeries_eq_sum_partial k hw, Finset.mul_sum]
  simp_rw [mul_left_comm (zetaGammaFactor F23 w), ← idealClassThetaPair_eq_completedPartial F23 _ hw,
    class_lambda_sub _ _ h₀ h₁]
  rw [sum_three_classes, classLambdaZero_inv_eq, discriminant23CharacterFold, map_one, one_pow, one_mul,
    add_assoc, ← add_mul, two_character_values hk]
  ring

private theorem gamma_eq_base_cube (w : ℂ) :
    zetaGammaFactor L23 w = zetaGammaFactor F23 w ^ 3 := by
  let : IsTotallyComplex F23 := discriminant23_quadratic_totallyComplex
  have hReal := IsTotallyComplex.nrRealPlaces_eq_zero F23
  have hComplex : nrComplexPlaces F23 = 1 := by
    have h := discriminant23_quadratic_place_count
    rwa [card_eq_nrRealPlaces_add_nrComplexPlaces, hReal, zero_add] at h
  unfold zetaGammaFactor
  rw [discriminant23_completion_factor, hReal, hComplex,
    discriminant23_quadratic_discriminant, Complex.Gammaℂ_def]
  norm_num
  ring

private theorem field_lambda_eq_gamma_zeta {w : ℂ} (hw : 1 < w.re) :
    (mixedThetaPair L23).Λ w = zetaGammaFactor L23 w * dedekindZeta L23 w :=
  ((mixedThetaPair L23).hasMellin hw).2.symm.trans (hasMellin_mixedThetaPair L23 hw).2

private theorem continued_product_right {w : ℂ} (hw : 1 < w.re) :
    w * (1 - w) * (mixedThetaPair L23).Λ₀ w - (mixedThetaPair L23).f₀ =
      (w * (1 - w) * discriminant23TotalFold w - 3) * discriminant23CharacterFold w ^ 2 := by
  have h₀ : w ≠ 0 := by rintro rfl; norm_num at hw
  have h₁ : w ≠ 1 := by rintro rfl; norm_num at hw
  let P := mixedThetaPair L23
  have hΛ := lambda_sub_of_self_dual_constants P rfl rfl
    (mixedThetaPair_global_g₀_eq_f₀ L23) w h₀ h₁
  have hVal : P.Λ w =
      (discriminant23TotalFold w - 3 / (w * (1 - w))) * discriminant23CharacterFold w ^ 2 := by
    change (mixedThetaPair L23).Λ w = _
    rw [field_lambda_eq_gamma_zeta hw, gamma_eq_base_cube, discriminant23_dedekindZeta_eq_classSeries hw,
      show zetaGammaFactor F23 w ^ 3 *
          (dedekindZeta F23 w * discriminant23ClassSeries 1 w * discriminant23ClassSeries 2 w) =
        (zetaGammaFactor F23 w * dedekindZeta F23 w) *
          (zetaGammaFactor F23 w * discriminant23ClassSeries 1 w) *
          (zetaGammaFactor F23 w * discriminant23ClassSeries 2 w) by ring,
      completed_base_eq_total hw, completed_character_eq_fold (Or.inl rfl) hw,
      completed_character_eq_fold (Or.inr rfl) hw]
    ring
  rw [hΛ] at hVal
  change w * (1 - w) * P.Λ₀ w - P.f₀ = _
  linear_combination (norm := (field_simp [h₀, sub_ne_zero.mpr h₁.symm]; ring))
    (w * (1 - w)) * hVal

/-- The prime-factor identity continues to the whole plane after the two
poles are cleared. All functions here use the same complex input. -/
theorem discriminant23_continued_completed_class_product (w : ℂ) :
    w * (1 - w) * (mixedThetaPair L23).Λ₀ w - (mixedThetaPair L23).f₀ =
      (w * (1 - w) * discriminant23TotalFold w - 3) * discriminant23CharacterFold w ^ 2 := by
  let lhs : ℂ → ℂ := fun z ↦ z * (1 - z) * (mixedThetaPair L23).Λ₀ z - (mixedThetaPair L23).f₀
  let rhs : ℂ → ℂ := fun z ↦
    (z * (1 - z) * discriminant23TotalFold z - 3) * discriminant23CharacterFold z ^ 2
  have hp : Differentiable ℂ (fun z : ℂ ↦ z * (1 - z)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have ha := (idealClassThetaPair F23 1).differentiable_Λ₀
  have hb := (idealClassThetaPair F23 c₂).differentiable_Λ₀
  have ht : Differentiable ℂ discriminant23TotalFold :=
    ha.add ((differentiable_const (2 : ℂ)).mul hb)
  have hc : Differentiable ℂ discriminant23CharacterFold := ha.sub hb
  have hL : Differentiable ℂ lhs :=
    (hp.mul (mixedThetaPair L23).differentiable_Λ₀).sub (differentiable_const _)
  have hR : Differentiable ℂ rhs :=
    ((hp.mul ht).sub (differentiable_const (3 : ℂ))).mul (hc.pow 2)
  have hOpen : ∀ᶠ z in nhds (2 : ℂ), 1 < z.re :=
    (isOpen_lt (continuous_const : Continuous (fun _ : ℂ ↦ (1 : ℝ)))
      Complex.continuous_re).mem_nhds (show 1 < (2 : ℂ).re by norm_num)
  have hEv : lhs =ᶠ[nhds (2 : ℂ)] rhs := by
    filter_upwards [hOpen] with z hz
    exact continued_product_right hz
  exact congrFun ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hL).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hR) hEv) w

#check @discriminant23_continued_completed_class_product
#print axioms discriminant23_classLambdaZero_eq_fold
#print axioms discriminant23_continued_completed_class_product

end
end FieldTarget
