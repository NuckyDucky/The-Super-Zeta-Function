import DedekindDiscriminant23CompletedProduct
import DedekindMixedThetaCompletedRings
import Discriminant23DottieDisk

namespace FieldTarget

open scoped NumberField
open NumberField MeasureTheory Set ArtinPrimitiveRootsConjecture
open SuperZeta.StirlingCorrection

noncomputable section

local notation "L23" => Discriminant23GaloisField
local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "c₂" => discriminant23NormTwoClass

private def thetaAt (Q : ℤ → ℤ → ℤ) (t : ℝ) : ℝ :=
  classThetaStar Q (Real.exp (-discriminant23ThetaScale * t))

private def thetaSum (t : ℝ) : ℝ :=
  thetaAt discriminant23PrincipalForm t + 2 * thetaAt discriminant23OtherForm t

private def thetaDifference (t : ℝ) : ℝ :=
  thetaAt discriminant23PrincipalForm t - thetaAt discriminant23OtherForm t

private theorem fold_translate (H : ℝ → ℝ) (w : ℂ) :
    (∫ t : ℝ in Ioi 1, discriminant23FoldWeight w t * (H t : ℂ)) =
      2 * classMellinReading (fun t ↦ H (1 + t)) w := by
  let g : ℝ → ℂ := fun t ↦ discriminant23FoldWeight w t * H t
  have h := (measurePreserving_add_right volume (1 : ℝ)).setIntegral_preimage_emb
    (Homeomorph.addRight (1 : ℝ)).measurableEmbedding g (Ioi 1)
  have hSet : (fun x : ℝ ↦ x + 1) ⁻¹' Ioi 1 = Ioi 0 := by
    ext x
    change 1 < x + 1 ↔ 0 < x
    constructor <;> intro hx <;> linarith
  rw [hSet] at h
  change (∫ t in Ioi 1, g t) = _
  rw [← h, classMellinReading, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hp : 0 < x + 1 := by
    have : 0 < x := hx
    linarith
  have hPow (z : ℂ) : ((x + 1 : ℝ) : ℂ) ^ z =
      Complex.exp (z * (Real.log (1 + x) : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
      ← Complex.ofReal_log hp.le, add_comm x 1, mul_comm]
  change discriminant23FoldWeight w (x + 1) * ↑(H (x + 1)) =
    2 * (↑(H (1 + x)) * classMellinWeight w (Real.log (1 + x)))
  rw [discriminant23FoldWeight, hPow, hPow, classMellinWeight, add_comm x 1]
  ring

private theorem total_fold_eq_dottie (w : ℂ) :
    discriminant23TotalFold w = 2 * discriminant23TotalClassReading w := by
  have hp := discriminant23_fold_integrable (1 : ClassGroup (𝓞 F23)) w
  have hn := discriminant23_fold_integrable c₂ w
  rw [discriminant23TotalFold, discriminant23_classLambdaZero_eq_fold,
    discriminant23_classLambdaZero_eq_fold, ← integral_const_mul, ← integral_add hp (hn.const_mul 2)]
  trans ∫ t : ℝ in Ioi 1, discriminant23FoldWeight w t * (thetaSum t : ℂ)
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [discriminant23ClassKernel,
      ite_eq_right discriminant23_normTwoClass_ne_one, thetaSum, thetaAt]
    push_cast
    ring
  · exact fold_translate thetaSum w

private theorem character_fold_eq_dottie (w : ℂ) :
    discriminant23CharacterFold w = 2 * discriminant23CharacterClassReading w := by
  have hp := discriminant23_fold_integrable (1 : ClassGroup (𝓞 F23)) w
  have hn := discriminant23_fold_integrable c₂ w
  rw [discriminant23CharacterFold, discriminant23_classLambdaZero_eq_fold,
    discriminant23_classLambdaZero_eq_fold, ← integral_sub hp hn]
  trans ∫ t : ℝ in Ioi 1, discriminant23FoldWeight w t * (thetaDifference t : ℂ)
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [discriminant23ClassKernel,
      ite_eq_right discriminant23_normTwoClass_ne_one, thetaDifference, thetaAt]
    push_cast
    ring
  · exact fold_translate thetaDifference w

/-- The folded Dedekind reading is the explicit class product everywhere away
from the two poles, with the library's factor of eight. -/
theorem discriminant23_completedFold_eq_classProduct_off_poles (w : ℂ)
    (h₀ : w ≠ 0) (h₁' : w ≠ 1) :
    (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair L23).Λ₀ w -
      (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair L23).f₀ / (w * (1 - w)) =
        8 * discriminant23CompletedClassProduct w := by
  have h₁ : 1 - w ≠ 0 := sub_ne_zero.mpr h₁'.symm
  have hPole : w * (1 - w) ≠ 0 := mul_ne_zero h₀ h₁
  let A := discriminant23TotalClassReading w
  let C := discriminant23CharacterClassReading w
  have hModel : discriminant23CompletedClassProduct w = (A - (3 / 2 : ℂ) / (w * (1 - w))) * C ^ 2 :=
    rfl
  have h := discriminant23_continued_completed_class_product w
  rw [total_fold_eq_dottie, character_fold_eq_dottie] at h
  change _ = (w * (1 - w) * (2 * A) - 3) * (2 * C) ^ 2 at h
  rw [hModel]
  apply (mul_left_cancel₀ hPole)
  calc
    _ = w * (1 - w) * (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair L23).Λ₀ w -
          (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair L23).f₀ := by
      field_simp [h₀, h₁]
    _ = _ := h.trans (by field_simp [h₀, h₁]; ring)

/-- The actual completed Dedekind reading is the explicit class product
on the open critical strip. -/
theorem discriminant23_completedReading_eq_classProduct (w : ℂ)
    (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaCompletedReading L23 w = 8 * discriminant23CompletedClassProduct w := by
  have h₀ : w ≠ 0 := by rintro rfl; norm_num at hlo
  have h₁ : w ≠ 1 := by rintro rfl; norm_num at hhi
  rw [mixedThetaCompletedReading_eq_mellin L23 w hlo hhi]
  exact discriminant23_completedFold_eq_classProduct_off_poles w h₀ h₁

/-- The actual pole-cleared readings have one relative factor, the square
of the class-character fold, at the same input throughout the strip. -/
theorem discriminant23_signedReading_eq_base_mul_character_sq (w : ℂ)
    (h0 : 0 < w.re) (h1 : w.re < 1) :
    mixedThetaSignedReading L23 w =
      mixedThetaSignedReading F23 w * discriminant23CharacterFold w ^ 2 := by
  rw [mixedThetaSignedReading_eq_mellin_sub L23 w h0 h1,
    discriminant23_continued_completed_class_product,
    mixedThetaSignedReading_eq_mellin_sub F23 w h0 h1, discriminant23_continued_completed_base]

theorem discriminant23_dedekind_zero_iff_base_or_character (w : ℂ)
    (h0 : 0 < w.re) (h1 : w.re < 1) :
    mixedThetaContinuation L23 w = 0 ↔
      mixedThetaContinuation F23 w = 0 ∨ discriminant23CharacterFold w = 0 := by
  rw [← mixedThetaSignedReading_zero_iff L23 w h0 h1,
    discriminant23_signedReading_eq_base_mul_character_sq w h0 h1, mul_eq_zero,
    mixedThetaSignedReading_zero_iff F23 w h0 h1, pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)]

theorem discriminant23_dedekindRH_iff_base_and_character :
    DedekindZetaRH L23 ↔ DedekindZetaRH F23 ∧ StripZerosOnLine discriminant23CharacterFold := by
  rw [dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind L23),
    dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind F23)]
  constructor
  · intro h
    exact ⟨fun w h0 h1 hz ↦ h w h0 h1
      ((discriminant23_dedekind_zero_iff_base_or_character w h0 h1).mpr (.inl hz)),
      fun w h0 h1 hz ↦ h w h0 h1
        ((discriminant23_dedekind_zero_iff_base_or_character w h0 h1).mpr (.inr hz))⟩
  · rintro ⟨hF, hC⟩ w h0 h1 hz
    exact ((discriminant23_dedekind_zero_iff_base_or_character w h0 h1).mp hz).elim
      (hF w h0 h1) (hC w h0 h1)

theorem discriminant23_dedekindRH_iff_character (hF : DedekindZetaRH F23) :
    DedekindZetaRH L23 ↔ StripZerosOnLine discriminant23CharacterFold := by
  rw [discriminant23_dedekindRH_iff_base_and_character, and_iff_right hF]

/-- The signed margin for the genuine completed reading on the entire
first closed Dottie disk. -/
theorem re_discriminant23_completedReading_le_on_first_dottie_disk {w : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter (1 / 512) 0) (dottieScaledRadius 0)) :
    (mixedThetaCompletedReading L23 w).re ≤ -(1 / 50 : ℝ) := by
  have hstrip := dottieScaledRightDisk_strip hw
  have hPos : 0 < w.re := by linarith [hstrip.1]
  rw [discriminant23_completedReading_eq_classProduct w hPos hstrip.2]
  have h := re_discriminant23_classProduct_le_on_first_dottie_disk hw
  norm_num [Complex.mul_re]
  linarith only [h]

/-- The first closed Dottie disk excludes zeros of the actual continued
Dedekind zeta of the splitting field. -/
theorem discriminant23_dedekind_ne_zero_on_first_dottie_disk {w : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter (1 / 512) 0) (dottieScaledRadius 0)) :
    mixedThetaContinuation L23 w ≠ 0 := by
  have hstrip := dottieScaledRightDisk_strip hw
  have hPos : 0 < w.re := by linarith [hstrip.1]
  intro hz
  have hz' := (mixedThetaCompletedReading_zero_iff L23 w hPos hstrip.2).mpr hz
  have h := re_discriminant23_completedReading_le_on_first_dottie_disk hw
  rw [hz', Complex.zero_re] at h
  norm_num at h

/-- The polynomial weight `w * (1 - w)` keeps the genuine completed reading
strictly negative in real part across the full low-height strip. -/
theorem re_weighted_discriminant23_completedReading_le_on_low_strip {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) (him : |w.im| ≤ 1 / 2) :
    (w * (1 - w) * mixedThetaCompletedReading L23 w).re ≤ -(3 / 64 : ℝ) := by
  rw [discriminant23_completedReading_eq_classProduct w h0 h1]
  rw [show w * (1 - w) * (8 * discriminant23CompletedClassProduct w) =
    8 * (w * (1 - w) * discriminant23CompletedClassProduct w) by ring]
  have h := re_weighted_discriminant23_classProduct_le_on_low_strip h0 h1 him
  norm_num [Complex.mul_re] at h ⊢
  linarith only [h]

/-- There are no zeros of the actual Dedekind continuation in the open
critical strip at heights of absolute value at most `1/2`. -/
theorem discriminant23_dedekind_ne_zero_on_low_strip {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) (him : |w.im| ≤ 1 / 2) :
    mixedThetaContinuation L23 w ≠ 0 := by
  intro hz
  have h := re_weighted_discriminant23_completedReading_le_on_low_strip h0 h1 him
  rw [(mixedThetaCompletedReading_zero_iff L23 w h0 h1).mpr hz, mul_zero, Complex.zero_re] at h
  norm_num at h

theorem discriminant23_fold_bounds_to_seven_sixths {w : ℂ}
    (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1) (him : |w.im| ≤ 7 / 6) :
    ‖discriminant23TotalFold w‖ ≤ 216 / 143 ∧ 1 / 96 ≤ (discriminant23CharacterFold w).re := by
  obtain ⟨hA, hC⟩ := discriminant23_class_reading_bounds_on_strip h0 h1
  rw [total_fold_eq_dottie, character_fold_eq_dottie]
  constructor
  · rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    linarith only [hA]
  · have hi := pow_le_pow_left₀ (abs_nonneg _) him 2
    rw [sq_abs] at hi
    norm_num [Complex.mul_re]
    nlinarith only [hi, hC]

private theorem discriminant23_characterFold_ne_zero_on_wide_strip {w : ℂ}
    (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1) (him : |w.im| ≤ 7 / 6) :
    discriminant23CharacterFold w ≠ 0 := by
  have h := (discriminant23_fold_bounds_to_seven_sixths h0 h1 him).2
  intro hz
  rw [hz, Complex.zero_re] at h
  norm_num at h

theorem re_discriminant23_signed_base_le_on_wide_strip {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) (him : |w.im| ≤ 7 / 6) :
    (mixedThetaSignedReading F23 w).re ≤ -(3 / 13 : ℝ) := by
  have hgeom := norm_dottie_pole_weight_sq_le h0.le h1.le
  have h2 := pow_le_pow_left₀ (abs_nonneg _) him 2
  rw [sq_abs] at h2
  have h4 := pow_le_pow_left₀ (sq_nonneg w.im) h2 2
  have hq : ‖w * (1 - w)‖ ≤ 11 / 6 := by
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 11 / 6)).mp
    nlinarith only [hgeom, h2, h4]
  have ht := (discriminant23_fold_bounds_to_seven_sixths h0.le h1.le him).1
  have hreg : ‖w * (1 - w) * discriminant23TotalFold w‖ ≤ 36 / 13 := calc
    _ = ‖w * (1 - w)‖ * ‖discriminant23TotalFold w‖ := norm_mul ..
    _ ≤ (11 / 6) * (216 / 143) := mul_le_mul hq ht (norm_nonneg _) (by norm_num)
    _ = _ := by norm_num
  have hre := (Complex.re_le_norm _).trans hreg
  rw [mixedThetaSignedReading_eq_mellin_sub F23 w h0 h1,
    discriminant23_continued_completed_base, Complex.sub_re]
  norm_num [Complex.mul_re] at hre ⊢
  linarith only [hre]

/-- Normalize the completed reading by the proved nonzero character factor. -/
def discriminant23CharacterWeight (w : ℂ) : ℂ :=
  w * (1 - w) / discriminant23CharacterFold w ^ 2

theorem discriminant23CharacterWeight_analyticOnNhd :
    AnalyticOnNhd ℂ discriminant23CharacterWeight
      {w : ℂ | 0 < w.re ∧ w.re < 1 ∧ |w.im| ≤ 7 / 6} := by
  have hp : Differentiable ℂ (fun z : ℂ ↦ z * (1 - z)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  have hp' := Complex.analyticOnNhd_univ_iff_differentiable.mpr hp
  have hc' := Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (discriminant23CharacterFold_differentiable.pow 2)
  intro w hw
  exact (hp' w (mem_univ w)).div (hc' w (mem_univ w))
    (pow_ne_zero _ (discriminant23_characterFold_ne_zero_on_wide_strip hw.1.le hw.2.1.le hw.2.2))

theorem re_discriminant23_characterWeightedReading_le_on_wide_strip {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) (him : |w.im| ≤ 7 / 6) :
    (discriminant23CharacterWeight w * mixedThetaCompletedReading L23 w).re ≤ -(3 / 13 : ℝ) := by
  have h0w : w ≠ 0 := by rintro rfl; norm_num at h0
  have h1w : 1 - w ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h] at h1
    norm_num at h1
  have hC := discriminant23_characterFold_ne_zero_on_wide_strip h0.le h1.le him
  have heq : discriminant23CharacterWeight w * mixedThetaCompletedReading L23 w =
      mixedThetaSignedReading F23 w := by
    rw [discriminant23CharacterWeight, mixedThetaCompletedReading,
      discriminant23_signedReading_eq_base_mul_character_sq w h0 h1]
    field_simp [h0w, h1w, hC]
  rw [heq]
  exact re_discriminant23_signed_base_le_on_wide_strip h0 h1 him

theorem norm_discriminant23_signedReading_ge_on_wide_strip {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) (him : |w.im| ≤ 7 / 6) :
    (1 / 39936 : ℝ) ≤ ‖mixedThetaSignedReading L23 w‖ := by
  have hre := re_discriminant23_signed_base_le_on_wide_strip h0 h1 him
  have hbase : (3 / 13 : ℝ) ≤ ‖mixedThetaSignedReading F23 w‖ := calc
    _ ≤ (-mixedThetaSignedReading F23 w).re := by
      rw [Complex.neg_re]
      linarith only [hre]
    _ ≤ ‖-mixedThetaSignedReading F23 w‖ := Complex.re_le_norm _
    _ = _ := norm_neg _
  have hC := (discriminant23_fold_bounds_to_seven_sixths h0.le h1.le him).2.trans
    (Complex.re_le_norm _)
  rw [discriminant23_signedReading_eq_base_mul_character_sq w h0 h1, norm_mul, norm_pow]
  calc
    (1 / 39936 : ℝ) = (3 / 13) * (1 / 96) ^ 2 := by norm_num
    _ ≤ _ := mul_le_mul hbase (pow_le_pow_left₀ (by norm_num) hC 2)
      (by norm_num) (norm_nonneg _)

/-- The wider low-height band is zero-free for the actual Dedekind continuation. -/
theorem discriminant23_dedekind_ne_zero_to_seven_sixths {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) (him : |w.im| ≤ 7 / 6) :
    mixedThetaContinuation L23 w ≠ 0 := by
  intro hz
  have h := norm_discriminant23_signedReading_ge_on_wide_strip h0 h1 him
  rw [(mixedThetaSignedReading_zero_iff L23 w h0 h1).mpr hz, norm_zero] at h
  norm_num at h

#check @discriminant23_completedReading_eq_classProduct
#check @discriminant23_signedReading_eq_base_mul_character_sq
#check @discriminant23_dedekind_zero_iff_base_or_character
#check @discriminant23_dedekindRH_iff_character
#check @re_discriminant23_completedReading_le_on_first_dottie_disk
#check @discriminant23_dedekind_ne_zero_on_first_dottie_disk
#check @re_weighted_discriminant23_completedReading_le_on_low_strip
#check @discriminant23_dedekind_ne_zero_on_low_strip
#check @discriminant23CharacterWeight_analyticOnNhd
#check @re_discriminant23_characterWeightedReading_le_on_wide_strip
#check @norm_discriminant23_signedReading_ge_on_wide_strip
#check @discriminant23_dedekind_ne_zero_to_seven_sixths
#print axioms discriminant23_completedFold_eq_classProduct_off_poles
#print axioms discriminant23_completedReading_eq_classProduct
#print axioms discriminant23_signedReading_eq_base_mul_character_sq
#print axioms discriminant23_dedekind_zero_iff_base_or_character
#print axioms discriminant23_dedekindRH_iff_base_and_character
#print axioms discriminant23_dedekindRH_iff_character
#print axioms re_discriminant23_completedReading_le_on_first_dottie_disk
#print axioms discriminant23_dedekind_ne_zero_on_first_dottie_disk
#print axioms re_weighted_discriminant23_completedReading_le_on_low_strip
#print axioms discriminant23_dedekind_ne_zero_on_low_strip
#print axioms discriminant23_fold_bounds_to_seven_sixths
#print axioms re_discriminant23_signed_base_le_on_wide_strip
#print axioms discriminant23CharacterWeight_analyticOnNhd
#print axioms re_discriminant23_characterWeightedReading_le_on_wide_strip
#print axioms norm_discriminant23_signedReading_ge_on_wide_strip
#print axioms discriminant23_dedekind_ne_zero_to_seven_sixths

end
end FieldTarget
