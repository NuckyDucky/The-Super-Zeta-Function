import DedekindDiscriminant23CompletedProduct
import DedekindMixedThetaCompletedRings
import Discriminant23DottieDisk

namespace FieldTarget

open scoped NumberField
open NumberField MeasureTheory Set
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
    discriminant23TotalFold w = 2 * classMellinReading (fun t ↦ thetaSum (1 + t)) w := by
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
    discriminant23CharacterFold w = 2 * classMellinReading (fun t ↦ thetaDifference (1 + t)) w := by
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

/-- The actual completed Dedekind reading is the explicit class product
on the open critical strip, with the library's factor of eight. -/
theorem discriminant23_completedReading_eq_classProduct (w : ℂ)
    (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaCompletedReading L23 w = 8 * discriminant23CompletedClassProduct w := by
  have h₀ : w ≠ 0 := by rintro rfl; norm_num at hlo
  have h₁ : 1 - w ≠ 0 := by
    intro h
    have hw := sub_eq_zero.mp h
    rw [← hw] at hhi
    norm_num at hhi
  have hPole : w * (1 - w) ≠ 0 := mul_ne_zero h₀ h₁
  let A := classMellinReading (fun t ↦ thetaSum (1 + t)) w
  let C := classMellinReading (fun t ↦ thetaDifference (1 + t)) w
  have hModel : discriminant23CompletedClassProduct w = (A - (3 / 2 : ℂ) / (w * (1 - w))) * C ^ 2 :=
    rfl
  have h := discriminant23_continued_completed_class_product w
  rw [total_fold_eq_dottie, character_fold_eq_dottie] at h
  change _ = (w * (1 - w) * (2 * A) - 3) * (2 * C) ^ 2 at h
  rw [mixedThetaCompletedReading_eq_mellin L23 w hlo hhi, hModel]
  apply (mul_left_cancel₀ hPole)
  calc
    _ = w * (1 - w) * (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair L23).Λ₀ w -
          (DedekindZetaZeroFree.AbelianQuotient.Theta.mixedThetaPair L23).f₀ := by
      field_simp [h₀, h₁]
    _ = _ := h.trans (by field_simp [h₀, h₁]; ring)

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

#check @discriminant23_completedReading_eq_classProduct
#check @re_discriminant23_completedReading_le_on_first_dottie_disk
#check @discriminant23_dedekind_ne_zero_on_first_dottie_disk
#check @re_weighted_discriminant23_completedReading_le_on_low_strip
#check @discriminant23_dedekind_ne_zero_on_low_strip
#print axioms discriminant23_completedReading_eq_classProduct
#print axioms re_discriminant23_completedReading_le_on_first_dottie_disk
#print axioms discriminant23_dedekind_ne_zero_on_first_dottie_disk
#print axioms re_weighted_discriminant23_completedReading_le_on_low_strip
#print axioms discriminant23_dedekind_ne_zero_on_low_strip

end
end FieldTarget
