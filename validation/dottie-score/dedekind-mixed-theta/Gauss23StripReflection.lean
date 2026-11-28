import DedekindDiscriminant23CharacterReflectedCounts
import Mathlib.Analysis.Calculus.Deriv.Star

/-! Reflect value and slope certificates at the same height across the critical line. -/

namespace FieldTarget

open Complex MeasureTheory Set NumberField
open DedekindZetaZeroFree.AbelianQuotient DedekindZetaZeroFree.AbelianQuotient.Theta
open DedekindZetaZeroFree.Hecke
open scoped NumberField ComplexConjugate

local notation "C23" => ClassGroup (𝓞 (discriminant23QuadraticSubfield : Type))

private theorem fold_weight_conj (w : ℂ) {t : ℝ} (ht : 0 < t) :
    discriminant23FoldWeight (conj w) t = conj (discriminant23FoldWeight w t) := by
  have hPow (z : ℂ) : (t : ℂ) ^ z = Complex.exp (z * (Real.log t : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
      ← Complex.ofReal_log ht.le, mul_comm]
  have h (z : ℂ) : conj ((t : ℂ) ^ z) = (t : ℂ) ^ conj z := by
    rw [hPow z, hPow (conj z), ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
  simp only [discriminant23FoldWeight, map_add, h, map_sub, map_one, map_neg]

private theorem class_fold_conj (C : C23) (w : ℂ) :
    (idealClassThetaPair (discriminant23QuadraticSubfield : Type) C).Λ₀ (conj w) =
      conj ((idealClassThetaPair (discriminant23QuadraticSubfield : Type) C).Λ₀ w) := by
  rw [discriminant23_classLambdaZero_eq_fold, discriminant23_classLambdaZero_eq_fold, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [map_mul, fold_weight_conj w (zero_lt_one.trans ht)]
  congr 1
  unfold discriminant23ClassKernel
  split <;> simp

theorem discriminant23_characterFold_conj (w : ℂ) :
    discriminant23CharacterFold (conj w) = conj (discriminant23CharacterFold w) := by
  unfold discriminant23CharacterFold
  rw [map_sub, class_fold_conj, class_fold_conj]

theorem discriminant23_characterFold_same_height_reflection (w : ℂ) :
    discriminant23CharacterFold (1 - conj w) = conj (discriminant23CharacterFold w) := by
  rw [discriminant23_characterFold_one_sub, discriminant23_characterFold_conj]

theorem discriminant23_characterFold_deriv_im_same_height_reflection (w : ℂ) :
    (deriv discriminant23CharacterFold (1 - conj w)).im =
      (deriv discriminant23CharacterFold w).im := by
  let f := discriminant23CharacterFold
  have hDiff : Differentiable ℂ f := discriminant23CharacterCountingFunction.differentiable
  have hConjFun : conj ∘ f ∘ conj = f := by
    funext z
    simp only [Function.comp_apply, f, discriminant23_characterFold_conj, Complex.conj_conj]
  have hConj := congrFun (deriv_conj_conj (f := f)) w
  rw [hConjFun] at hConj
  have hConj' : deriv f (conj w) = conj (deriv f w) := by
    simpa only [Function.comp_apply, Complex.conj_conj] using (congrArg conj hConj).symm
  let z := conj w
  have hLinear : HasDerivAt (fun y : ℂ ↦ 1 - y) (-1) z := by
    have he : ((fun _ : ℂ ↦ (1 : ℂ)) - id) = (fun y : ℂ ↦ 1 - y) := rfl
    have hd := (hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)
    rw [he, zero_sub] at hd
    exact hd
  have h := ((hDiff (1 - z)).hasDerivAt.comp z hLinear).deriv
  have hSym : f ∘ (fun y : ℂ ↦ 1 - y) = f := funext discriminant23_characterFold_one_sub
  rw [hSym, mul_neg, mul_one] at h
  have hRef : deriv f (1 - conj w) = -conj (deriv f w) := by
    have hn := congrArg Neg.neg h.symm
    simpa only [neg_neg, z, hConj'] using hn
  change (deriv f (1 - conj w)).im = (deriv f w).im
  rw [hRef, Complex.neg_im, Complex.conj_im, neg_neg]

#print axioms discriminant23_characterFold_same_height_reflection
#print axioms discriminant23_characterFold_deriv_im_same_height_reflection

end FieldTarget
