import Discriminant23GaussArithmetic
import Discriminant23GaussCoefficientError

namespace FieldTarget

open Finset

noncomputable section

set_option exponentiation.threshold 1024

def height29GaussCombination (total : Bool) : ℤ :=
  if total then 2 else -1

private def height29GaussCoefficientMultiplier : ℕ :=
  gaussCoefficientDenominator / height29FactorDenominator

private theorem height29_denominator_eq :
    gaussCoefficientDenominator = height29FactorDenominator * height29GaussCoefficientMultiplier := by
  decide +kernel

private theorem height29_coefficient_multiplier_pos : 0 < height29GaussCoefficientMultiplier := by
  decide +kernel

def height29GaussScaledSavedNumerator (total : Bool) (k : ℕ) : GaussianInt :=
  (height29GaussCoefficientMultiplier : GaussianInt) * height29SavedTaylorNumerator total k

private theorem height29GaussScaledSavedNumerator_eq (total : Bool) (k : ℕ) :
    gaussianScaled (height29GaussScaledSavedNumerator total k) gaussCoefficientDenominator =
      discriminant23Height29TaylorApprox total k := by
  have h : (height29GaussCoefficientMultiplier : ℂ) ≠ 0 := by
    exact_mod_cast height29_coefficient_multiplier_pos.ne'
  unfold gaussianScaled height29GaussScaledSavedNumerator
  rw [height29_denominator_eq, Nat.cast_mul, GaussianInt.toComplex_mul, map_natCast]
  change (height29GaussCoefficientMultiplier : ℂ) * (height29SavedTaylorNumerator total k : ℂ) /
    ((height29FactorDenominator : ℂ) * (height29GaussCoefficientMultiplier : ℂ)) = _
  unfold discriminant23Height29TaylorApprox gaussianScaled
  rw [mul_comm (height29GaussCoefficientMultiplier : ℂ), mul_div_mul_right _ _ h]
  rfl

def height29GaussTracedNumerator (trace : Fin 32 → Fin 24 → GaussPanelTrace)
    (total : Bool) (k : ℕ) : GaussianInt :=
  ∑ p : Fin 32, gaussTracedPanelCoefficientSum trace (height29GaussCombination total) p k

theorem height29GaussTracedNumerator_eq {trace : Fin 32 → Fin 24 → GaussPanelTrace}
    (h : ∀ (p : Fin 32) (i : Fin 24), (trace p i).approximation = gaussPanelApproximation p.val i)
    (total : Bool) (k : ℕ) :
    height29GaussTracedNumerator trace total k = gaussCoefficientNumerator (height29GaussCombination total) k := by
  unfold height29GaussTracedNumerator gaussCoefficientNumerator
  simp only [gaussTracedPanelCoefficientSum_eq h]
  exact Fin.sum_univ_eq_sum_range (fun p ↦ gaussPanelCoefficientSum (height29GaussCombination total) p k) 32

def Height29GaussIntegerCheck (trace : Fin 32 → Fin 24 → GaussPanelTrace)
    (total : Bool) (k : ℕ) : Prop :=
  gaussianL1 (height29GaussTracedNumerator trace total k - height29GaussScaledSavedNumerator total k) *
    10 ^ 28 ≤ gaussCoefficientDenominator

instance (trace : Fin 32 → Fin 24 → GaussPanelTrace) (total : Bool) (k : ℕ) :
    Decidable (Height29GaussIntegerCheck trace total k) := by
  unfold Height29GaussIntegerCheck
  infer_instance

theorem height29TaylorCoeff_enclosure_of_integer_check
    {trace : Fin 32 → Fin 24 → GaussPanelTrace}
    (hTrace : ∀ (p : Fin 32) (i : Fin 24), (trace p i).approximation = gaussPanelApproximation p.val i)
    {total : Bool} {k : ℕ} (hCheck : Height29GaussIntegerCheck trace total k) :
    ‖discriminant23ClassCombinationTaylorCoeff (height29GaussCombination total : ℝ)
        discriminant23Height29TaylorCenter k -
      discriminant23Height29TaylorApprox total k‖ ≤ 1 / 10 ^ 27 := by
  have h₀ : |(height29GaussCombination total : ℝ)| ≤ 2 := by
    cases total <;> norm_num [height29GaussCombination]
  have hExact := discriminant23_gaussCoefficient_approximation (k := k) h₀
  have hCompare : ‖gaussianScaled (height29GaussTracedNumerator trace total k)
        gaussCoefficientDenominator - discriminant23Height29TaylorApprox total k‖ ≤ 1 / 10 ^ 28 := by
    rw [← height29GaussScaledSavedNumerator_eq]
    have h := norm_gaussianScaled_le_of_l1 (d := gaussCoefficientDenominator) (p := 1) (q := 10 ^ 28)
      (by norm_num [gaussCoefficientDenominator, gaussWeightDenominator, gaussExpScale, gaussMomentScale])
      (by norm_num) (by simpa only [Height29GaussIntegerCheck, mul_one] using hCheck)
    simpa only [gaussianScaled, GaussianInt.toComplex_sub, sub_div, Nat.cast_one, Nat.cast_pow,
      Nat.cast_ofNat] using h
  rw [height29GaussTracedNumerator_eq hTrace] at hCompare
  refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hExact hCompare).trans ?_)
  norm_num

#print axioms height29TaylorCoeff_enclosure_of_integer_check

end
end FieldTarget
