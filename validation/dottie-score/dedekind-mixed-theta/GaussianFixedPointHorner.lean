import GaussianFixedPointExponential

namespace FieldTarget

open Complex Finset

noncomputable section

/-- Evaluate consecutive integer coefficients from highest degree to lowest
with every intermediate result rounded onto the common dyadic grid. -/
def gaussianFixedPointHorner (coeff : ℕ → ℤ) (q : GaussianInt) (s : ℕ) :
    ℕ → ℕ → GaussianInt
  | _, 0 => 0
  | k, n + 1 => ⟨coeff k * (s : ℤ), 0⟩ +
      gaussianFloorDiv (q * gaussianFixedPointHorner coeff q s (k + 1) n) s

private theorem shifted_polynomial_step (a : ℕ → ℤ) (z : ℂ) (k n : ℕ) :
    (∑ j ∈ range (n + 1), (a (k + j) : ℂ) * z ^ j) =
      (a k : ℂ) + z * ∑ j ∈ range n, (a (k + 1 + j) : ℂ) * z ^ j := by
  rw [sum_range_succ', mul_sum, Nat.add_zero, pow_zero, mul_one, add_comm (a k : ℂ)]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [show k + (j + 1) = k + 1 + j by omega, pow_succ']
  ring

theorem norm_polynomial_sub_gaussianFixedPointHorner_le (a : ℕ → ℤ)
    (q : GaussianInt) {s : ℕ} (hs : 0 < s) (hq : ‖gaussianScaled q s‖ ≤ 1)
    (k n : ℕ) :
    ‖(∑ j ∈ range n, (a (k + j) : ℂ) * (gaussianScaled q s) ^ j) -
      gaussianScaled (gaussianFixedPointHorner a q s k n) s‖ ≤ (n : ℝ) * (2 / (s : ℝ)) := by
  induction n generalizing k with
  | zero => simp [gaussianFixedPointHorner, gaussianScaled]
  | succ n ih =>
    let z := gaussianScaled q s
    let u := gaussianFixedPointHorner a q s (k + 1) n
    let v := gaussianFloorDiv (q * u) s
    let P := ∑ j ∈ range n, (a (k + 1 + j) : ℂ) * z ^ j
    have hCoeff : gaussianScaled (gaussianFixedPointHorner a q s k (n + 1)) s =
        (a k : ℂ) + gaussianScaled v s := by
      have hS : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
      simp only [gaussianFixedPointHorner, v, u, gaussianScaled, GaussianInt.toComplex_add,
        GaussianInt.toComplex_def', Int.cast_mul, Int.cast_natCast, Int.cast_zero,
        zero_mul, add_zero, add_div, mul_div_cancel_right₀ _ hS]
    have hRound : ‖z * gaussianScaled u s - gaussianScaled v s‖ ≤ 2 / (s : ℝ) := by
      rw [show z * gaussianScaled u s = gaussianScaled (q * u) (s * s) by
        simp only [z, gaussianScaled, GaussianInt.toComplex_mul, Nat.cast_mul, div_mul_div_comm]]
      exact norm_gaussianFloorDiv_error (q * u) hs hs
    have hProd : ‖z * (P - gaussianScaled u s)‖ ≤ (n : ℝ) * (2 / (s : ℝ)) := by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hq).trans (ih (k + 1))
    rw [shifted_polynomial_step, hCoeff, add_sub_add_left_eq_sub]
    change ‖z * P - gaussianScaled v s‖ ≤ _
    rw [show z * P - gaussianScaled v s = z * (P - gaussianScaled u s) +
        (z * gaussianScaled u s - gaussianScaled v s) by ring]
    exact (norm_add_le _ _).trans ((add_le_add hProd hRound).trans_eq (by rw [Nat.cast_succ]; ring))

#print axioms norm_polynomial_sub_gaussianFixedPointHorner_le

end
end FieldTarget
