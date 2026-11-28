import GaussianFixedPointExponential

namespace FieldTarget

noncomputable section

/-- Repeated multiplication rounded to the same integer grid as the input. -/
def gaussianFixedPointProducts (step start : GaussianInt) (s : ℕ) : ℕ → GaussianInt
  | 0 => start
  | j + 1 => gaussianFloorDiv (step * gaussianFixedPointProducts step start s j) s

theorem norm_gaussianFixedPointProducts_error {z x : ℂ} {step start : GaussianInt}
    {s : ℕ} (hs : 0 < s) (hz : ‖z‖ ≤ 1) (hx : ‖x‖ ≤ 1)
    (hStepNorm : ‖gaussianScaled step s‖ ≤ 1) {ε δ : ℝ}
    (hStart : ‖x - gaussianScaled start s‖ ≤ ε)
    (hStep : ‖z - gaussianScaled step s‖ ≤ δ) (j : ℕ) :
    ‖z ^ j * x - gaussianScaled (gaussianFixedPointProducts step start s j) s‖ ≤
      ε + (j : ℝ) * (δ + 2 / (s : ℝ)) := by
  induction j with
  | zero => simpa only [pow_zero, one_mul, gaussianFixedPointProducts, Nat.cast_zero, zero_mul,
      add_zero] using hStart
  | succ j ih =>
    let a := gaussianFixedPointProducts step start s j
    have hPower : ‖z ^ j * x‖ ≤ 1 := by
      rw [norm_mul, norm_pow]
      calc
        _ ≤ ‖z‖ ^ j * 1 := mul_le_mul_of_nonneg_left hx (by positivity)
        _ ≤ _ := by rw [mul_one]; exact pow_le_one₀ (norm_nonneg _) hz
    have hRound : ‖gaussianScaled step s * gaussianScaled a s -
        gaussianScaled (gaussianFloorDiv (step * a) s) s‖ ≤ 2 / (s : ℝ) := by
      rw [show gaussianScaled step s * gaussianScaled a s = gaussianScaled (step * a) (s * s) by
        simp only [gaussianScaled, GaussianInt.toComplex_mul, Nat.cast_mul, div_mul_div_comm]]
      exact norm_gaussianFloorDiv_error (step * a) hs hs
    have hProduct : ‖z * (z ^ j * x) - gaussianScaled step s * gaussianScaled a s‖ ≤
        δ + (ε + (j : ℝ) * (δ + 2 / (s : ℝ))) := by
      rw [show z * (z ^ j * x) - gaussianScaled step s * gaussianScaled a s =
          (z - gaussianScaled step s) * (z ^ j * x) +
            gaussianScaled step s * (z ^ j * x - gaussianScaled a s) by ring]
      calc
        _ ≤ _ := norm_add_le _ _
        _ = ‖z - gaussianScaled step s‖ * ‖z ^ j * x‖ +
            ‖gaussianScaled step s‖ * ‖z ^ j * x - gaussianScaled a s‖ := by simp only [norm_mul]
        _ ≤ _ := add_le_add
          ((mul_le_of_le_one_right (norm_nonneg _) hPower).trans hStep)
          ((mul_le_of_le_one_left (norm_nonneg _) hStepNorm).trans ih)
    rw [pow_succ', mul_assoc, gaussianFixedPointProducts]
    calc
      _ ≤ ‖z * (z ^ j * x) - gaussianScaled step s * gaussianScaled a s‖ +
          ‖gaussianScaled step s * gaussianScaled a s -
            gaussianScaled (gaussianFloorDiv (step * a) s) s‖ := by
        simpa only [sub_add_sub_cancel] using
          norm_add_le (z * (z ^ j * x) - gaussianScaled step s * gaussianScaled a s)
            (gaussianScaled step s * gaussianScaled a s -
              gaussianScaled (gaussianFloorDiv (step * a) s) s)
      _ ≤ _ := by
        rw [Nat.cast_succ]
        linarith only [add_le_add hProduct hRound]

#print axioms norm_gaussianFixedPointProducts_error

end
end FieldTarget
