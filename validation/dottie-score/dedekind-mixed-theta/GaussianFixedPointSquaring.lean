import GaussianFixedPointExponential

namespace FieldTarget

open Complex

noncomputable section

/-- Repeated squaring on a fixed integer grid. -/
def gaussianFixedPointSquares (a : GaussianInt) (s : ℕ) : ℕ → GaussianInt
  | 0 => a
  | j + 1 =>
    let v := gaussianFixedPointSquares a s j
    gaussianFloorDiv (v * v) s

theorem norm_gaussianFixedPointSquares_step (a : GaussianInt) {s : ℕ} (hs : 0 < s) (j : ℕ) :
    ‖(gaussianScaled (gaussianFixedPointSquares a s j) s) ^ 2 -
      gaussianScaled (gaussianFixedPointSquares a s (j + 1)) s‖ ≤ 2 / (s : ℝ) := by
  let v := gaussianFixedPointSquares a s j
  rw [show (gaussianScaled v s) ^ 2 = gaussianScaled (v * v) (s * s) by
    simp only [pow_two, gaussianScaled, GaussianInt.toComplex_mul, Nat.cast_mul, div_mul_div_comm]]
  exact norm_gaussianFloorDiv_error (v * v) hs hs

/-- The exact exponential stays in the unit disk, so the error in each
rounded square grows by at most three times the previous error plus 2/s. -/
theorem norm_exp_sub_fixedPointSquares_le {z : ℂ} (hz : z.re ≤ 0) (a : GaussianInt)
    {s : ℕ} (hs : 0 < s) (K : ℕ) {ε : ℝ}
    (hStart : ‖Complex.exp (z / 2 ^ K) - gaussianScaled a s‖ ≤ ε)
    (hBudget : (3 : ℝ) ^ K * (ε + 1 / (s : ℝ)) ≤ 1) :
    ‖Complex.exp z - gaussianScaled (gaussianFixedPointSquares a s K) s‖ ≤
      (3 : ℝ) ^ K * (ε + 1 / (s : ℝ)) - 1 / (s : ℝ) := by
  let E (j : ℕ) : ℝ := (3 : ℝ) ^ j * (ε + 1 / (s : ℝ)) - 1 / (s : ℝ)
  let v (j : ℕ) : ℂ := gaussianScaled (gaussianFixedPointSquares a s j) s
  have hE₀ : 0 ≤ ε := (norm_nonneg _).trans hStart
  have hE (j : ℕ) (hj : j ≤ K) : E j ≤ 1 := by
    have hPow : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ K := pow_le_pow_right₀ (by norm_num) hj
    have hM := mul_le_mul_of_nonneg_right hPow
      (show 0 ≤ ε + 1 / (s : ℝ) by positivity)
    dsimp only [E]
    linarith only [hM, hBudget, show 0 ≤ (1 : ℝ) / s by positivity]
  have hNorm (j : ℕ) : Real.exp (dyadicExpArgument z K j).re ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hArg : dyadicExpArgument z K j =
        ((((2 : ℝ) ^ j / (2 : ℝ) ^ K) : ℝ) : ℂ) * z := by
      unfold dyadicExpArgument
      push_cast
      ring
    rw [hArg, Complex.re_ofReal_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hz
  refine norm_exp_sub_dyadic_approximation_le z K v E ?_ ?_
  · simpa only [v, E, gaussianFixedPointSquares, pow_zero, one_mul, add_sub_cancel_right] using hStart
  · intro j hj hp
    have hv : ‖v j‖ ≤ 2 := by
      have h := norm_le_norm_sub_add (v j) (Complex.exp (dyadicExpArgument z K j))
      rw [norm_sub_rev, Complex.norm_exp] at h
      linarith only [h, hp, hNorm j, hE j hj.le]
    have hE' : 0 ≤ E j := (norm_nonneg _).trans hp
    have hR : ‖v j ^ 2 - v (j + 1)‖ ≤ 2 / (s : ℝ) := norm_gaussianFixedPointSquares_step a hs j
    calc
      _ ≤ 3 * E j + 2 / (s : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right (by linarith only [hNorm j, hv]) hE') hR
      _ = _ := by dsimp only [E]; rw [pow_succ]; ring

/-- The evaluation uses a Taylor sum at one scaled input and integer squares. -/
def gaussianFixedPointExp (a : GaussianInt) (d s K n : ℕ) : GaussianInt :=
  gaussianFixedPointSquares (gaussianTaylorSum a (d * 2 ^ K) s n) s K

theorem norm_exp_sub_gaussianFixedPointExp (a : GaussianInt) {d s : ℕ}
    (hd : 0 < d) (hs : 0 < s) (K n : ℕ)
    (hRe : (gaussianScaled a d).re ≤ 0) (hSmall : ‖gaussianScaled a (d * 2 ^ K)‖ ≤ 1 / 2)
    (hBudget : (3 : ℝ) ^ K *
      ((1 / 2 : ℝ) ^ n / n.factorial * 2 + (n : ℝ) * (4 / (s : ℝ)) + 1 / (s : ℝ)) ≤ 1) :
    ‖Complex.exp (gaussianScaled a d) - gaussianScaled (gaussianFixedPointExp a d s K n) s‖ ≤
      (3 : ℝ) ^ K * ((1 / 2 : ℝ) ^ n / n.factorial * 2 + (n : ℝ) * (4 / (s : ℝ)) + 1 / (s : ℝ)) -
        1 / (s : ℝ) := by
  have hInput : gaussianScaled a d / (2 : ℂ) ^ K = gaussianScaled a (d * 2 ^ K) := by
    simp only [gaussianScaled, div_div, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hInitial := norm_exp_sub_gaussianTaylorSum a (Nat.mul_pos hd (by positivity)) hs hSmall n
  exact norm_exp_sub_fixedPointSquares_le hRe _ hs K (by rwa [hInput]) hBudget

#print axioms norm_gaussianFixedPointSquares_step
#print axioms norm_exp_sub_fixedPointSquares_le
#print axioms norm_exp_sub_gaussianFixedPointExp

end
end FieldTarget
