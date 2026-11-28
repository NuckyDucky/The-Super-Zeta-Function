import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

namespace FieldTarget

noncomputable section

def dyadicExpArgument (z : ℂ) (k j : ℕ) : ℂ :=
  2 ^ j * (z / 2 ^ k)

theorem norm_exp_sub_taylor_approximation_le {z a : ℂ} {n : ℕ} {ε : ℝ}
    (hCut : ‖z‖ / (n.succ : ℝ) ≤ 1 / 2)
    (hRound : ‖(∑ m ∈ Finset.range n, z ^ m / (m.factorial : ℂ)) - a‖ ≤ ε) :
    ‖Complex.exp z - a‖ ≤ ‖z‖ ^ n / (n.factorial : ℝ) * 2 + ε :=
  (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (Complex.exp_bound' hCut) hRound)

private theorem exp_dyadic_succ (z : ℂ) (k j : ℕ) :
    Complex.exp (dyadicExpArgument z k (j + 1)) = Complex.exp (dyadicExpArgument z k j) ^ 2 := by
  rw [show dyadicExpArgument z k (j + 1) = dyadicExpArgument z k j + dyadicExpArgument z k j by
    unfold dyadicExpArgument
    rw [pow_succ]
    ring, Complex.exp_add, pow_two]

private theorem norm_sq_sub_sq (a b : ℂ) :
    ‖a ^ 2 - b ^ 2‖ ≤ (‖a‖ + ‖b‖) * ‖a - b‖ := by
  rw [show a ^ 2 - b ^ 2 = (a + b) * (a - b) by ring, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (norm_nonneg _)

set_option maxHeartbeats 1000000 in
/-- A Taylor enclosure at the scaled input can be replayed with rounded
squares. At each step the exact modulus depends only on the real part. -/
theorem norm_exp_sub_dyadic_approximation_le (z : ℂ) (k : ℕ) (v : ℕ → ℂ) (E : ℕ → ℝ)
    (hStart : ‖Complex.exp (z / 2 ^ k) - v 0‖ ≤ E 0)
    (hStep : ∀ j < k,
      ‖Complex.exp (dyadicExpArgument z k j) - v j‖ ≤ E j →
      (Real.exp (dyadicExpArgument z k j).re + ‖v j‖) * E j +
        ‖v j ^ 2 - v (j + 1)‖ ≤ E (j + 1)) :
    ‖Complex.exp z - v k‖ ≤ E k := by
  have h (j : ℕ) (hj : j ≤ k) :
      ‖Complex.exp (dyadicExpArgument z k j) - v j‖ ≤ E j := by
    induction j with
    | zero => simpa only [dyadicExpArgument, pow_zero, one_mul] using hStart
    | succ j ih =>
        have hj' : j < k := Nat.lt_of_succ_le hj
        have hp := ih hj'.le
        have hBudget : (‖Complex.exp (dyadicExpArgument z k j)‖ + ‖v j‖) * E j +
            ‖v j ^ 2 - v (j + 1)‖ ≤ E (j + 1) := by
          simpa only [Complex.norm_exp] using hStep j hj' hp
        rw [exp_dyadic_succ]
        calc
          _ ≤ ‖Complex.exp (dyadicExpArgument z k j) ^ 2 - v j ^ 2‖ +
              ‖v j ^ 2 - v (j + 1)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ (‖Complex.exp (dyadicExpArgument z k j)‖ + ‖v j‖) * E j +
              ‖v j ^ 2 - v (j + 1)‖ :=
            add_le_add ((norm_sq_sub_sq _ _).trans
              (mul_le_mul_of_nonneg_left hp (by positivity))) le_rfl
          _ ≤ _ := hBudget
  have hFinal : dyadicExpArgument z k k = z := by
    unfold dyadicExpArgument
    field_simp
  simpa only [hFinal] using h k le_rfl

#print axioms norm_exp_sub_taylor_approximation_le
#print axioms norm_exp_sub_dyadic_approximation_le

end
end FieldTarget
