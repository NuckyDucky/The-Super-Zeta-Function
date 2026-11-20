import SuperZeta.FieldWeights
import SuperZeta.SignWords

/-! The prime-power detector at 2 encodes the signed products of chronological
prefixes. The exponent convention belongs to this encoding. -/
noncomputable section
namespace SuperZeta.DyadicWeights

open SignWords

def stepExponent : Sign → ℕ
  | .plus => 2
  | .minus => 1

def letter : Sign → ℝ
  | .plus => 1
  | .minus => -1

noncomputable def exponent (w : List Sign) : ℕ := (w.map stepExponent).sum

noncomputable def signProduct (w : List Sign) : ℝ := (w.map letter).prod

theorem legendre_three_two : legendreSym 3 2 = -1 := by
  apply (legendreSym.eq_neg_one_iff 3).mpr
  rintro ⟨x, hx⟩
  fin_cases x <;> revert hx <;> decide

/-- At 2 the real character mod 3 takes value −1. Each positive stage
increments the exponent by two, each negative one by one. -/
theorem dyadic_parity (w : List Sign) : (-1 : ℝ) ^ exponent w = signProduct w := by
  induction w with
  | nil => simp [exponent, signProduct]
  | cons s w ih =>
    unfold exponent signProduct at *
    simp only [List.map_cons, List.sum_cons, List.prod_cons, pow_add]
    rw [ih]
    cases s <;> norm_num [stepExponent, letter]

/-- Reading the corresponding actual normalized prime-power coefficient and
subtracting its trivial-character part recovers this entire prefix's sign. -/
theorem recover_prefix (w : List Sign) :
    7 * (FieldWeights.primePowerWeight (1/7) (-1) (exponent w) - 1) =
      signProduct w := by
  unfold FieldWeights.primePowerWeight
  rw [dyadic_parity]
  ring

theorem recover_character_prefix (w : List Sign) :
    7 * (FieldWeights.primePowerWeight (1/7) (legendreSym 3 2 : ℝ) (exponent w) - 1) =
      signProduct w := by
  simpa only [legendre_three_two, Int.cast_neg, Int.cast_one] using recover_prefix w

/-- Evaluating any finite prefix polynomial commutes with this change of
coordinates, including evaluation at the complex cap lift. -/
theorem weighted_prefix_sum (w : List Sign) (t : ℂ) :
    (∑ j ∈ Finset.range w.length,
      (signProduct (w.take (j+1)) : ℂ) * t^j) =
    ∑ j ∈ Finset.range w.length,
      ((7 * (FieldWeights.primePowerWeight (1/7) (-1)
        (exponent (w.take (j+1))) - 1) : ℝ) : ℂ) * t^j := by
  apply Finset.sum_congr rfl
  intro j _
  rw [recover_prefix]

end SuperZeta.DyadicWeights
