import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! A common Taylor error bound for finite exponential sums and their derivatives. -/

namespace FieldTarget

noncomputable section

def centeredExponentialSum {ι : Type*} (s : Finset ι) (u : ι → ℝ) (A B : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ j ∈ s, (A j * Complex.exp ((u j : ℂ) * z) + B j * Complex.exp (-((u j : ℂ) * z)))

def centeredExponentialSumCoeff {ι : Type*} (s : Finset ι) (u : ι → ℝ) (A B : ι → ℂ)
    (k : ℕ) : ℂ :=
  ∑ j ∈ s, (A j + (-1 : ℂ) ^ k * B j) * (u j : ℂ) ^ k / (k.factorial : ℂ)

theorem centeredExponentialSum_error_le {ι : Type*} (s : Finset ι) (u : ι → ℝ) (A B : ι → ℂ)
    {L r M : ℝ} (hL : 0 ≤ L) (hU : ∀ j ∈ s, |u j| ≤ L)
    (hM : (∑ j ∈ s, (‖A j‖ + ‖B j‖)) ≤ M)
    (n : ℕ) (hcut : L * r / (n + 1 : ℕ) ≤ 1 / 2) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖centeredExponentialSum s u A B z -
        ∑ k ∈ Finset.range n, centeredExponentialSumCoeff s u A B k * z ^ k‖ ≤
      M * (2 * (L * r) ^ n / (n.factorial : ℝ)) := by
  let p (v : ℂ) := ∑ k ∈ Finset.range n, v ^ k / (k.factorial : ℂ)
  let E := 2 * (L * r) ^ n / (n.factorial : ℝ)
  have hE : 0 ≤ E := by
    have hr := (norm_nonneg z).trans hz
    dsimp [E]
    positivity
  have hTaylor (v : ℂ) (hv : ‖v‖ ≤ L * r) : ‖Complex.exp v - p v‖ ≤ E := by
    have h := Complex.exp_bound' ((div_le_div_of_nonneg_right hv (by positivity)).trans hcut)
    refine h.trans ?_
    dsimp only [E]
    rw [mul_comm (2 : ℝ), ← div_mul_eq_mul_div]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hv n) (by positivity))
      (by norm_num)
  have hpoly :
      (∑ j ∈ s, (A j * p ((u j : ℂ) * z) + B j * p (-((u j : ℂ) * z)))) =
        ∑ k ∈ Finset.range n, centeredExponentialSumCoeff s u A B k * z ^ k := by
    calc
      _ = ∑ j ∈ s, ∑ k ∈ Finset.range n,
          (A j + (-1 : ℂ) ^ k * B j) * (u j : ℂ) ^ k / (k.factorial : ℂ) * z ^ k := by
        apply Finset.sum_congr rfl
        intro j _
        unfold p
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        rw [show -((u j : ℂ) * z) = (-1 : ℂ) * ((u j : ℂ) * z) by ring, mul_pow, mul_pow]
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        simp only [centeredExponentialSumCoeff, Finset.sum_mul]
  rw [centeredExponentialSum, ← hpoly, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ s, ‖(A j * Complex.exp ((u j : ℂ) * z) + B j * Complex.exp (-((u j : ℂ) * z))) -
        (A j * p ((u j : ℂ) * z) + B j * p (-((u j : ℂ) * z)))‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s, (‖A j‖ + ‖B j‖) * E := by
      apply Finset.sum_le_sum
      intro j hj
      let v := (u j : ℂ) * z
      have hv : ‖v‖ ≤ L * r := by
        rw [show ‖v‖ = |u j| * ‖z‖ by simp [v, Complex.norm_real, Real.norm_eq_abs]]
        exact mul_le_mul (hU j hj) hz (norm_nonneg _) hL
      have hnv : ‖-v‖ ≤ L * r := by simpa only [norm_neg] using hv
      change
        ‖(A j * Complex.exp v + B j * Complex.exp (-v)) - (A j * p v + B j * p (-v))‖ ≤
          (‖A j‖ + ‖B j‖) * E
      rw [show (A j * Complex.exp v + B j * Complex.exp (-v)) - (A j * p v + B j * p (-v)) =
        A j * (Complex.exp v - p v) + B j * (Complex.exp (-v) - p (-v)) by ring, add_mul]
      exact (norm_add_le _ _).trans (by
        rw [norm_mul, norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hTaylor v hv) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left (hTaylor (-v) hnv) (norm_nonneg _)))
    _ = (∑ j ∈ s, (‖A j‖ + ‖B j‖)) * E := (Finset.sum_mul _ _ _).symm
    _ ≤ M * E := mul_le_mul_of_nonneg_right hM hE

#print axioms centeredExponentialSum_error_le

end

end FieldTarget
