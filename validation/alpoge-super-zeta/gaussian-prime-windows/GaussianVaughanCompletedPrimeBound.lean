import GaussianVaughanPrimeInversion
import GaussianVaughanCofactorBound
import GaussianVaughanPrimeComplement

/-! Feed the shifted Mellin bound into the actual finite cofactor sum. -/

namespace AlpogeSuperZeta

open Finset

noncomputable section

/-- The completed-prime term spends a fixed multiple of the error scale.
The logarithmic power counts the cofactors. -/
theorem archivedGaussianVaughanCompletedPrimeSum_log_bound
    (hDir : DirichletLZerosOnLine) :
    ∃ C ≥ 0, ∀ X > (1 : ℝ),
      |archivedGaussianVaughanCompletedPrimeSum X| ≤
        C * (X ^ (3 / 8 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ)) := by
  obtain ⟨D, hD, hKernel⟩ := archivedGaussianVaughanCompletedPrimeKernel_left_powerBound hDir
  refine ⟨8 * D, by positivity, fun X hX => ?_⟩
  let a : ℝ := 3 / 8
  let L : ℝ := (Real.log X) ^ (8 / 3 : ℝ)
  let s := Icc 1 (Nat.floor L)
  let f (m : ℕ) : ℝ := (archivedGaussianMoebiusCoefficients m).re *
    (archivedGaussianVaughanCompletedPrimeKernel (m / X)).re
  have hX₀ := zero_lt_one.trans hX
  have hL : 0 ≤ L := by dsimp [L]; positivity [Real.log_pos hX]
  have hTerm (m : ℕ) (hm : m ∈ s) : |f m| ≤ 8 * D * X ^ a := by
    have hm₀ : 0 < m := (mem_Icc.mp hm).1
    have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm₀
    have hScale : ((m : ℝ) / X) ^ (-a) = X ^ a / (m : ℝ) ^ a := by
      rw [Real.div_rpow hmR.le hX₀.le, Real.rpow_neg hmR.le, Real.rpow_neg hX₀.le, inv_div_inv]
    dsimp only [f]
    rw [abs_mul]
    calc
      _ ≤ ‖archivedGaussianMoebiusCoefficients m‖ *
          ‖archivedGaussianVaughanCompletedPrimeKernel (m / X)‖ :=
        mul_le_mul (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
          (abs_nonneg _) (norm_nonneg _)
      _ ≤ (8 * (m : ℝ) ^ a) * (D * ((m : ℝ) / X) ^ (-a)) :=
        mul_le_mul (archivedGaussianMoebius_three_eighths_bound hm₀.ne')
          (hKernel _ (div_pos hmR hX₀)) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [hScale]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hmR a)]
  have hCount : (s.card : ℝ) ≤ L := by
    simpa [s, Nat.card_Icc] using (Nat.floor_le hL)
  change |∑ m ∈ s, f m| ≤ (8 * D) * (X ^ a * L)
  calc
    _ ≤ ∑ m ∈ s, |f m| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ s, 8 * D * X ^ a := sum_le_sum hTerm
    _ = (s.card : ℝ) * (8 * D * X ^ a) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ L * (8 * D * X ^ a) := mul_le_mul_of_nonneg_right hCount (by positivity)
    _ = _ := by ring

/-- The complementary error consists of the upper and below-window errors,
plus the now bounded completed-prime term. -/
theorem archivedGaussianVaughan_complement_error_with_prime_bound
    (hDir : DirichletLZerosOnLine) :
    ∃ C ≥ 0, ∀ (W : ℝ → ℝ), (∀ u ≥ 2, W u = 0) →
      ∀ X > (1 : ℝ),
        |archivedGaussianVaughanSum X - archivedGaussianVaughanLowerSum W X| ≤
          |archivedGaussianVaughanSum X - archivedGaussianVaughanUpperPrimeSum W X| +
          C * (X ^ (3 / 8 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ)) +
          |archivedGaussianVaughanBelowWindowSum W X| := by
  obtain ⟨C, hC, hPrime⟩ := archivedGaussianVaughanCompletedPrimeSum_log_bound hDir
  exact ⟨C, hC, fun _ hW X hX =>
    archivedGaussianVaughan_complement_error hW hX le_rfl (hPrime X hX) le_rfl⟩

#check archivedGaussianVaughanCompletedPrimeSum_log_bound
#check archivedGaussianVaughan_complement_error_with_prime_bound
#print axioms archivedGaussianVaughanCompletedPrimeSum_log_bound
#print axioms archivedGaussianVaughan_complement_error_with_prime_bound

end
end AlpogeSuperZeta
