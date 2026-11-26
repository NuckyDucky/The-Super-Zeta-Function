import GaussianFrobeniusTriangle
import GaussianPrimeSquaredWindow

/-! In the original quartic's signed sum, the aggregate triangle error
fits every cofinal window exponent used by the pole criterion. -/

namespace AlpogeSuperZeta

open ArtinPrimitiveRootsConjecture FieldTarget Finset
open scoped Classical

noncomputable section

def archivedGaussianTriangleWindow (x : ℝ) : ℝ :=
  (∑ p ∈ range (⌊x⌋₊ + 1), archivedGaussianSignedPrimeWeight p *
    ((2 * Real.log x / x ^ 2) * (frobeniusTriangleDivisibility x (Real.log x) p : ℝ))) -
    x / 3 * archivedGaussianPrimeCenter

theorem archivedGaussianTriangleWindow_error :
    ∃ C ≥ (0 : ℝ), ∀ x ≥ (2 : ℝ),
      |archivedGaussianTriangleWindow x - archivedGaussianPrimeSquaredWindow x| ≤ C * x ^ (1 / 2 : ℝ) := by
  let W (p : ℕ) := |archivedGaussianSignedPrimeWeight p| / ((max 1 p : ℕ) : ℝ) ^ (5 / 4 : ℝ)
  have hW : Summable W := archivedGaussianSignedPrimeWeight_summable (by norm_num)
  have hW₀ (p : ℕ) : 0 ≤ W p := div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  let M : ℝ := ∑' p, W p
  have hM : 0 ≤ M := tsum_nonneg hW₀
  refine ⟨18 * M, mul_nonneg (by norm_num) hM, fun x hx => ?_⟩
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := one_pos.trans_le hx₁
  let k := Real.log x
  have hk : 0 < k := Real.log_pos (by linarith)
  let B : ℝ := (2 * k / x ^ 2) * (x + x / k + 1)
  have hB : B * x ≤ 18 * x ^ (1 / 4 : ℝ) := by
    have hcalc : B * x = 2 * k + 2 + (2 * k) / x := by
      dsimp [B]
      field_simp
    have hdiv : 2 * k / x ≤ 2 * k := (div_le_iff₀ hx₀).mpr (by
      nlinarith [mul_nonneg hk.le (sub_nonneg.mpr hx₁)])
    have hlog : k ≤ 4 * x ^ (1 / 4 : ℝ) := by
      have h := Real.log_le_rpow_div (ε := (1 / 4 : ℝ)) hx₀.le (by norm_num)
      dsimp [k]
      linarith
    have hpow : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx₁ (by norm_num)
    rw [hcalc]
    linarith
  let V (p : ℕ) := (2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k p : ℝ)
  let S (p : ℕ) := ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * p)
  have hTerm (p : ℕ) (hpRange : p ∈ range (⌊x⌋₊ + 1)) :
      |archivedGaussianSignedPrimeWeight p * (V p - S p)| ≤
        (18 * x ^ (1 / 2 : ℝ)) * W p := by
    by_cases hp : p.Prime
    · have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
      have hpBound : (p : ℝ) ≤ x := (Nat.le_floor_iff hx₀.le).mp
        (Nat.le_of_lt_succ (mem_range.mp hpRange))
      have hcount : (↑(⌈x / (p : ℝ)⌉₊ - 1) : ℝ) ≤ x / (p : ℝ) := by
        have hc : 1 ≤ ⌈x / (p : ℝ)⌉₊ :=
          Nat.lt_ceil.mpr (by simpa using div_pos hx₀ hp')
        rw [Nat.cast_sub hc, Nat.cast_one]
        linarith [Nat.ceil_lt_add_one (div_pos hx₀ hp').le]
      have hMargin := frobeniusTriangleDivisibility_error hx₁ hk hp.pos
      change 0 ≤ V p - S p ∧ (V p - S p) ≤ B * (↑(⌈x / (p : ℝ)⌉₊ - 1) : ℝ) at hMargin
      have hB₀ : 0 ≤ B := by dsimp [B]; positivity
      have hScaled : |archivedGaussianSignedPrimeWeight p| / (p : ℝ) ≤ x ^ (1 / 4 : ℝ) * W p := by
        have hPow : (p : ℝ) ^ (5 / 4 : ℝ) = (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) := by
          rw [show (5 / 4 : ℝ) = (1 / 4 : ℝ) + 1 by norm_num, Real.rpow_add hp', Real.rpow_one]
        have he : |archivedGaussianSignedPrimeWeight p| / (p : ℝ) =
            (p : ℝ) ^ (1 / 4 : ℝ) * W p := by
          dsimp [W]
          rw [max_eq_right hp.one_lt.le, hPow]
          field_simp
        rw [he]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp'.le hpBound (by norm_num)) (hW₀ p)
      rw [abs_mul, abs_of_nonneg hMargin.1]
      calc
        _ ≤ |archivedGaussianSignedPrimeWeight p| * (B * (x / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (hMargin.2.trans (mul_le_mul_of_nonneg_left hcount hB₀)) (abs_nonneg _)
        _ = (B * x) * (|archivedGaussianSignedPrimeWeight p| / (p : ℝ)) := by ring
        _ ≤ (18 * x ^ (1 / 4 : ℝ)) * (x ^ (1 / 4 : ℝ) * W p) :=
          mul_le_mul hB hScaled (div_nonneg (abs_nonneg _) hp'.le) (by positivity)
        _ = 18 * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) * W p := by ring
        _ = _ := by
          rw [← Real.rpow_add hx₀ (1 / 4 : ℝ) (1 / 4 : ℝ)]
          norm_num
    · simp only [archivedGaussianSignedPrimeWeight, if_neg hp, mul_zero, neg_zero, zero_mul, abs_zero]
      exact mul_nonneg (by positivity) (hW₀ p)
  rw [archivedGaussianPrimeSquaredWindow_eq_sum hx₁, archivedGaussianTriangleWindow]
  have he (a b c : ℝ) : (a - c) - (b - c) = a - b := by ring
  rw [he]
  change |(∑ p ∈ range (⌊x⌋₊ + 1), archivedGaussianSignedPrimeWeight p * V p) -
      (∑ p ∈ range (⌊x⌋₊ + 1), archivedGaussianSignedPrimeWeight p * S p)| ≤
      (18 * M) * x ^ (1 / 2 : ℝ)
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ p ∈ range (⌊x⌋₊ + 1), |archivedGaussianSignedPrimeWeight p * (V p - S p)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ range (⌊x⌋₊ + 1), (18 * x ^ (1 / 2 : ℝ)) * W p := sum_le_sum hTerm
    _ = (18 * x ^ (1 / 2 : ℝ)) * ∑ p ∈ range (⌊x⌋₊ + 1), W p := (mul_sum _ _ _).symm
    _ ≤ (18 * x ^ (1 / 2 : ℝ)) * M :=
      mul_le_mul_of_nonneg_left (hW.sum_le_tsum _ (fun p _ => hW₀ p)) (by positivity)
    _ = _ := by ring

theorem archivedGaussianTriangleWindowBound_iff_prime_squared :
    GaussianCutoffWindowBound archivedGaussianTriangleWindow ↔
      GaussianCutoffWindowBound archivedGaussianPrimeSquaredWindow := by
  apply gaussianCutoffWindowBound_iff_of_error (X₀ := 2)
  intro θ hθ _
  obtain ⟨C, hC, hE⟩ := archivedGaussianTriangleWindow_error
  refine ⟨C, hC, fun x hx => (hE x hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hθ.le) hC

theorem quartic_rh_of_archived_gaussian_triangle_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianTriangleWindow) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_prime_squared_windows hD hpos
    (archivedGaussianTriangleWindowBound_iff_prime_squared.mp hcut)

#print axioms archivedGaussianTriangleWindow_error
#print axioms archivedGaussianTriangleWindowBound_iff_prime_squared
#check quartic_rh_of_archived_gaussian_triangle_windows
#print axioms quartic_rh_of_archived_gaussian_triangle_windows

end
end AlpogeSuperZeta
