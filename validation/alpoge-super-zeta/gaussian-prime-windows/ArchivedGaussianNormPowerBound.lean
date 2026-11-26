import ArchivedGaussianNormCriterion
import GaussianSquaredRoundingResidual
import Mathlib.Algebra.BigOperators.Module

/-! Transfer signed prime-prefix bounds to the retained ideal norms of the archived quartic. -/

namespace AlpogeSuperZeta

open Finset

noncomputable section

private theorem weighted_sum_le_of_prefix_le (a w : ℕ → ℝ) (n : ℕ) {M : ℝ}
    (hw : Antitone w) (hw₀ : 0 ≤ w n)
    (hprefix : ∀ m ≤ n, (∑ i ∈ range (m + 1), a i) ≤ M) :
    (∑ i ∈ range (n + 1), a i * w i) ≤ M * w 0 := by
  let P (m : ℕ) := ∑ i ∈ range (m + 1), a i
  have hparts : (∑ i ∈ range (n + 1), a i * w i) =
      w n * P n - ∑ i ∈ range n, (w (i + 1) - w i) * P i := by
    simpa only [P, smul_eq_mul, Nat.add_sub_cancel, mul_comm] using
      (sum_range_by_parts w a (n + 1))
  rw [hparts]
  calc
    _ ≤ w n * M - ∑ i ∈ range n, (w (i + 1) - w i) * M := by
      apply sub_le_sub (mul_le_mul_of_nonneg_left (hprefix n le_rfl) hw₀)
      apply sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonpos_left (hprefix i (mem_range.mp hi).le)
        (sub_nonpos.mpr (hw (Nat.le_succ i)))
    _ = _ := by
      rw [← sum_mul, sum_range_sub w]
      ring

private def roundingWeight (x : ℝ) (p : ℕ) : ℝ :=
  if p = 0 then 1 / 2 else squaredRoundingResidual (x / (p : ℝ))

private theorem roundingWeight_nonneg {x : ℝ} (hx : 0 ≤ x) (p : ℕ) :
    0 ≤ roundingWeight x p := by
  by_cases h : p = 0
  · simp [roundingWeight, h]
  · simpa only [roundingWeight, if_neg h] using
      squaredRoundingResidual_nonneg (div_nonneg hx (Nat.cast_nonneg p))

private theorem roundingWeight_antitone {x : ℝ} (hx : 0 ≤ x) : Antitone (roundingWeight x) := by
  intro m n hmn
  by_cases hn : n = 0
  · have hm := Nat.eq_zero_of_le_zero (hn ▸ hmn)
    simp [hn, hm]
  by_cases hm : m = 0
  · simpa only [roundingWeight, if_neg hn, if_pos hm] using
      squaredRoundingResidual_le_half (div_nonneg hx (Nat.cast_nonneg n))
  rw [roundingWeight, if_neg hn, roundingWeight, if_neg hm]
  apply squaredRoundingResidual_monotoneOn (div_nonneg hx (Nat.cast_nonneg n))
    (div_nonneg hx (Nat.cast_nonneg m))
  exact div_le_div_of_nonneg_left hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm))
    (Nat.cast_le.mpr hmn)

/-- The signed prefix of the actual degree-one Gaussian prime coefficients. -/
def archivedGaussianSignedPrimePrefix (n : ℕ) : ℝ :=
  ∑ p ∈ range (n + 1), -archivedGaussianSignedPrimeWeight p

/-- The finite reciprocal prime sum measured from the actual logarithmic-derivative center. -/
def archivedGaussianReciprocalCenterError (x : ℝ) : ℝ :=
  (∑ p ∈ range (⌊x⌋₊ + 1), archivedGaussianSignedPrimeWeight p / (p : ℝ)) -
    archivedGaussianPrimeCenter

private theorem archivedGaussianPrimeSquaredWindow_eq_rounding {x : ℝ} (hx : 1 ≤ x) :
    archivedGaussianPrimeSquaredWindow x =
      (∑ p ∈ range (⌊x⌋₊ + 1), (-archivedGaussianSignedPrimeWeight p) * roundingWeight x p) +
        x / 3 * archivedGaussianReciprocalCenterError x := by
  let b := archivedGaussianSignedPrimeWeight
  let S (p : ℕ) := ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * p)
  have hterm (p : ℕ) : b p * S p = (-b p) * roundingWeight x p + (x / 3) * (b p / (p : ℝ)) := by
    by_cases hp : p = 0
    · simp [hp, b, archivedGaussianSignedPrimeWeight]
    · rw [roundingWeight, if_neg hp,
        squaredRoundingResidual_at_prime (one_pos.trans_le hx) (Nat.pos_of_ne_zero hp)]
      change b p * S p = (-b p) * (x / (3 * (p : ℝ)) - S p) + (x / 3) * (b p / (p : ℝ))
      ring
  rw [archivedGaussianPrimeSquaredWindow_eq_sum hx]
  change (∑ p ∈ range (⌊x⌋₊ + 1), b p * S p) - _ = _
  simp_rw [hterm]
  rw [sum_add_distrib, ← mul_sum]
  unfold archivedGaussianReciprocalCenterError
  ring

/-- At a given cutoff, the squared ramp preserves the upper bound on the signed prime prefixes. -/
theorem archivedGaussianPrimeSquaredWindow_le_of_prefix_le {x M : ℝ} (hx : 1 ≤ x)
    (hprefix : ∀ n ≤ ⌊x⌋₊, archivedGaussianSignedPrimePrefix n ≤ M) :
    archivedGaussianPrimeSquaredWindow x ≤ M / 2 + x / 3 * archivedGaussianReciprocalCenterError x := by
  rw [archivedGaussianPrimeSquaredWindow_eq_rounding hx]
  refine add_le_add ?_ le_rfl
  have h := weighted_sum_le_of_prefix_le (fun p => -archivedGaussianSignedPrimeWeight p)
    (roundingWeight x) ⌊x⌋₊ (roundingWeight_antitone (zero_le_one.trans hx))
    (roundingWeight_nonneg (zero_le_one.trans hx) _) hprefix
  rwa [show roundingWeight x 0 = 1 / 2 by simp [roundingWeight], mul_one_div] at h

namespace GaussianQuarticClosure

/-- A prime-prefix bound and a reciprocal-center bound at one exponent transfer to the exact
signed ideal norm, with the existing square-root-scale error included. -/
theorem archivedGaussianNorm_le_of_prime_bounds {θ : ℝ} (hθ : 1 / 2 < θ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hprefix : ∀ n : ℕ, archivedGaussianSignedPrimePrefix n ≤ A * (n : ℝ) ^ θ)
    (hcenter : ∀ x ≥ (1 : ℝ), archivedGaussianReciprocalCenterError x ≤ B * x ^ (θ - 1)) :
    ∃ X C : ℝ, 1 ≤ X ∧ 0 ≤ C ∧
      ∀ x ≥ X, archivedGaussianRetainedNormWindow x ≤ C * x ^ θ := by
  obtain ⟨X₀, hData⟩ := eventually_retainedPrimeData
  let W (p : ℕ) := |archivedGaussianSignedPrimeWeight p| /
    ((max 1 p : ℕ) : ℝ) ^ (1 + (θ - 1 / 2))
  let E := 10 * ∑' p, W p
  have hE : 0 ≤ E := by
    apply mul_nonneg (by norm_num)
    exact tsum_nonneg fun p => by dsimp [W]; positivity
  refine ⟨max 2 X₀, A / 2 + B / 3 + E, by linarith [le_max_left (2 : ℝ) X₀],
    by positivity, ?_⟩
  intro x hx
  have hx₂ := (le_max_left (2 : ℝ) X₀).trans hx
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := one_pos.trans_le hx₁
  obtain ⟨frob, hFrob⟩ := hData x ((le_max_right (2 : ℝ) X₀).trans hx)
  have hscale : 1 ≤ gaussianSqrtTriangleScale x := by
    have hp := Real.one_le_rpow hx₁ (by norm_num : 0 ≤ (1 / 2 : ℝ))
    dsimp [gaussianSqrtTriangleScale]
    linarith
  have hError := (abs_le.mp (archivedGaussianTriangleAtScale_error hx₂ hscale le_rfl hθ)).2
  change archivedGaussianSqrtTriangleWindow x - archivedGaussianPrimeSquaredWindow x ≤
    E * x ^ θ at hError
  have hP : ∀ n ≤ ⌊x⌋₊, archivedGaussianSignedPrimePrefix n ≤ A * x ^ θ := by
    intro n hn
    exact (hprefix n).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n)
        ((Nat.cast_le.mpr hn).trans (Nat.floor_le hx₀.le)) (by linarith)) hA)
  have hC : x / 3 * archivedGaussianReciprocalCenterError x ≤ (B / 3) * x ^ θ := by
    calc
      _ ≤ x / 3 * (B * x ^ (θ - 1)) :=
        mul_le_mul_of_nonneg_left (hcenter x hx₁) (by positivity)
      _ = (B / 3) * (x ^ (1 : ℝ) * x ^ (θ - 1)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [← Real.rpow_add hx₀, show (1 : ℝ) + (θ - 1) = θ by ring]
  rw [archivedGaussianRetainedNormWindow_eq hFrob]
  have hSquare := archivedGaussianPrimeSquaredWindow_le_of_prefix_le hx₁ hP
  calc
    _ ≤ archivedGaussianPrimeSquaredWindow x + E * x ^ θ := sub_le_iff_le_add'.mp hError
    _ ≤ (A / 2 + B / 3 + E) * x ^ θ := by linarith

end GaussianQuarticClosure

#print axioms squaredRoundingResidual_monotoneOn
#print axioms squaredRoundingResidual_le_half
#print axioms archivedGaussianPrimeSquaredWindow_le_of_prefix_le
#check GaussianQuarticClosure.archivedGaussianNorm_le_of_prime_bounds
#print axioms GaussianQuarticClosure.archivedGaussianNorm_le_of_prime_bounds

end

end AlpogeSuperZeta
