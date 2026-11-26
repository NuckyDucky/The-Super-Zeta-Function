import GaussianPrimePrefixKernel

/-! Transfer one-sided estimates on prime windows to the actual norm windows. -/

namespace AlpogeSuperZeta

open Filter Finset Set Topology
open scoped Classical

noncomputable section

private theorem squaredRoundingWeightStep_sum_below {x Y : ℝ} (hx : 0 < x)
    (hY : 0 ≤ Y) (N : ℕ) :
    (∑ n ∈ range N, if 0 < n ∧ (n : ℝ) < Y then squaredRoundingWeightStep x n else 0) ≤
      (Y + 1) / (3 * x) := by
  let f (n : ℕ) : ℝ := (min ⌈Y⌉₊ n : ℕ)
  have hterm (n : ℕ) : (if 0 < n ∧ (n : ℝ) < Y then squaredRoundingWeightStep x n else 0) ≤
      (f (n + 1) - f n) * (1 / (3 * x)) := by
    by_cases h : 0 < n ∧ (n : ℝ) < Y
    · have hn := Nat.lt_ceil.mpr h.2
      rw [if_pos h]
      dsimp only [f]
      rw [min_eq_right (Nat.succ_le_of_lt hn), min_eq_right hn.le, Nat.cast_succ]
      calc
        _ ≤ 1 / (3 * x) := squaredRoundingWeightStep_le hx h.1
        _ = _ := by ring
    · rw [if_neg h]
      exact mul_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr
        (min_le_min (le_refl ⌈Y⌉₊) (Nat.le_succ n)))) (by positivity)
  calc
    _ ≤ ∑ n ∈ range N, (f (n + 1) - f n) * (1 / (3 * x)) :=
      sum_le_sum fun n _ => hterm n
    _ = f N * (1 / (3 * x)) := by rw [← sum_mul, sum_range_sub f]; simp [f]
    _ ≤ _ := by
      rw [mul_one_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact (Nat.cast_le.mpr (min_le_left ⌈Y⌉₊ N)).trans (Nat.ceil_lt_add_one hY).le

private theorem squaredRoundingWeightStep_sum_above {x Y θ : ℝ}
    (hx : 1 ≤ x) (hY : x ≤ Y) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (N : ℕ) :
    (∑ n ∈ range N, if Y ≤ (n : ℝ) then (n : ℝ) ^ θ * squaredRoundingWeightStep x n else 0) ≤
      x / (3 * (1 - θ)) * Y ^ (θ - 1) := by
  let f (n : ℕ) : ℝ := ((max ⌈Y⌉₊ n : ℕ) : ℝ) ^ (θ - 1)
  let C := x / (3 * (1 - θ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hY₀ : 0 < Y := one_pos.trans_le (hx.trans hY)
  have hp (n : ℕ) : 0 < ((max ⌈Y⌉₊ n : ℕ) : ℝ) :=
    hY₀.trans_le ((Nat.le_ceil Y).trans (Nat.cast_le.mpr (le_max_left _ _)))
  have hf (n : ℕ) : f (n + 1) ≤ f n :=
    Real.rpow_le_rpow_of_nonpos (hp n)
      (Nat.cast_le.mpr (max_le_max (le_refl ⌈Y⌉₊) (Nat.le_succ n))) (by linarith)
  have hterm (n : ℕ) :
      (if Y ≤ (n : ℝ) then (n : ℝ) ^ θ * squaredRoundingWeightStep x n else 0) ≤
        C * (f n - f (n + 1)) := by
    by_cases h : Y ≤ (n : ℝ)
    · have hn := Nat.ceil_le.mpr h
      have hn₀ : 0 < n := Nat.cast_pos.mp (hY₀.trans_le h)
      rw [if_pos h]
      dsimp only [f]
      rw [max_eq_right hn, max_eq_right (hn.trans (Nat.le_succ _))]
      exact squaredRoundingWeightStep_mul_rpow_le (zero_le_one.trans hx) hn₀
        (hY.trans h) hθ₀ hθ₁
    · rw [if_neg h]
      exact mul_nonneg hC (sub_nonneg.mpr (hf n))
  have h0 : f 0 ≤ Y ^ (θ - 1) := by
    change ((max ⌈Y⌉₊ 0 : ℕ) : ℝ) ^ (θ - 1) ≤ Y ^ (θ - 1)
    rw [max_eq_left (Nat.zero_le _)]
    exact Real.rpow_le_rpow_of_nonpos hY₀ (Nat.le_ceil Y) (by linarith)
  calc
    _ ≤ ∑ n ∈ range N, C * (f n - f (n + 1)) := sum_le_sum fun n _ => hterm n
    _ = C * (f 0 - f N) := by rw [← mul_sum, sum_range_sub' f]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((sub_le_self _ (Real.rpow_nonneg (hp N).le _)).trans h0) hC

private theorem squaredRoundingWeightStep_moment {x θ : ℝ} (hx : 1 ≤ x)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (N : ℕ) :
    (∑ n ∈ range N, (n : ℝ) ^ θ * squaredRoundingWeightStep x n) ≤
      (1 / 2 + 1 / (3 * (1 - θ))) * x ^ θ := by
  have hx₀ := one_pos.trans_le hx
  let κ := squaredRoundingWeightStep x
  let F (n : ℕ) := if x ≤ (n : ℝ) then (n : ℝ) ^ θ * κ n else 0
  have hterm (n : ℕ) : (n : ℝ) ^ θ * κ n ≤ x ^ θ * κ n + F n := by
    by_cases hn : x ≤ (n : ℝ)
    · simp only [F, if_pos hn]
      exact le_add_of_nonneg_left
        (mul_nonneg (Real.rpow_nonneg hx₀.le _) (squaredRoundingWeightStep_nonneg hx₀.le n))
    · simp only [F, if_neg hn, add_zero]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (Nat.cast_nonneg n) (le_of_not_ge hn) hθ₀)
          (squaredRoundingWeightStep_nonneg hx₀.le n)
  have hscale : x * x ^ (θ - 1) = x ^ θ := by
    rw [Real.rpow_sub_one hx₀.ne']
    field_simp
  calc
    _ ≤ ∑ n ∈ range N, (x ^ θ * κ n + F n) := sum_le_sum fun n _ => hterm n
    _ = x ^ θ * (∑ n ∈ range N, κ n) + ∑ n ∈ range N, F n := by
      rw [sum_add_distrib, mul_sum]
    _ ≤ x ^ θ * (1 / 2) + x / (3 * (1 - θ)) * x ^ (θ - 1) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (squaredRoundingWeightStep_sum_le_half hx₀.le N)
          (Real.rpow_nonneg hx₀.le _))
        (squaredRoundingWeightStep_sum_above hx le_rfl hθ₀ hθ₁ N)
    _ = _ := by rw [div_mul_eq_mul_div, hscale]; ring

/-- A signed bound within a finite prime window suffices for the squared cutoff at an
interior point, with explicit costs for the early and late prefixes. -/
theorem archivedGaussianPrimeSquaredWindow_le_of_local_prefix {x Y Z θ η A B : ℝ}
    (hY₀ : 1 ≤ Y) (hYx : Y ≤ x) (hxZ : x ≤ Z)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) (hη₀ : 0 ≤ η) (hη₁ : η < 1) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcenter : ArchivedGaussianPrimeCenterLimit)
    (hglobal : ∀ n : ℕ, |archivedGaussianSignedPrimePrefix n| ≤ B * (n : ℝ) ^ η)
    (hlocal : ∀ n : ℕ, Y ≤ (n : ℝ) → (n : ℝ) ≤ Z →
      archivedGaussianSignedPrimePrefix n ≤ A * (n : ℝ) ^ θ) :
    archivedGaussianPrimeSquaredWindow x ≤
      A * (1 / 2 + 1 / (3 * (1 - θ))) * x ^ θ +
        B * (Y + 1) * Y ^ η / (3 * x) + B * x / (3 * (1 - η)) * Z ^ (η - 1) := by
  have hx := hY₀.trans hYx
  have hx₀ := one_pos.trans_le hx
  have hY := zero_le_one.trans hY₀
  let P := archivedGaussianSignedPrimePrefix
  let κ := squaredRoundingWeightStep x
  let L (n : ℕ) := if 0 < n ∧ (n : ℝ) < Y then κ n else 0
  let U (n : ℕ) := if Z ≤ (n : ℝ) then (n : ℝ) ^ η * κ n else 0
  have hκ (n : ℕ) : 0 ≤ κ n := squaredRoundingWeightStep_nonneg hx₀.le n
  have hL (n : ℕ) : 0 ≤ L n := by
    dsimp [L]
    split
    · exact hκ n
    · exact le_rfl
  have hU (n : ℕ) : 0 ≤ U n := by
    dsimp [U]
    split
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (hκ n)
    · exact le_rfl
  have hterm (n : ℕ) : P n * κ n ≤ A * ((n : ℝ) ^ θ * κ n) + B * Y ^ η * L n + B * U n := by
    have hA₀ : 0 ≤ A * ((n : ℝ) ^ θ * κ n) :=
      mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (hκ n))
    have hL₀ : 0 ≤ B * Y ^ η * L n := mul_nonneg
      (mul_nonneg hB (Real.rpow_nonneg hY _)) (hL n)
    have hU₀ : 0 ≤ B * U n := mul_nonneg hB (hU n)
    have hg : P n ≤ B * (n : ℝ) ^ η := (le_abs_self _).trans (hglobal n)
    by_cases hzero : n = 0
    · subst n
      have hp0 : P 0 = 0 := by
        simp [P, archivedGaussianSignedPrimePrefix, archivedGaussianSignedPrimeWeight]
      rw [hp0, zero_mul]
      exact add_nonneg (add_nonneg hA₀ hL₀) hU₀
    by_cases hbefore : (n : ℝ) < Y
    · have hsmall : P n ≤ B * Y ^ η := hg.trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg n) hbefore.le hη₀) hB)
      have hb : P n * κ n ≤ B * Y ^ η * L n := by
        rw [show L n = κ n from if_pos ⟨Nat.pos_of_ne_zero hzero, hbefore⟩]
        exact mul_le_mul_of_nonneg_right hsmall (hκ n)
      linarith
    by_cases hafter : Z < (n : ℝ)
    · have hb : P n * κ n ≤ B * U n := by
        rw [show U n = (n : ℝ) ^ η * κ n from if_pos hafter.le, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hg (hκ n)
      linarith
    have hb : P n * κ n ≤ A * ((n : ℝ) ^ θ * κ n) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (hlocal n (le_of_not_gt hbefore) (le_of_not_gt hafter)) (hκ n)
    linarith
  have hlim := archivedGaussianPrimeSquaredWindow_prefixLimit hx hη₁ hcenter hglobal
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro N
  calc
    _ ≤ ∑ n ∈ range N, (A * ((n : ℝ) ^ θ * κ n) + B * Y ^ η * L n + B * U n) :=
      sum_le_sum fun n _ => hterm n
    _ = A * (∑ n ∈ range N, (n : ℝ) ^ θ * κ n) +
        B * Y ^ η * (∑ n ∈ range N, L n) + B * (∑ n ∈ range N, U n) := by
      simp only [sum_add_distrib, mul_sum]
    _ ≤ A * ((1 / 2 + 1 / (3 * (1 - θ))) * x ^ θ) +
        B * Y ^ η * ((Y + 1) / (3 * x)) + B * (x / (3 * (1 - η)) * Z ^ (η - 1)) := by
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (squaredRoundingWeightStep_moment hx hθ₀ hθ₁ N) hA)
        (mul_le_mul_of_nonneg_left (squaredRoundingWeightStep_sum_below hx₀ hY N)
          (mul_nonneg hB (Real.rpow_nonneg hY _))))
        (mul_le_mul_of_nonneg_left (squaredRoundingWeightStep_sum_above hx hxZ hη₀ hη₁ N) hB)
    _ = _ := by ring

#print axioms archivedGaussianPrimeSquaredWindow_le_of_local_prefix

end

end AlpogeSuperZeta
