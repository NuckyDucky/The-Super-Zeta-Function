import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.Exponential

/-! Signed partial summation for the Gaussian block estimates. The order
of the complex coefficients is part of the input to the bound. -/

namespace QuarticModel

open Finset
open scoped BigOperators

theorem dottie_signed_block_variation (c f : ℕ → ℂ) (n : ℕ) (A : ℝ)
    (hprefix : ∀ k ≤ n + 1, ‖∑ i ∈ range k, c i‖ ≤ A) :
    ‖∑ i ∈ range (n + 1), f i * c i‖ ≤
      A * (‖f n‖ + ∑ i ∈ range n, ‖f (i + 1) - f i‖) := by
  have hparts := Finset.sum_range_by_parts f c (n + 1)
  simp only [smul_eq_mul, Nat.add_sub_cancel] at hparts
  rw [hparts]
  calc
    _ ≤ ‖f n * ∑ i ∈ range (n + 1), c i‖ +
        ‖∑ i ∈ range n, (f (i + 1) - f i) * ∑ j ∈ range (i + 1), c j‖ :=
      norm_sub_le _ _
    _ ≤ ‖f n‖ * A + ∑ i ∈ range n, ‖f (i + 1) - f i‖ * A := by
      refine add_le_add ?_ ((norm_sum_le _ _).trans ?_)
      · rw [Complex.norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix _ le_rfl) (norm_nonneg _)
      · refine sum_le_sum fun i hi => ?_
        rw [Complex.norm_mul]
        exact mul_le_mul_of_nonneg_left (hprefix _ (by have := mem_range.mp hi; omega))
          (norm_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem dottie_signed_block_lipschitz (c : ℕ → ℂ) (f : ℝ → ℂ) (u : ℕ → ℝ)
    (n : ℕ) (A L K : ℝ) (hu : Monotone u) (hu₀ : 0 ≤ u 0) (huN : u n ≤ L)
    (hK : 0 ≤ K)
    (hvariation : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ L → ‖f y - f x‖ ≤ K * (y - x))
    (hprefix : ∀ k ≤ n + 1, ‖∑ i ∈ range k, c i‖ ≤ A) :
    ‖∑ i ∈ range (n + 1), f (u i) * c i‖ ≤ A * (‖f (u n)‖ + K * L) := by
  have hA : 0 ≤ A := (norm_nonneg _).trans (hprefix 0 (Nat.zero_le _))
  refine (dottie_signed_block_variation c (fun i => f (u i)) n A hprefix).trans ?_
  apply mul_le_mul_of_nonneg_left _ hA
  apply add_le_add_right
  calc
    (∑ i ∈ range n, ‖f (u (i + 1)) - f (u i)‖) ≤
        ∑ i ∈ range n, K * (u (i + 1) - u i) := by
      refine sum_le_sum fun i hi => ?_
      exact hvariation _ _ (hu₀.trans (hu (Nat.zero_le _))) (hu (Nat.le_succ _))
        ((hu (mem_range.mp hi)).trans huN)
    _ = K * (u n - u 0) := by
      rw [← Finset.mul_sum]
      have telescope (j : ℕ) : (∑ i ∈ range j, (u (i + 1) - u i)) = u j - u 0 := by
        induction j with
        | zero => simp
        | succ j ih => rw [sum_range_succ, ih]; ring
      rw [telescope n]
    _ ≤ K * L := mul_le_mul_of_nonneg_left (by linarith) hK

private theorem exp_on_nonnegative_segment (z : ℂ) {x L : ℝ}
    (hx : 0 ≤ x) (hL : x ≤ L) :
    ‖Complex.exp (z * (x : ℂ))‖ ≤ Real.exp (‖z‖ * L) := by
  refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
  rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_left hL (norm_nonneg _)

private theorem exp_step (z : ℂ) {x y L : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) (hL : y ≤ L) :
    ‖Complex.exp (z * (y : ℂ)) - Complex.exp (z * (x : ℂ))‖ ≤
      ‖z‖ * Real.exp (‖z‖ * L) * (y - x) := by
  have hnorm : ‖z * ((y - x : ℝ) : ℂ)‖ = ‖z‖ * (y - x) := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy)]
  have hsplit : z * (y : ℂ) = z * (x : ℂ) + z * ((y - x : ℝ) : ℂ) := by
    push_cast
    ring
  have hproduct : Complex.exp (z * (y : ℂ)) - Complex.exp (z * (x : ℂ)) =
      Complex.exp (z * (x : ℂ)) * (Complex.exp (z * ((y - x : ℝ) : ℂ)) - 1) := by
    rw [hsplit, Complex.exp_add]
    ring
  have hrem := Complex.norm_exp_sub_sum_le_norm_mul_exp (z * ((y - x : ℝ) : ℂ)) 1
  simp only [sum_range_one, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, pow_one,
    hnorm] at hrem
  rw [hproduct, Complex.norm_mul]
  calc
    _ ≤ Real.exp (‖z‖ * x) * (‖z‖ * (y - x) * Real.exp (‖z‖ * (y - x))) :=
      mul_le_mul (exp_on_nonnegative_segment z hx le_rfl) hrem (norm_nonneg _)
        (Real.exp_pos _).le
    _ = Real.exp (‖z‖ * y) * (‖z‖ * (y - x)) := by
      rw [show ‖z‖ * y = ‖z‖ * x + ‖z‖ * (y - x) by ring, Real.exp_add]
      ring
    _ ≤ _ := by
      rw [show ‖z‖ * Real.exp (‖z‖ * L) * (y - x) =
          Real.exp (‖z‖ * L) * (‖z‖ * (y - x)) by ring]
      exact mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL (norm_nonneg _)))
        (mul_nonneg (norm_nonneg _) (sub_nonneg.mpr hxy))

theorem dottie_signed_block_exp_displacement (c : ℕ → ℂ) (u : ℕ → ℝ)
    (n : ℕ) (A L : ℝ) (z : ℂ) (hu : Monotone u) (hu₀ : 0 ≤ u 0) (huN : u n ≤ L)
    (hprefix : ∀ k ≤ n + 1, ‖∑ i ∈ range k, c i‖ ≤ A) :
    ‖∑ i ∈ range (n + 1), (Complex.exp (z * (u i : ℂ)) - 1) * c i‖ ≤
      2 * A * ‖z‖ * L * Real.exp (‖z‖ * L) := by
  let K := ‖z‖ * Real.exp (‖z‖ * L)
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have huN₀ : 0 ≤ u n := hu₀.trans (hu (Nat.zero_le _))
  have hA : 0 ≤ A := (norm_nonneg _).trans (hprefix 0 (Nat.zero_le _))
  have hvariation (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ L) :
      ‖(Complex.exp (z * (y : ℂ)) - 1) - (Complex.exp (z * (x : ℂ)) - 1)‖ ≤
        K * (y - x) := by
    convert exp_step z hx hxy hy using 2
    ring
  have hend : ‖Complex.exp (z * (u n : ℂ)) - 1‖ ≤ K * L := by
    have h := exp_step z (le_refl (0 : ℝ)) huN₀ huN
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, sub_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_left huN hK)
  refine (dottie_signed_block_lipschitz c
    (fun x => Complex.exp (z * (x : ℂ)) - 1) u n A L K hu hu₀ huN hK hvariation hprefix).trans ?_
  calc
    _ ≤ A * (K * L + K * L) := mul_le_mul_of_nonneg_left (add_le_add_left hend _) hA
    _ = _ := by dsimp [K]; ring

theorem dottie_signed_block_log_weight (c : ℕ → ℂ) (u : ℕ → ℝ)
    (n : ℕ) (A L : ℝ) (z : ℂ) (hu : Monotone u) (hu₀ : 0 ≤ u 0) (huN : u n ≤ L)
    (hprefix : ∀ k ≤ n + 1, ‖∑ i ∈ range k, c i‖ ≤ A) :
    ‖∑ i ∈ range (n + 1), ((u i : ℂ) * Complex.exp (z * (u i : ℂ))) * c i‖ ≤
      A * L * (2 + ‖z‖ * L) * Real.exp (‖z‖ * L) := by
  let E := Real.exp (‖z‖ * L)
  let K := (1 + ‖z‖ * L) * E
  have huN₀ : 0 ≤ u n := hu₀.trans (hu (Nat.zero_le _))
  have hL : 0 ≤ L := huN₀.trans huN
  have hK : 0 ≤ K := mul_nonneg (by positivity) (Real.exp_pos _).le
  have hA : 0 ≤ A := (norm_nonneg _).trans (hprefix 0 (Nat.zero_le _))
  have hvariation (x y : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ L) :
      ‖(y : ℂ) * Complex.exp (z * (y : ℂ)) -
        (x : ℂ) * Complex.exp (z * (x : ℂ))‖ ≤ K * (y - x) := by
    have hsplit : (y : ℂ) * Complex.exp (z * (y : ℂ)) -
        (x : ℂ) * Complex.exp (z * (x : ℂ)) =
        ((y - x : ℝ) : ℂ) * Complex.exp (z * (y : ℂ)) +
        (x : ℂ) * (Complex.exp (z * (y : ℂ)) - Complex.exp (z * (x : ℂ))) := by
      push_cast
      ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hxy), abs_of_nonneg hx]
    calc
      _ ≤ (y - x) * E + x * (‖z‖ * E * (y - x)) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left (exp_on_nonnegative_segment z (hx.trans hxy) hy)
            (sub_nonneg.mpr hxy))
          (mul_le_mul_of_nonneg_left (exp_step z hx hxy hy) hx)
      _ ≤ (y - x) * E + L * (‖z‖ * E * (y - x)) := by
        apply add_le_add_right
        exact mul_le_mul_of_nonneg_right (hxy.trans hy) (by positivity)
      _ = _ := by dsimp [K]; ring
  have hend : ‖(u n : ℂ) * Complex.exp (z * (u n : ℂ))‖ ≤ L * E := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg huN₀]
    exact mul_le_mul huN (exp_on_nonnegative_segment z huN₀ huN)
      (norm_nonneg _) hL
  refine (dottie_signed_block_lipschitz c
    (fun x => (x : ℂ) * Complex.exp (z * (x : ℂ))) u n A L K hu hu₀ huN hK hvariation
    hprefix).trans ?_
  calc
    _ ≤ A * (L * E + K * L) := mul_le_mul_of_nonneg_left (add_le_add_left hend _) hA
    _ = _ := by dsimp [K, E]; ring

#print axioms dottie_signed_block_variation
#print axioms dottie_signed_block_lipschitz
#print axioms dottie_signed_block_exp_displacement
#print axioms dottie_signed_block_log_weight

end QuarticModel
