import MellinFixedFunctions
import MellinFixedIntervalSound
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! A geometric remainder bound for the odd logarithm series. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.MellinFixed

private def oddCoefficient (k : Nat) : Box := fromRatio 1 (2*k+1 : ℕ)

private theorem odd_table : oddReciprocals = coefficients oddCoefficient 0 40 := by
  decide +kernel

private theorem odd_coefficient_contains (k : Nat) :
    Contains (oddCoefficient k) (1/(2*(k:ℝ)+1)) := by
  have hk : (0:ℤ) < ((2*k+1 : ℕ):ℤ) := by omega
  have hd : (((2*k+1:ℕ):ℤ):ℝ) = 2*(k:ℝ)+1 := by push_cast; rfl
  rw [← hd]
  simpa only [oddCoefficient, Int.cast_one] using ratio_contains 1 hk

private theorem log_tail {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1/2) :
    |(Real.log (1-q)-Real.log (1+q)) -
        (-2*(q * (∑ k ∈ Finset.range 40, (1/(2*(k:ℝ)+1))*(q*q)^k)))|
      ≤ 2/(scale:ℝ) := by
  let a := fun k : ℕ => (2:ℝ)*(1/(2*(k:ℝ)+1))*q^(2*k+1)
  have hq1 : |q| < 1 := by rw [abs_of_nonneg hq]; linarith
  have hs : HasSum a (Real.log (1+q)-Real.log (1-q)) :=
    Real.hasSum_log_sub_log_of_abs_lt_one hq1
  have ht : HasSum (fun j => a (j+40))
      ((Real.log (1+q)-Real.log (1-q)) - ∑ k ∈ Finset.range 40, a k) :=
    (hasSum_nat_add_iff' 40).mpr hs
  have hp : (∑ k ∈ Finset.range 40, a k) =
      2*(q*(∑ k ∈ Finset.range 40, (1/(2*(k:ℝ)+1))*(q*q)^k)) := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [a, pow_succ q (2*k), pow_mul q 2 k, pow_two q]
    ring
  have hcon : (Real.log (1-q)-Real.log (1+q)) -
        (-2*(q * (∑ k ∈ Finset.range 40, (1/(2*(k:ℝ)+1))*(q*q)^k))) =
      -(∑' j : ℕ, a (j+40)) := by
    rw [ht.tsum_eq, hp]
    ring
  let b := fun j : ℕ => (2*(1/2:ℝ)^81)*(1/4:ℝ)^j
  have hb (j : ℕ) : a (j+40) ≤ b j := by
    have ha : 1/(2*((j+40:ℕ):ℝ)+1) ≤ (1:ℝ) := by
      rw [div_le_one (by positivity : (0:ℝ) < 2*((j+40:ℕ):ℝ)+1)]
      have : (0:ℝ) ≤ ((j+40:ℕ):ℝ) := by positivity
      linarith
    calc
      _ ≤ 2*(1/2:ℝ)^(2*(j+40)+1) := by
        dsimp only [a]
        calc
          _ ≤ 2*1*q^(2*(j+40)+1) := by gcongr
          _ ≤ _ := by rw [mul_one]; gcongr
      _ = b j := by
        rw [show 2*(j+40)+1=81+2*j by omega, pow_add, pow_mul]
        norm_num [b, mul_assoc]
        ring
  have hsb : Summable b := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ) < 1)).mul_left _
  have hnon (j : ℕ) : 0 ≤ a (j+40) := by dsimp only [a]; positivity
  rw [hcon, abs_neg, abs_of_nonneg (tsum_nonneg hnon)]
  calc
    _ ≤ ∑' j : ℕ, b j := ht.summable.tsum_le_tsum hb hsb
    _ ≤ _ := by
      rw [show (∑' j : ℕ, b j) = (2*(1/2:ℝ)^81)*(1-(1/4:ℝ))⁻¹ by
        simp only [b, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
          (by norm_num : (1/4:ℝ) < 1)]]
      norm_num [scale]

theorem logDomain_contains {a : Box} {q : ℝ} (h : Contains a q)
    (hb : inLogDomain a = true) : 0 ≤ q ∧ q ≤ 1/2 := by
  have hd : 0 ≤ a.lo ∧ 2*a.hi ≤ scale := of_decide_eq_true hb
  have hlo : (0:ℝ) ≤ (a.lo:ℝ) := by exact_mod_cast hd.1
  have hhi : (2:ℝ)*(a.hi:ℝ) ≤ (scale:ℝ) := by exact_mod_cast hd.2
  refine ⟨nonneg_of_mul_nonneg_right (hlo.trans h.1) scale_pos, ?_⟩
  apply le_of_mul_le_mul_left _ scale_pos
  linarith only [h.2, hhi]

theorem logGapFixed_contains {a : Box} {q : ℝ} (h : Contains a q)
    (hb : inLogDomain a = true) :
    Contains (logGapFixed a) (Real.log (1-q)-Real.log (1+q)) := by
  have hd := logDomain_contains h hb
  have hp := horner_contains (mul_contains h h) oddCoefficient _ odd_coefficient_contains 0 40
  rw [← odd_table] at hp
  simp only [Nat.zero_add] at hp
  have ht := mul_contains (constant_contains (-2)) (mul_contains h hp)
  simp only [Int.cast_neg, Int.cast_ofNat] at ht
  exact widen_contains ht (units := 2) (by
    simpa only [Nat.cast_ofNat] using log_tail hd.1 hd.2)

#print axioms logGapFixed_contains

end DottieOriented.NativeSpectrum.MellinFixed
end
