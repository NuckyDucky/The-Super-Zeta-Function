import SuperZeta.MarkedBranch
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! Finite coefficient arithmetic and complex interpolation for the two marks over 73. -/

namespace SuperZeta.FractionalTurnAt73

open Complex

/-- A signed prime contributes the geometric series with coefficient `a ^ n` in degree `n`. -/
noncomputable def signedGeometric (a : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => a ^ n

theorem signedGeometric_denominator (a : ℚ) :
    signedGeometric a * (1 - PowerSeries.C ℚ a * PowerSeries.X) = 1 := by
  rw [mul_sub, mul_one, ← mul_assoc]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero =>
    simp [signedGeometric, PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.constantCoeff_mk]
  | succ n =>
    simp [signedGeometric, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C,
      PowerSeries.coeff_one, pow_succ]

/-- The two local factors use the root counts of the marked quadratic at 27 and 46 mod 73. -/
noncomputable def localSeries : PowerSeries ℚ :=
  signedGeometric MarkedBranch.firstSign * signedGeometric MarkedBranch.secondSign

private theorem marks :
    MarkedBranch.firstSign = -1 ∧ MarkedBranch.secondSign = 1 := by
  norm_num [MarkedBranch.firstSign, MarkedBranch.secondSign, FieldWeights.root_counts_73]

theorem localSeries_denominator :
    localSeries * (1 - PowerSeries.X ^ 2) = 1 := by
  have h := congrArg₂ (· * ·) (signedGeometric_denominator MarkedBranch.firstSign)
    (signedGeometric_denominator MarkedBranch.secondSign)
  rw [marks.1, marks.2] at h
  simp only [map_neg, map_one, neg_one_mul, one_mul] at h
  unfold localSeries
  rw [marks.1, marks.2]
  calc
    _ = (signedGeometric (-1) * (1 - -PowerSeries.X)) *
        (signedGeometric 1 * (1-PowerSeries.X)) := by ring
    _ = _ := h

private theorem localSeries_coeff (m : ℕ) :
    PowerSeries.coeff ℚ m localSeries = ∑ j ∈ Finset.range (m+1), (-1 : ℚ)^j := by
  rw [localSeries, marks.1, marks.2, PowerSeries.coeff_mul]
  simp only [signedGeometric, PowerSeries.coeff_mk, one_pow, mul_one]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => (-1 : ℚ)^i) m

theorem localSeries_odd (n : ℕ) : PowerSeries.coeff ℚ (2*n+1) localSeries = 0 := by
  rw [localSeries_coeff]
  induction n with
  | zero => norm_num [Finset.sum_range_succ]
  | succ n ih =>
    rw [show 2*(n+1)+1+1 = (2*n+1+1)+1+1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, ih, pow_succ]
    ring

theorem localSeries_even (n : ℕ) : PowerSeries.coeff ℚ (2*n) localSeries = 1 := by
  cases n with
  | zero => simp [localSeries_coeff]
  | succ n =>
    have h := localSeries_odd n
    rw [localSeries_coeff] at h ⊢
    rw [Finset.sum_range_succ, show 2*(n+1) = 2*n+1+1 by omega, h, zero_add]
    simp [pow_add, pow_mul]

/-- The height chosen to make the doubled local phase a clockwise quarter-turn. -/
noncomputable def quarterHeight : ℝ := Real.pi / (4 * Real.log 73)

noncomputable def quarterInput : ℂ := 1/2 + (quarterHeight : ℂ) * I

/-- The positive-base Euler variable at the marked height. -/
noncomputable def primeVariable : ℂ := (73 : ℂ) ^ (-quarterInput)

/-- The doubled exponent coming from the height, before reducing its imaginary part. -/
noncomputable def heightLift : ℂ := -2 * quarterInput * (Real.log 73 : ℝ)

private theorem primeVariable_exp :
    primeVariable = exp (-quarterInput * (Real.log 73 : ℝ)) := by
  rw [primeVariable, Complex.cpow_def_of_ne_zero (by norm_num)]
  have hlog : log (73 : ℂ) = (Real.log 73 : ℝ) := by
    simpa only [Complex.ofReal_ofNat] using (Complex.ofReal_log (x := 73) (by norm_num)).symm
  rw [hlog]
  exact congrArg Complex.exp (mul_comm _ _)

theorem heightLift_explicit :
    heightLift = -(Real.log 73 : ℝ) - (Real.pi : ℂ)/2 * I := by
  have h : (Real.log 73 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h' : (↑(Real.log 73) : ℂ) ≠ 0 := by exact_mod_cast h
  have hc : log (73 : ℂ) ≠ 0 := by
    simpa only [Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 73), Complex.ofReal_ofNat] using h'
  unfold heightLift quarterInput quarterHeight
  push_cast only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_neg]
  field_simp [h', hc]
  ring

theorem heightLift_exp : exp heightLift = -I / 73 := by
  rw [heightLift_explicit, sub_eq_add_neg, exp_add, exp_neg, exp_neg, exp_pi_div_two_mul_I,
    Complex.inv_I]
  rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]
  norm_num only [Complex.ofReal_ofNat]
  ring

theorem heightLift_base_square : exp heightLift = primeVariable ^ 2 := by
  rw [primeVariable_exp, ← exp_nat_mul]
  congr 1
  unfold heightLift
  push_cast
  ring

theorem heightLift_midpoint : exp ((3/2 : ℂ) * heightLift) = primeVariable ^ 3 := by
  rw [primeVariable_exp, ← exp_nat_mul]
  congr 1
  unfold heightLift
  push_cast
  ring

theorem extra_turn_midpoint :
    exp ((3/2 : ℂ) * (heightLift + 2 * Real.pi * I)) = -primeVariable ^ 3 := by
  rw [mul_add, exp_add, heightLift_midpoint,
    show (3/2 : ℂ) * (2 * Real.pi * I) = (3 : ℕ) * ((Real.pi : ℂ) * I) by push_cast; ring,
    exp_nat_mul, exp_pi_mul_I]
  ring

theorem midpoint_recovers_root :
    exp ((3/2 : ℂ) * heightLift) / exp heightLift = primeVariable ∧
    exp ((3/2 : ℂ) * (heightLift + 2 * Real.pi * I)) / exp heightLift = -primeVariable := by
  have hx : primeVariable ≠ 0 := by rw [primeVariable_exp]; exact exp_ne_zero _
  rw [heightLift_midpoint, extra_turn_midpoint, heightLift_base_square]
  constructor <;> field_simp [hx] <;> ring

/-- A nonzero midpoint and the zero coefficient of that degree, in the same statement. -/
theorem midpoint_and_cubic_coefficient :
    exp ((3/2 : ℂ) * heightLift) = primeVariable ^ 3 ∧
    primeVariable ^ 3 ≠ 0 ∧ PowerSeries.coeff ℚ 3 localSeries = 0 := by
  exact ⟨heightLift_midpoint, by rw [← heightLift_midpoint]; exact exp_ne_zero _,
    localSeries_odd 1⟩

end SuperZeta.FractionalTurnAt73
