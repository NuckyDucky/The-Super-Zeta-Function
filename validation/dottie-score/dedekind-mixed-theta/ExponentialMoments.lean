import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Exact evaluation of polynomial moments of the exponential weight on a real panel. -/

namespace FieldTarget

open MeasureTheory Set
open scoped Interval

noncomputable section

def exponentialMoment (v : ℂ) (a b c : ℝ) (n : ℕ) : ℂ :=
  ∫ x in a..b, Complex.exp (v * (x : ℂ)) * ((x - c : ℝ) : ℂ) ^ n

private theorem shiftedPower_hasDerivAt (c x : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ ↦ ((y - c : ℝ) : ℂ) ^ (n + 1))
      ((n + 1 : ℂ) * ((x - c : ℝ) : ℂ) ^ n) x := by
  simpa only [Pi.pow_apply, id_eq, Nat.cast_succ, Nat.add_sub_cancel, mul_one, Complex.ofReal_sub] using
    (((hasDerivAt_id (x : ℂ)).sub_const (c : ℂ)).pow (n + 1)).comp_ofReal

theorem exponentialMoment_zero_rate (a b c : ℝ) (n : ℕ) :
    exponentialMoment 0 a b c n =
      (((b - c : ℝ) : ℂ) ^ (n + 1) - ((a - c : ℝ) : ℂ) ^ (n + 1)) / (n + 1 : ℂ) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ ↦ ((y - c : ℝ) : ℂ) ^ (n + 1) / (n + 1 : ℂ))
      (((x - c : ℝ) : ℂ) ^ n) x := by
    have h := (shiftedPower_hasDerivAt c x n).div_const (n + 1 : ℂ)
    rwa [mul_comm (n + 1 : ℂ), mul_div_cancel_right₀ _ hn] at h
  unfold exponentialMoment
  simp only [zero_mul, Complex.exp_zero, one_mul]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hd x)
    ((show Continuous (fun x : ℝ ↦ ((x - c : ℝ) : ℂ) ^ n) from by fun_prop).intervalIntegrable _ _)]
  ring

theorem exponentialMoment_zero_powers {v : ℂ} (hv : v ≠ 0) (a b c : ℝ) :
    exponentialMoment v a b c 0 =
      (Complex.exp (v * (b : ℂ)) - Complex.exp (v * (a : ℂ))) / v := by
  simpa only [exponentialMoment, pow_zero, mul_one] using
    (integral_exp_mul_complex (a := a) (b := b) hv)

private theorem dividedExp_hasDerivAt {v : ℂ} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Complex.exp (v * (y : ℂ)) / v) (Complex.exp (v * (x : ℂ))) x := by
  conv => congr
  rw [← mul_div_cancel_right₀ (Complex.exp (v * (x : ℂ))) hv]
  apply ((Complex.hasDerivAt_exp _).comp x _).div_const v
  simpa only [mul_one] using! ((hasDerivAt_id (x : ℂ)).const_mul v).comp_ofReal

/-- Each nonzero-rate moment uses only endpoint exponentials and the previous moment. -/
theorem exponentialMoment_succ {v : ℂ} (hv : v ≠ 0) (a b c : ℝ) (n : ℕ) :
    exponentialMoment v a b c (n + 1) =
      (Complex.exp (v * (b : ℂ)) * ((b - c : ℝ) : ℂ) ^ (n + 1) -
        Complex.exp (v * (a : ℂ)) * ((a - c : ℝ) : ℂ) ^ (n + 1) -
        (n + 1 : ℂ) * exponentialMoment v a b c n) / v := by
  have hp : IntervalIntegrable (fun x : ℝ ↦ (n + 1 : ℂ) * ((x - c : ℝ) : ℂ) ^ n) volume a b :=
    (show Continuous _ from by fun_prop).intervalIntegrable _ _
  have he : IntervalIntegrable (fun x : ℝ ↦ Complex.exp (v * (x : ℂ))) volume a b :=
    (show Continuous _ from by fun_prop).intervalIntegrable _ _
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ ↦ shiftedPower_hasDerivAt c x n) (fun x _ ↦ dividedExp_hasDerivAt hv x) hp he
  have hFactor (x : ℝ) :
      (n + 1 : ℂ) * ((x - c : ℝ) : ℂ) ^ n * (Complex.exp (v * (x : ℂ)) / v) =
      ((n + 1 : ℂ) / v) * (Complex.exp (v * (x : ℂ)) * ((x - c : ℝ) : ℂ) ^ n) := by ring
  simp_rw [hFactor, intervalIntegral.integral_const_mul] at h
  rw [exponentialMoment, show (fun x : ℝ ↦ Complex.exp (v * (x : ℂ)) * ((x - c : ℝ) : ℂ) ^ (n + 1)) =
    (fun x : ℝ ↦ ((x - c : ℝ) : ℂ) ^ (n + 1) * Complex.exp (v * (x : ℂ))) by funext x; exact mul_comm _ _,
    h, exponentialMoment]
  ring

end

#print axioms exponentialMoment_zero_rate
#print axioms exponentialMoment_zero_powers
#print axioms exponentialMoment_succ

end FieldTarget
