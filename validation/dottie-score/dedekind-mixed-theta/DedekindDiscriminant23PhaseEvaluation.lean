import DedekindDiscriminant23PhaseQuadrature
import ExponentialMoments

namespace FieldTarget

open MeasureTheory
open scoped Interval

noncomputable section

private theorem integral_input_exp_shiftedPower (v : ℂ) (a b c : ℝ) (n : ℕ) :
    (∫ x in a..b, (x : ℂ) * Complex.exp (v * (x : ℂ)) * ((x - c : ℝ) : ℂ) ^ n) =
      exponentialMoment v a b c (n + 1) + (c : ℂ) * exponentialMoment v a b c n := by
  unfold exponentialMoment
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add
      ((show Continuous (fun x : ℝ ↦ Complex.exp (v * (x : ℂ)) * ((x - c : ℝ) : ℂ) ^ (n + 1)) from
        by fun_prop).intervalIntegrable a b)
      ((show Continuous (fun x : ℝ ↦ (c : ℂ) * (Complex.exp (v * (x : ℂ)) * ((x - c : ℝ) : ℂ) ^ n)) from
        by fun_prop).intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro x _
  beta_reduce
  rw [pow_succ, Complex.ofReal_sub]
  ring

/-- The value uses the sum of the reflected moments. Differentiation uses their
difference and one extra moment to account for the log input. -/
def discriminant23PhaseMoment (odd : Bool) (w : ℂ) (a b c : ℝ) (n : ℕ) : ℂ :=
  if odd then
    (exponentialMoment w a b c (n + 1) + (c : ℂ) * exponentialMoment w a b c n) -
      (exponentialMoment (1 - w) a b c (n + 1) + (c : ℂ) * exponentialMoment (1 - w) a b c n)
  else exponentialMoment w a b c n + exponentialMoment (1 - w) a b c n

theorem discriminant23_phaseMoment_eq_integral (odd : Bool) (w : ℂ) (a b c : ℝ) (n : ℕ) :
    discriminant23PhaseMoment odd w a b c n =
      ∫ x in a..b, discriminant23PhaseWeight odd w x * ((x - c : ℝ) : ℂ) ^ n := by
  cases odd
  · change exponentialMoment w a b c n + exponentialMoment (1 - w) a b c n =
      ∫ x in a..b, (Complex.exp (w * (x : ℂ)) + Complex.exp ((1 - w) * (x : ℂ))) * ((x - c : ℝ) : ℂ) ^ n
    simp_rw [add_mul]
    unfold exponentialMoment
    rw [intervalIntegral.integral_add]
    all_goals exact (show Continuous _ from by fun_prop).intervalIntegrable a b
  · change _ = ∫ x in a..b,
      (x : ℂ) * (Complex.exp (w * (x : ℂ)) - Complex.exp ((1 - w) * (x : ℂ))) * ((x - c : ℝ) : ℂ) ^ n
    simp_rw [show ∀ x y z q : ℂ, x * (y - z) * q = x * y * q - x * z * q by intros; ring]
    rw [intervalIntegral.integral_sub,
      integral_input_exp_shiftedPower, integral_input_exp_shiftedPower]
    · rfl
    all_goals exact (show Continuous _ from by fun_prop).intervalIntegrable a b

/-- All theta coefficients are independent of the target input. The input
enters only through finite exponential moment recurrences. -/
theorem discriminant23_phaseTaylor_eq_moments (odd : Bool) (w : ℂ) :
    discriminant23PhaseTaylor odd w =
      ∑ k ∈ Finset.range 32, ∑ j ∈ Finset.range 20,
        let c : ℝ := (2 * (k : ℝ) + 1) * (3 / 64)
        contourTaylorCoeff discriminant23PanelDensity (c : ℂ) (1 / 4) j *
          discriminant23PhaseMoment odd w (c - 3 / 64) (c + 3 / 64) c j := by
  simp only [discriminant23PhaseTaylor, weightedContourTaylorComposite,
    weightedContourTaylorPanel, zero_add, ← discriminant23_phaseMoment_eq_integral]
  norm_num

end

#check @discriminant23_phaseTaylor_error
#check @discriminant23_phaseTaylor_eq_moments

#print axioms discriminant23_phaseMoment_eq_integral
#print axioms discriminant23_phaseTaylor_eq_moments

end FieldTarget
