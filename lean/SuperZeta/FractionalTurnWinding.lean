import SuperZeta.FractionalTurnPower
import Mathlib.Topology.SeparatedMap
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Winding of the closed path made by taking one logarithmic power from
exponent 1 to 2, then taking a second one back from 2 to 1.  The winding
convention is the increment of a continuous argument divided by 2π. -/

open Complex Real Set
open SuperZeta.FractionalTurnPower (turn)

namespace SuperZeta.FractionalTurnWinding

/-- On the parameter interval [0,2], the exponent rises from 1 to 2 on the
first branch and falls from 2 to 1 on the second. -/
noncomputable def loop (l : ℂ) (m : ℤ) (t : ℝ) : ℂ :=
  if t ≤ 1 then Complex.exp ((1 + (t : ℂ)) * (l + turn m))
  else Complex.exp ((3 - (t : ℂ)) * l)

/-- The returning logarithm needs the constant 2·turn m to join the
outgoing logarithm at exponent 2. -/
noncomputable def loopLog (l : ℂ) (m : ℤ) (t : ℝ) : ℂ :=
  if t ≤ 1 then (1 + (t : ℂ)) * (l + turn m)
  else (3 - (t : ℂ)) * l + 2 * turn m

theorem exp_turn (m : ℤ) : Complex.exp (turn m) = 1 :=
  Complex.exp_int_mul_two_pi_mul_I m

theorem continuous_loopLog (l : ℂ) (m : ℤ) : Continuous (loopLog l m) := by
  unfold loopLog
  apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
  intro t ht
  change t = 1 at ht
  subst t
  push_cast
  ring

theorem exp_loopLog (l : ℂ) (m : ℤ) (t : ℝ) :
    Complex.exp (loopLog l m t) = loop l m t := by
  unfold loopLog loop
  split_ifs
  · rfl
  · rw [Complex.exp_add, two_mul, Complex.exp_add, exp_turn]
    simp

theorem continuous_loop (l : ℂ) (m : ℤ) : Continuous (loop l m) := by
  simpa only [Function.comp_def, exp_loopLog] using
    Complex.continuous_exp.comp (continuous_loopLog l m)

theorem loop_ne_zero (l : ℂ) (m : ℤ) (t : ℝ) : loop l m t ≠ 0 :=
  exp_loopLog l m t ▸ Complex.exp_ne_zero _

theorem loop_closed (l : ℂ) (m : ℤ) : loop l m 0 = loop l m 2 := by
  norm_num [loop, Complex.exp_add, exp_turn]

theorem loopLog_increment (l : ℂ) (m : ℤ) :
    loopLog l m 2 - loopLog l m 0 = turn m := by
  norm_num [loopLog]
  ring

private theorem exp_locally_injective : IsLocallyInjective Complex.exp := by
  intro a
  let U := (fun z : ℂ => (z-a).im) ⁻¹' Ioo (-Real.pi) Real.pi
  have hc : Continuous (fun z : ℂ => (z-a).im) := by fun_prop
  refine ⟨U, isOpen_Ioo.preimage hc, ?_, ?_⟩
  · simp [U, Real.pi_pos]
  · intro b hb c hc h
    change -Real.pi < (b-a).im ∧ (b-a).im < Real.pi at hb
    change -Real.pi < (c-a).im ∧ (c-a).im < Real.pi at hc
    have hh : b - a = c - a :=
      Complex.exp_inj_of_neg_pi_lt_of_le_pi hb.1 hb.2.le hc.1 hc.2.le (by simp only [Complex.exp_sub, h])
    exact sub_left_inj.mp hh

/-- Every continuous logarithm of this *same path on the closed interval* has
the same increment, even if it starts on an arbitrary sheet. -/
theorem every_loopLog_increment (l : ℂ) (m : ℤ) (L : ℝ → ℂ)
    (hcontinuous : ContinuousOn L (Icc 0 2))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 2, Complex.exp (L t) = loop l m t) :
    L 2 - L 0 = turn m := by
  let D := fun t => L t - loopLog l m t
  have hD : ContinuousOn D (Icc 0 2) :=
    hcontinuous.sub (continuous_loopLog l m).continuousOn
  have h1 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 2) : Complex.exp (D t) = 1 := by
    simp [D, Complex.exp_sub, hlift t ht, exp_loopLog, loop_ne_zero]
  have heq := (T2Space.isSeparatedMap Complex.exp).constOn_of_comp exp_locally_injective
    isPreconnected_Icc hD (fun s hs t ht => (h1 s hs).trans (h1 t ht).symm)
    (a := 2) (a' := 0) (by constructor <;> norm_num) (by constructor <;> norm_num)
  change L 2 - loopLog l m 2 = L 0 - loopLog l m 0 at heq
  linear_combination heq + loopLog_increment l m

/-- The standard continuous-argument winding count, evaluated using any
continuous logarithm of the actual closed path. -/
theorem winding_eq (l : ℂ) (m : ℤ) (L : ℝ → ℂ)
    (hcontinuous : ContinuousOn L (Icc 0 2))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 2, Complex.exp (L t) = loop l m t) :
    ((L 2).im - (L 0).im) / (2 * Real.pi) = (m : ℝ) := by
  have h := congrArg Complex.im (every_loopLog_increment l m L hcontinuous hlift)
  simp [turn, Complex.mul_im, Complex.mul_re] at h
  apply (div_eq_iff (by positivity : 2 * Real.pi ≠ 0)).mpr
  linarith

end SuperZeta.FractionalTurnWinding
