import SuperZeta.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! The exponential half-stages in the normalized real parameter, including the
removable stage at zero. The fourth-order contrast is taken directly from
derivatives of the compositions, in their chronological order. -/

noncomputable section
namespace SuperZeta.Germ

def stage (a x : ℝ) : ℝ := if a = 0 then x else (Real.exp (a*x)-1)/a
def ordered (a b x : ℝ) := stage a (stage b x)

@[simp] theorem stage_zero (a : ℝ) : stage a 0 = 0 := by simp [stage]

theorem stage_hasDerivAt (a x : ℝ) : HasDerivAt (stage a) (Real.exp (a*x)) x := by
  by_cases ha : a = 0
  · subst a
    change HasDerivAt (fun u => stage 0 u) _ _
    simpa [stage] using hasDerivAt_id x
  · have h := ((((hasDerivAt_id x).const_mul a).exp.sub_const 1).div_const a)
    change HasDerivAt (fun u => stage a u) _ _
    simpa [stage, ha, mul_div_cancel_right₀] using h

private def innerExp (b x : ℝ) := Real.exp (b*x)
private def speed (a b x : ℝ) := Real.exp (a*stage b x) * innerExp b x
private def rate (a b x : ℝ) := a * innerExp b x + b
private def bend (a b x : ℝ) := a * b * innerExp b x

private theorem inner_d (b x : ℝ) : HasDerivAt (innerExp b) (innerExp b x * b) x := by
  simpa [innerExp] using ((hasDerivAt_id x).const_mul b).exp

private theorem first (a b x : ℝ) : HasDerivAt (ordered a b) (speed a b x) x :=
  (stage_hasDerivAt a (stage b x)).comp x (stage_hasDerivAt b x)

private theorem speed_d (a b x : ℝ) :
    HasDerivAt (speed a b) (speed a b x * rate a b x) x := by
  convert (((stage_hasDerivAt b x).const_mul a).exp.mul (inner_d b x)) using 1
  dsimp [speed, rate, innerExp]
  ring

private theorem rate_d (a b x : ℝ) : HasDerivAt (rate a b) (bend a b x) x := by
  convert ((inner_d b x).const_mul a).add_const b using 1
  dsimp [bend]; ring

private theorem bend_d (a b x : ℝ) : HasDerivAt (bend a b) (bend a b x*b) x := by
  convert (inner_d b x).const_mul (a*b) using 1
  dsimp [bend]; ring

private theorem second_d (a b x : ℝ) :
    HasDerivAt (fun u => speed a b u * rate a b u)
      (speed a b x * ((rate a b x)^2 + bend a b x)) x := by
  convert (speed_d a b x).mul (rate_d a b x) using 1
  ring

private theorem third_d (a b x : ℝ) :
    HasDerivAt (fun u => speed a b u * ((rate a b u)^2 + bend a b u))
      (speed a b x * ((rate a b x)^3 + 3*rate a b x*bend a b x + b*bend a b x)) x := by
  convert (speed_d a b x).mul (((rate_d a b x).pow 2).add (bend_d a b x)) using 1
  ring

private theorem d1 (a b : ℝ) : iteratedDeriv 1 (ordered a b) = speed a b := by
  funext x
  rw [iteratedDeriv_one]
  exact (first a b x).deriv

private theorem d2 (a b : ℝ) :
    iteratedDeriv 2 (ordered a b) = fun x => speed a b x * rate a b x := by
  rw [show 2 = 1+1 by rfl, iteratedDeriv_succ, d1]
  exact funext fun x => (speed_d a b x).deriv

private theorem d3 (a b : ℝ) :
    iteratedDeriv 3 (ordered a b) = fun x => speed a b x * ((rate a b x)^2 + bend a b x) := by
  rw [show 3 = 2+1 by rfl, iteratedDeriv_succ, d2]
  exact funext fun x => (second_d a b x).deriv

/-- Three lower derivatives agree after interchanging the stages. -/
theorem lower_orders (a b : ℝ) :
    iteratedDeriv 1 (ordered a b) 0 = 1 ∧
    iteratedDeriv 2 (ordered a b) 0 = a+b ∧
    iteratedDeriv 3 (ordered a b) 0 = (a+b)^2+a*b := by
  rw [d1, d2, d3]
  simp [speed, rate, bend, innerExp]

theorem actual_fourthCoeff (a b : ℝ) :
    iteratedDeriv 4 (ordered a b) 0 / 24 = SuperZeta.Order.fourthCoeff a b := by
  rw [show 4 = 3+1 by rfl, iteratedDeriv_succ, d3, (third_d a b 0).deriv]
  simp only [speed, stage_zero, innerExp, rate, bend, mul_zero, Real.exp_zero, mul_one]
  unfold SuperZeta.Order.fourthCoeff
  ring

/-- The signed distinction of the actual two nested exponential functions. -/
theorem actual_order_contrast (k : ℝ) :
    iteratedDeriv 4 (ordered k (2-k)) 0 / 24 -
    iteratedDeriv 4 (ordered (2-k) k) 0 / 24 = SuperZeta.Order.contrast k := by
  rw [actual_fourthCoeff, actual_fourthCoeff, SuperZeta.Order.order_difference]

end SuperZeta.Germ
