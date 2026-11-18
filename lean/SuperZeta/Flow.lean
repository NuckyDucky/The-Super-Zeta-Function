import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The regular response equations follow by differentiating the original
lifted exponential equations in local time `t`, where `L = L₀ exp t`. -/
namespace SuperZeta.Flow
open Complex Filter
open scoped Topology

theorem response {U V : ℂ → ℂ} {L₀ t u' v' : ℂ}
    (hU : HasDerivAt U u' t) (hV : HasDerivAt V v' t)
    (hu : U =ᶠ[𝓝 t] fun z => L₀ * exp z * exp (V z))
    (hv : V =ᶠ[𝓝 t] fun z => -(L₀ * exp z) * exp (U z))
    (hreg : 1-U t*V t ≠ 0) :
    HasDerivAt (fun z => (U z+V z)/2)
      (((U t+V t)/2+U t*V t)/(1-U t*V t)) t ∧
    HasDerivAt (fun z => U z*V z)
      ((2*(U t*V t)*(1+(U t+V t)/2))/(1-U t*V t)) t := by
  have h₁ := (((Complex.hasDerivAt_exp t).const_mul L₀).mul hV.cexp).congr_of_eventuallyEq hu
  have h₂ := ((((Complex.hasDerivAt_exp t).const_mul L₀).neg).mul hU.cexp).congr_of_eventuallyEq hv
  have du : u' = U t*(1+v') := by
    rw [hu.eq_of_nhds]
    simpa only [mul_add, mul_one, mul_assoc] using hU.unique h₁
  have dv : v' = V t*(1+u') := by
    rw [hv.eq_of_nhds]
    simpa only [mul_add, mul_one, mul_assoc] using hV.unique h₂
  have su : u'*(1-U t*V t) = U t*(1+V t) := by linear_combination du + U t*dv
  have sv : v'*(1-U t*V t) = V t*(1+U t) := by linear_combination dv + V t*du
  constructor
  · convert (hU.add hV).div_const 2 using 1
    field_simp [hreg]
    linear_combination -2*su-2*sv
  · convert hU.mul hV using 1
    field_simp [hreg]
    linear_combination -2*V t*su-2*U t*sv

/-- The regular polynomial clock preserves the exponential law for μ−a²,
including at μ=1 where the logarithmic coordinate becomes singular. -/
theorem transverse_flow {a μ : ℂ → ℂ} {z : ℂ}
    (ha : HasDerivAt a (a z+μ z) z)
    (hm : HasDerivAt μ (2*μ z*(1+a z)) z) :
    HasDerivAt (fun w => μ w-(a w)^2) (2*(μ z-(a z)^2)) z := by
  simp only [pow_two]
  convert hm.sub (ha.mul ha) using 1
  ring
end SuperZeta.Flow
