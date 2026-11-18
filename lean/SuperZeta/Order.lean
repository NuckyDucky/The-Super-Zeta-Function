import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Reciprocal coordinates and the fourth-order contrast of the two ordered stages.
The fourth coefficient below composes the degree-four Taylor polynomials of
`(exp (a*x)-1)/a` and its opposite stage. The coefficient extends to a=0. -/
namespace SuperZeta.Order

noncomputable section

def cayley (a : ℂ) := a / (1+a)

theorem cayley_reciprocal (a : ℂ) (ha : a ≠ 0) (hb : 1+a ≠ 0) :
    cayley a⁻¹ = 1-cayley a := by
  have hc : 1+a⁻¹ ≠ 0 := by
    intro h
    apply hb
    field_simp [ha] at h
    linear_combination h
  unfold cayley
  apply (div_eq_iff hc).2
  field_simp [ha, hb]
  ring

/-- The contributions of outer powers 1, 2, 3 and 4, in that order. -/
def fourthCoeff (outer inner : ℝ) :=
  inner^3/24 + outer/2*(2*(inner^2/6)+(inner/2)^2) +
  outer^2/6*(3*(inner/2)) + outer^3/24

def contrast (k : ℝ) := k*(k-1)*(k-2)/12

theorem order_difference (k : ℝ) :
    fourthCoeff k (2-k) - fourthCoeff (2-k) k = contrast k := by
  unfold fourthCoeff contrast
  ring

def hurwitzPolynomial (q : ℝ) := -(1/12) + q/2 - q^2/2

theorem contrast_derivative (k : ℝ) :
    HasDerivAt contrast (-2 * hurwitzPolynomial (k/2)) k := by
  have h := ((((hasDerivAt_id k).mul ((hasDerivAt_id k).sub_const 1)).mul
    ((hasDerivAt_id k).sub_const 2)).div_const 12)
  convert h using 1
  simp [hurwitzPolynomial, id]
  ring

/-- Unique maximizer on the real limiting interval for the normalized phase. -/
theorem contrast_strict_max {k : ℝ} (hk : k ≤ 1) (hne : k ≠ 1-Real.sqrt 3/3) :
    contrast k < contrast (1-Real.sqrt 3/3) := by
  let c : ℝ := 1-Real.sqrt 3/3
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hc : 3*c^2-6*c+2=0 := by dsimp [c]; nlinarith
  have fact : contrast c - contrast k = (k-c)^2*(3-2*c-k)/12 := by
    unfold contrast
    linear_combination (c-k)/12*hc
  have hpos : 0 < 3-2*c-k := by
    dsimp [c]
    linarith [Real.sqrt_pos.2 (by norm_num : (0:ℝ)<3)]
  have hsq : 0 < (k-c)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  change contrast k < contrast c
  apply sub_pos.mp
  rw [fact]
  positivity

theorem selected_radius :
    let r := 2-Real.sqrt 3
    2*r/(1+r) = 1-Real.sqrt 3/3 ∧
    hurwitzPolynomial (r/(1+r)) = 0 := by
  dsimp
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hr : 1+(2-Real.sqrt 3) ≠ 0 := by intro h; nlinarith
  constructor
  · field_simp
    nlinarith
  · have hq : (2-Real.sqrt 3)/(1+(2-Real.sqrt 3)) = (1-Real.sqrt 3/3)/2 := by
      field_simp
      nlinarith
    rw [hq]
    unfold hurwitzPolynomial
    nlinarith

end
end SuperZeta.Order
