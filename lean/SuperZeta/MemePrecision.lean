import SuperZeta.Meme

/-! Certified decimal intervals for the original six-coefficient approximation. -/
namespace SuperZeta.Meme

open Lean Elab Tactic in
/-- Generate rational enclosures for nested square roots in the polygon
bounds on π. Mathlib checks every step by exact integer arithmetic. -/
private def polygonBound (upperPi : Bool) : TacticM Unit := do
  let d := 10^86
  let mut a := 0
  let mut witnesses := #[]
  for _ in [:62] do
    let k := Nat.sqrt ((2*d+a)*d)
    a := if upperPi then k else k+1
    witnesses := witnesses.push (← `($(quote a) / $(quote d)))
  if upperPi then
    evalTactic (← `(tactic| pi_upper_bound [$witnesses,*]))
  else
    evalTactic (← `(tactic| pi_lower_bound [$witnesses,*]))

elab "meme_lower_pi" : tactic => polygonBound false
elab "meme_upper_pi" : tactic => polygonBound true

set_option maxRecDepth 8000
set_option maxHeartbeats 5000000

theorem pi_bounds :
    3.14159265358979323846264338327950288 < Real.pi ∧
    Real.pi < 3.14159265358979323846264338327950289 := by
  constructor
  · meme_lower_pi
  · meme_upper_pi

theorem exp_one_bounds :
    2.71828182845904523536028747135266248 ≤ Real.exp 1 ∧
    Real.exp 1 ≤ 2.71828182845904523536028747135266252 := by
  have h : |Real.exp 1 - 2.71828182845904523536028747135266250| ≤ 1/10^35 := by
    apply Real.exp_approx_start
    iterate 34 refine Real.exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
    norm_num1
    refine Real.exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
    rw [abs_one, abs_le]
    constructor <;> norm_num1
  exact ⟨by linarith only [(abs_le.mp h).1], by linarith only [(abs_le.mp h).2]⟩

theorem ratio_bounds :
    1.7728776128573442028057927864223875 ≤ ratio (Real.exp 1) ∧
    ratio (Real.exp 1) ≤ 1.7728776128573442028057927864223879 := by
  obtain ⟨el,eh⟩ := exp_one_bounds
  have esl := mul_self_le_mul_self (by positivity) el
  have esh := mul_self_le_mul_self (Real.exp_pos 1).le eh
  have hd : 0 < denominator (Real.exp 1) := by
    unfold denominator
    nlinarith only [esl,el]
  unfold ratio
  rw [le_div_iff₀ hd, div_le_iff₀ hd]
  unfold numerator denominator
  constructor <;> nlinarith only [esl,esh,el,eh]

theorem target_bounds :
    1.7728776128573442027795613469919432 ≤ target Real.pi ∧
    target Real.pi ≤ 1.7728776128573442027795613469919434 := by
  obtain ⟨pl,ph⟩ := pi_bounds
  have psl := mul_self_le_mul_self (by positivity) pl.le
  have psh := mul_self_le_mul_self Real.pi_pos.le ph.le
  have hd : 0 < Real.pi^2+Real.pi-1 := by nlinarith only [pl,psl]
  unfold target
  rw [le_div_iff₀ hd, div_le_iff₀ hd]
  constructor <;> nlinarith only [psl,psh,pl,ph]

/-- Thirteen decimal significant digits of the signed discrepancy. -/
theorem signed_gap_precise :
    2.6231439430444/10^20 < ratio (Real.exp 1) - target Real.pi ∧
    ratio (Real.exp 1) - target Real.pi < 2.6231439430445/10^20 := by
  obtain ⟨rl,rh⟩ := ratio_bounds
  obtain ⟨tl,th⟩ := target_bounds
  constructor <;> linarith only [rl,rh,tl,th]

/-- An interval for the selected positive root, from the signs of its
quadratic at two rational test coordinates and the certified ratio. -/
theorem piHat_bounds :
    3.141592653589793238375823310552252 < piHat ∧
    piHat < 3.141592653589793238375823310552254 := by
  let n := numerator (Real.exp 1)
  let d := denominator (Real.exp 1)
  let r := ratio (Real.exp 1)
  let y := piHat
  obtain ⟨rl,rh⟩ := ratio_bounds
  change _ ≤ r at rl
  change r ≤ _ at rh
  have el := exp_one_bounds.1
  have es := mul_self_le_mul_self (by positivity) el
  have hd : 0 < d := by dsimp [d,denominator]; nlinarith only [el,es]
  have hr : r*d = n := div_mul_cancel₀ _ (ne_of_gt hd)
  have hnd : 0 < n-d := by
    rw [← hr]
    nlinarith only [mul_pos (show 0 < r-1 by linarith only [rl]) hd]
  have hy : 0 ≤ y := by
    change 0 ≤ (3*d-n+Real.sqrt (discriminant n d))/(2*(n-d))
    apply div_nonneg _ (by positivity)
    have hp := mul_pos (show 0 < 3-r by linarith only [rh]) hd
    nlinarith only [hp,hr,Real.sqrt_nonneg (discriminant n d)]
  have eqn := plusRoot_is_root n d hnd.ne'
  change (n-d)*y^2+(n-3*d)*y-(n+2*d) = 0 at eqn
  rw [← hr] at eqn
  let q := fun t : ℝ => (r-1)*t^2+(r-3)*t-(r+2)
  have hq : q y = 0 := by
    apply (mul_eq_zero.mp (show d*q y=0 by dsimp [q]; linear_combination eqn)).resolve_left hd.ne'
  have factor (t : ℝ) (ht : 3 ≤ t) : 0 < (r-1)*(t+y)+(r-3) := by
    have prod := mul_nonneg (show 0 ≤ r-1 by linarith only [rl])
      (show 0 ≤ t+y-3 by linarith only [ht,hy])
    nlinarith only [prod,rl]
  have diff (t : ℝ) : (t-y)*((r-1)*(t+y)+(r-3)) = q t := by
    dsimp [q] at hq ⊢
    linear_combination -hq
  let lo : ℝ := 3.141592653589793238375823310552252
  let hi : ℝ := 3.141592653589793238375823310552254
  have hlo : q lo < 0 := by dsimp [q,lo]; linarith only [rh]
  have hhi : 0 < q hi := by dsimp [q,hi]; linarith only [rl]
  change lo < y ∧ y < hi
  constructor
  · by_contra! hn
    exact (not_lt_of_ge (mul_nonneg (sub_nonneg.mpr hn) (factor lo (by norm_num [lo])).le))
      ((diff lo).trans_lt hlo)
  · by_contra! hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hn) (factor hi (by norm_num [hi])).le))
      (hhi.trans_eq (diff hi).symm)

/-- Signed error of the inverted approximation to π. -/
theorem piHat_gap_precise :
    8.682007272724/10^20 < Real.pi-piHat ∧ Real.pi-piHat < 8.682007272726/10^20 := by
  obtain ⟨pl,ph⟩ := pi_bounds
  obtain ⟨hl,hh⟩ := piHat_bounds
  constructor <;> linarith only [pl,ph,hl,hh]

end SuperZeta.Meme
