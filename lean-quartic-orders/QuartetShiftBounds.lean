import SuperZeta.UnitSpectrum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Geometry of the upper cosine roots and the real comparison points πn. -/
namespace SuperZeta.QuartetShiftBounds
noncomputable section
open RootBounds QuartetRadius Real Complex Set
open scoped ComplexConjugate

private theorem coordinates {t : ℝ} (ht : 0 < t) :
    Real.sinh t ^ 2 ≤ (x t)^2 + t^2 := by
  have hs := Real.sinh_pos_iff.mpr ht
  have ha : 0 ≤ a t := div_nonneg ht.le hs.le
  have hb : a t ≤ 1 := (div_le_one hs).mpr (Real.self_le_sinh_iff.mpr ht.le)
  have hc : Real.sinh t * Real.cos (θ t) = -t := by
    rw [θ, Real.cos_arccos (by linarith) (by linarith), a]
    field_simp [hs.ne']
    ring
  have h₁ := congrArg (fun b : ℝ => Real.sinh t ^2 * b) (Real.sin_sq_add_cos_sq (θ t))
  have h₂ := congrArg (fun b : ℝ => b^2) hc
  have h₃ := congrArg (fun b : ℝ => b * Real.sin (θ t)^2) (Real.cosh_sq_sub_sinh_sq t)
  dsimp only at h₁ h₂ h₃
  unfold x
  nlinarith only [h₁,h₂,h₃,sq_nonneg (Real.sin (θ t))]

theorem horizontal_strip {t : ℝ} {n : ℕ} (ht : 0 < t)
    (he : level t = 2 * π * n) :
    π * n - π/2 ≤ x t ∧ x t ≤ π * n := by
  have hθ := Real.arccos_le_pi (-a t)
  have ha : 0 ≤ a t := div_nonneg ht.le (Real.sinh_pos_iff.mpr ht).le
  have hθ' := Real.arccos_le_arccos (neg_nonpos.mpr ha)
  rw [Real.arccos_zero] at hθ'
  change 2*(Real.arccos (-a t) + x t) - π = _ at he
  constructor <;> linarith

theorem slope_bound {t : ℝ} {n : ℕ} (hn : 2 ≤ n) (ht : 0 < t)
    (he : level t = 2 * π * n) : t < (11/20 : ℝ) * x t := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hx := (horizontal_strip ht he).1
  have hlarge : 471/100 ≤ x t := by
    nlinarith only [hx,Real.pi_gt_d2,mul_nonneg (sub_nonneg.mpr hn') Real.pi_pos.le]
  have hsum := sum_le_hasSum (Finset.range 2) (fun n _ => by positivity) (Real.hasSum_sinh t)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hsum
  by_contra! bad
  have ht' : 259/100 ≤ t := by linarith
  have ht2 := mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 259/100) ht'
  have hs' : (21/10:ℝ) * t ≤ Real.sinh t := by
    nlinarith only [hsum, mul_le_mul_of_nonneg_right ht2 ht.le, ht]
  have hx' : x t ≤ (20/11 : ℝ) * t := by linarith
  have hsq := pow_le_pow_left₀ (show 0 ≤ x t by linarith) hx' 2
  have hss := pow_le_pow_left₀ (by positivity) hs' 2
  nlinarith only [hsq, hss, coordinates ht, sq_pos_of_pos ht]

theorem height_le_log {t : ℝ} {n : ℕ} (hn : 2 ≤ n) (ht : 0 < t)
    (he : level t = 2 * π * n) : t ≤ Real.log (3 * x t) := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hx' := RootBounds.x_lower (by omega : 0 < n) he
  have hx : 0<x t := by linarith
  have hst := slope_bound hn ht he
  have hs2 := pow_le_pow_left₀ ht.le hst.le 2
  have hs : Real.sinh t ≤ (5/4:ℝ)*x t := by
    by_contra! bad
    have b := mul_self_lt_mul_self (by positivity : 0 ≤ (5/4:ℝ)*x t) bad
    nlinarith only [b,hs2,coordinates ht,sq_pos_of_pos hx]
  have hneg : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq] at hs
  rw [← Real.exp_le_exp, Real.exp_log (by positivity)]
  linarith

theorem arg_bound_of_slope {z : ℂ} (hx : 0 < z.re)
    (hz : |z.im| ≤ 11/20 * z.re) : |z.arg| ≤ (11/20 : ℝ) := by
  have hlt := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx)
  have htan := Real.le_tan (abs_nonneg z.arg) hlt
  by_cases ha : 0 ≤ z.arg
  · rw [abs_of_nonneg ha, Complex.tan_arg] at htan
    rw [abs_of_nonneg ha]
    exact htan.trans ((div_le_iff₀ hx).mpr ((le_abs_self _).trans hz))
  · rw [abs_of_neg (lt_of_not_ge ha), Real.tan_neg, Complex.tan_arg, ← neg_div] at htan
    rw [abs_of_neg (lt_of_not_ge ha)]
    exact htan.trans ((div_le_iff₀ hx).mpr ((neg_le_abs _).trans hz))

theorem actual_angle (j : ℕ) (hj : 1 ≤ j) :
    2 * |(u (UnitSpectrum.levelHeight j)).arg| ≤ 11/10 := by
  obtain ⟨ht,he⟩ := UnitSpectrum.levelHeight_spec j
  have he' : level (UnitSpectrum.levelHeight j)=2*π*(j+1:ℕ) := by simpa using he
  have h := slope_bound (by omega) ht he'
  have hx := x_lower (Nat.succ_pos j) he'
  have hh : 0 < x (UnitSpectrum.levelHeight j) := lt_of_lt_of_le (by positivity) hx
  have ha := arg_bound_of_slope (z:=u (UnitSpectrum.levelHeight j)) hh
    (by change |UnitSpectrum.levelHeight j| ≤ _; rw [abs_of_pos ht]; exact h.le)
  linarith

end
end SuperZeta.QuartetShiftBounds
