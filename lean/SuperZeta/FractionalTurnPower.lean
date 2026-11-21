import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Fractional powers of a nonzero complex value from its chosen logarithm.
The integer indexes all lifts of the logarithm, and the exponent is real. -/
noncomputable section
namespace SuperZeta.FractionalTurnPower

open Complex

/-- The change in a logarithm after `k` extra counterclockwise turns. -/
def turn (k : ℤ) : ℂ := (k : ℂ) * (2 * Real.pi * I)

/-- The fractional power formed using `L + turn k` as the logarithm. -/
def reading (L : ℂ) (k : ℤ) (x : ℝ) : ℂ := exp ((x : ℂ) * (L + turn k))

theorem exp_eq_iff_turn (L' L : ℂ) : exp L' = exp L ↔ ∃ k : ℤ, L' = L + turn k := by
  simpa [turn, add_comm] using (Complex.exp_eq_exp_iff_exists_int (x := L') (y := L))

theorem reading_ne_zero (L : ℂ) (k : ℤ) (x : ℝ) : reading L k x ≠ 0 :=
  exp_ne_zero _

theorem reading_ratio (L : ℂ) (k j : ℤ) (x : ℝ) :
    reading L k x / reading L j x = exp ((x : ℂ) * turn (k - j)) := by
  rw [reading, reading, ← exp_sub]
  congr 1
  unfold turn
  push_cast
  ring

/-- Two sheets agree at a real exponent precisely when their extra phase is an integer turn. -/
theorem reading_eq_iff (L : ℂ) (k j : ℤ) (x : ℝ) :
    reading L k x = reading L j x ↔ ∃ m : ℤ, x * ((k : ℝ) - j) = m := by
  rw [← div_eq_one_iff_eq (reading_ne_zero L j x), reading_ratio, Complex.exp_eq_one_iff]
  apply exists_congr
  intro m
  unfold turn
  push_cast
  rw [← mul_assoc, mul_left_inj' Complex.two_pi_I_ne_zero]
  norm_cast

theorem reading_one (L : ℂ) (k : ℤ) : reading L k 1 = exp L := by
  simp [reading, turn, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]

theorem reading_two (L : ℂ) (k : ℤ) : reading L k 2 = (exp L)^2 := by
  calc
    _ = exp (L + turn k) ^ 2 := by simp [reading, two_mul, exp_add, pow_two]
    _ = _ := by simp [turn, exp_add, Complex.exp_int_mul_two_pi_mul_I]

/-- Dividing the exponent-3/2 reading by the common start returns a signed square root. -/
theorem midpoint_div_start (L : ℂ) (k : ℤ) :
    reading L k (3/2) / exp L = (-1 : ℂ)^k * exp (L/2) := by
  rw [reading, ← exp_sub]
  push_cast
  have h : (3 / 2 : ℂ) * (L + turn k) - L =
      turn k + ((k : ℂ) * (Real.pi * I) + L/2) := by unfold turn; ring
  rw [h, exp_add, turn, Complex.exp_int_mul_two_pi_mul_I, one_mul,
    exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem midpoint_eq_iff (L : ℂ) (k j : ℤ) :
    reading L k (3/2) = reading L j (3/2) ↔ k % 2 = j % 2 := by
  rw [reading_eq_iff]
  constructor
  · rintro ⟨m, hm⟩
    have hreal : 3 * ((k : ℝ) - j) = 2 * (m : ℝ) := by linarith
    have hint : 3 * (k - j) = 2 * m := by exact_mod_cast hreal
    omega
  · intro h
    use 3 * ((k-j)/2)
    have hint : k - j = 2 * ((k-j)/2) := by omega
    have hreal : (k : ℝ) - j = 2 * ((↑((k-j)/2) : ℝ)) := by exact_mod_cast hint
    push_cast
    linarith

theorem reading_norm (L : ℂ) (k : ℤ) (x : ℝ) :
    ‖reading L k x‖ = Real.exp (x * L.re) := by
  rw [reading, Complex.norm_exp]
  congr 1
  simp [turn, Complex.mul_re]

theorem radius_at_73 (L : ℂ) (hL : L.re = -Real.log 73) (k : ℤ) (x : ℝ) :
    ‖reading L k x‖ = (73 : ℝ)^(-x) := by
  rw [reading_norm, hL, Real.rpow_def_of_pos (by norm_num : 0 < (73 : ℝ))]
  congr 1
  ring

theorem exponent_from_radius (L : ℂ) (hL : L.re = -Real.log 73) (k : ℤ) (x : ℝ) :
    -Real.log ‖reading L k x‖ / Real.log 73 = x := by
  rw [radius_at_73 L hL, Real.log_rpow (by norm_num : 0 < (73 : ℝ))]
  field_simp [(Real.log_pos (by norm_num : 1 < (73 : ℝ))).ne']

theorem radius_between (L : ℂ) (hL : L.re = -Real.log 73) (k : ℤ) {x : ℝ}
    (h₁ : 1 < x) (h₂ : x < 2) :
    (73 : ℝ) ^ (-2 : ℤ) < ‖reading L k x‖ ∧ ‖reading L k x‖ < (73 : ℝ)⁻¹ := by
  rw [radius_at_73 L hL]
  have lower := Real.rpow_lt_rpow_of_exponent_lt (x := (73 : ℝ)) (by norm_num) (neg_lt_neg h₂)
  have upper := Real.rpow_lt_rpow_of_exponent_lt (x := (73 : ℝ)) (by norm_num) (neg_lt_neg h₁)
  constructor
  · convert lower using 1
    norm_num
  · convert upper using 1
    norm_num

end SuperZeta.FractionalTurnPower
