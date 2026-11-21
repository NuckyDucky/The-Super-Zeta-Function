import SuperZeta.FractionalTurnPower
import SuperZeta.FractionalTurnWinding
import SuperZeta.FractionalTurnAt73
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.ModEq

/-! Which powers distinguish two logarithmic lifts, and when their paths meet. -/

namespace SuperZeta.FractionalTurn

open Complex FractionalTurnPower

private theorem ratio_turn_iff {p q j k : ℤ} (hq : q ≠ 0) (hred : Int.gcd q p = 1) :
    (∃ a : ℤ, ((p : ℝ) / q) * ((j : ℝ) - k) = (a : ℝ)) ↔ j ≡ k [ZMOD q] := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [Int.modEq_comm, Int.modEq_iff_dvd]
  constructor
  · rintro ⟨a, ha⟩
    have h : (p : ℝ) * ((j : ℝ) - k) = q * (a : ℝ) := by
      field_simp [hqr] at ha
      linarith
    have hz : p * (j - k) = q * a := by exact_mod_cast h
    exact Int.dvd_of_dvd_mul_right_of_gcd_one ⟨a, hz⟩ hred
  · rintro ⟨b, hb⟩
    refine ⟨p*b, ?_⟩
    have h : (j : ℝ) - k = (q : ℝ) * b := by exact_mod_cast hb
    rw [h]
    push_cast
    field_simp
    ring

/-- A fractional reading at a reduced exponent p/q identifies the turn count modulo q. -/
theorem reduced_rational_reading_eq_iff (L : ℂ) (j k p q : ℤ)
    (hq : 0 < q) (hred : Int.gcd q p = 1) :
    reading L j ((p : ℝ) / q) = reading L k ((p : ℝ) / q) ↔ j ≡ k [ZMOD q] := by
  rw [reading_eq_iff]
  exact ratio_turn_iff hq.ne' hred

/-- Different exponents have different radii when the original modulus is not 1. -/
theorem exponent_eq_of_reading_eq {L : ℂ} (hL : L.re ≠ 0) {j k : ℤ} {x y : ℝ}
    (h : reading L j x = reading L k y) : x = y := by
  have hn := congrArg (fun w : ℂ => ‖w‖) h
  change ‖reading L j x‖ = ‖reading L k y‖ at hn
  rw [reading_norm, reading_norm] at hn
  exact (mul_left_inj' hL).mp (Real.exp_strictMono.injective hn)

/-- The outgoing and returning arcs on neighboring sheets meet only at the endpoints
in the exponent interval [1,2]. The exponent on the other sheet may be any real number. -/
theorem adjacent_open_arcs_disjoint {L : ℂ} (hL : L.re ≠ 0) {j : ℤ} {x y : ℝ}
    (h₁ : 1 < x) (h₂ : x < 2) : reading L (j+1) x ≠ reading L j y := by
  intro he
  have hxy := exponent_eq_of_reading_eq hL he
  subst y
  obtain ⟨m, hm⟩ := (reading_eq_iff L (j+1) j x).mp he
  push_cast at hm
  have heq : x = (m : ℝ) := by linarith
  rw [heq] at h₁ h₂
  have ha : (1 : ℤ) < m := by exact_mod_cast h₁
  have hb : m < (2 : ℤ) := by exact_mod_cast h₂
  omega

/-- The normalized 3/2 reading is precisely the half-time exponential on the same lift. -/
theorem midpoint_is_half_reading (L : ℂ) (k : ℤ) :
    reading L k (3/2) / exp L = reading L k (1/2) := by
  rw [← reading_one L k, reading, reading, reading, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

/-- Two logarithms differing by the extra clockwise turn in the Dottie interpolation
give opposite half-lap multipliers, for every starting logarithm. -/
theorem clockwise_half_lap (L : ℂ) : reading L (-1) (1/2) = -reading L 0 (1/2) := by
  rw [← midpoint_is_half_reading, ← midpoint_is_half_reading,
      midpoint_div_start, midpoint_div_start]
  norm_num

/-- The actual path used for winding traces these same fractional readings in order. -/
theorem loop_is_reading (L : ℂ) (m : ℤ) (t : ℝ) :
    FractionalTurnWinding.loop L m t =
      if t ≤ 1 then reading L m (1+t) else reading L 0 (3-t) := by
  by_cases h : t ≤ 1 <;> simp [FractionalTurnWinding.loop, h, reading, turn]

open FractionalTurnAt73

private theorem heightLift_re : heightLift.re = -Real.log 73 := by
  rw [heightLift_explicit]
  simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_sub, sub_neg_eq_add]
  norm_num

/-- At the specified quarter-turn, the modulus of the plotted point decodes the exponent. -/
theorem exponent_at_quarter_turn (k : ℤ) (x : ℝ) :
    -Real.log ‖reading heightLift k x‖ / Real.log 73 = x :=
  exponent_from_radius heightLift heightLift_re k x

/-- In this example each pair of adjacent open arcs is disjoint, even at unequal exponents. -/
theorem quarter_turn_open_arcs_disjoint (j : ℤ) {x y : ℝ} (h₁ : 1 < x) (h₂ : x < 2) :
    reading heightLift (j+1) x ≠ reading heightLift j y := by
  apply adjacent_open_arcs_disjoint _ h₁ h₂
  rw [heightLift_re]
  exact neg_ne_zero.mpr (Real.log_pos (by norm_num)).ne'

/-- At 73 the actual two readings recover the opposite square roots of their common start,
while their degree has coefficient zero in the signed local power series. -/
theorem quarter_turn_recovery :
    reading heightLift 0 (3/2) / (-I/73) = primeVariable ∧
    reading heightLift 1 (3/2) / (-I/73) = -primeVariable ∧
    primeVariable ^ 2 = -I/73 ∧ primeVariable ^ 3 ≠ 0 ∧
    PowerSeries.coeff ℚ 3 localSeries = 0 := by
  obtain ⟨h₀, h₁⟩ := midpoint_recovers_root
  rw [heightLift_exp] at h₀ h₁
  exact ⟨by simpa [reading, turn] using h₀, by simpa [reading, turn] using h₁,
    heightLift_base_square.symm.trans heightLift_exp,
    midpoint_and_cubic_coefficient.2⟩

/-- A continuous logarithm proving winding +1 exists for these two specific arcs. -/
theorem quarter_turn_loop_winds_once :
    ∃ g : ℝ → ℂ, Continuous g ∧ (∀ t, exp (g t) = FractionalTurnWinding.loop heightLift 1 t) ∧
        ((g 2).im - (g 0).im) / (2*Real.pi) = 1 := by
  let g := FractionalTurnWinding.loopLog heightLift 1
  refine ⟨g, FractionalTurnWinding.continuous_loopLog ..,
    FractionalTurnWinding.exp_loopLog heightLift 1, ?_⟩
  simpa using FractionalTurnWinding.winding_eq heightLift 1 g
    (FractionalTurnWinding.continuous_loopLog ..).continuousOn (fun t _ =>
      FractionalTurnWinding.exp_loopLog heightLift 1 t)

end SuperZeta.FractionalTurn
