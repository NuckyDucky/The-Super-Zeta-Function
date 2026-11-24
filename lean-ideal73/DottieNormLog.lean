import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace QuarticModel

open Finset

private theorem divisionTicks (m b : ℕ) (hb : 0 < b) :
    ((m / b : ℕ) : ℝ) ≤ (m : ℝ) / b ∧
      (m : ℝ) / b ≤ ((m / b : ℕ) : ℝ) + 1 := by
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  refine ⟨(le_div_iff₀ hb').2 ?_, (div_le_iff₀ hb').2 ?_⟩
  · exact_mod_cast Nat.div_mul_le_self m b
  · rw [mul_comm]
    exact_mod_cast (Nat.lt_mul_div_succ m hb).le

/-- The Horner stages round both the coefficient and the product down. -/
private def logHornerTicks (numerator b aSq bSq : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | terms + 1, i =>
    logHornerTicks numerator b aSq bSq terms (i + 1) * aSq / bSq +
      numerator / (b * (2 * i + 1))

private noncomputable def logPartial (r : ℝ) (terms i : ℕ) : ℝ :=
  ∑ j ∈ range terms, r ^ (2 * j + 1) / (2 * (i : ℝ) + 2 * (j : ℝ) + 1)

private theorem logPartial_succ (r : ℝ) (terms i : ℕ) :
    logPartial r (terms + 1) i =
      logPartial r terms (i + 1) * r ^ 2 + r / (2 * (i : ℝ) + 1) := by
  unfold logPartial
  rw [sum_range_succ', sum_mul]
  simp only [Nat.cast_zero, mul_zero, add_zero, zero_add, pow_one]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 2 by omega, pow_add]
  push_cast
  ring

private theorem logHornerTicks_spec (scale a b : ℕ) (hb : 0 < b)
    (hr : (a : ℝ) / b ≤ 1 / 3) (terms i : ℕ) :
    let r : ℝ := (a : ℝ) / b
    let ticks := logHornerTicks (2 * scale * a) b (a ^ 2) (b ^ 2) terms i
    (ticks : ℝ) ≤ 2 * scale * logPartial r terms i ∧
      2 * scale * logPartial r terms i ≤ (ticks : ℝ) + 3 := by
  let r : ℝ := (a : ℝ) / b
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ^ 2 ≤ (1 : ℝ) / 9 := by
    calc
      r ^ 2 ≤ (1 / 3 : ℝ) ^ 2 := pow_le_pow_left₀ hr0 hr 2
      _ = 1 / 9 := by norm_num
  induction terms generalizing i with
  | zero => simp [logHornerTicks, logPartial]
  | succ terms ih =>
    let tail := logHornerTicks (2 * scale * a) b (a ^ 2) (b ^ 2) terms (i + 1)
    let roundProduct := tail * a ^ 2 / b ^ 2
    let roundCoeff := 2 * scale * a / (b * (2 * i + 1))
    have hProduct : (roundProduct : ℝ) ≤ (tail : ℝ) * r ^ 2 ∧
        (tail : ℝ) * r ^ 2 ≤ (roundProduct : ℝ) + 1 := by
      have h := divisionTicks (tail * a ^ 2) (b ^ 2) (by positivity)
      simpa only [roundProduct, r, Nat.cast_mul, Nat.cast_pow, div_pow, mul_div_assoc] using h
    have hCoeff : (roundCoeff : ℝ) ≤ 2 * scale * (r / (2 * (i : ℝ) + 1)) ∧
        2 * scale * (r / (2 * (i : ℝ) + 1)) ≤ (roundCoeff : ℝ) + 1 := by
      have h := divisionTicks (2 * scale * a) (b * (2 * i + 1)) (by positivity)
      simpa only [roundCoeff, r, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
        div_mul_eq_div_div, mul_div_assoc] using h
    have hTail := ih (i + 1)
    change (tail : ℝ) ≤ 2 * scale * logPartial r terms (i + 1) ∧
      2 * scale * logPartial r terms (i + 1) ≤ (tail : ℝ) + 3 at hTail
    have hLower := mul_le_mul_of_nonneg_right hTail.1 (sq_nonneg r)
    have hUpper := mul_le_mul_of_nonneg_right hTail.2 (sq_nonneg r)
    change ((roundProduct + roundCoeff : ℕ) : ℝ) ≤ 2 * scale * logPartial r (terms + 1) i ∧
      2 * scale * logPartial r (terms + 1) i ≤ ((roundProduct + roundCoeff : ℕ) : ℝ) + 3
    rw [logPartial_succ, Nat.cast_add]
    constructor
    · nlinarith only [hProduct.1, hCoeff.1, hLower]
    · nlinarith only [hProduct.2, hCoeff.2, hUpper, hr2]

/-- Lower fixed-point endpoint for `log ((1+r)/(1-r))`, where `r = a/b`. -/
def logAtanhLowerTicks (scale a b terms : ℕ) : ℕ :=
  logHornerTicks (2 * scale * a) b (a ^ 2) (b ^ 2) terms 0

/-- Three ticks cover Horner rounding. The remaining ticks cover the Taylor tail. -/
def logAtanhErrorTicks (scale terms : ℕ) : ℕ :=
  4 + (3 * scale) / (4 * 9 ^ terms)

private theorem logAtanh_tail_bound {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r ≤ 1 / 3) (terms : ℕ) :
    2 * (r ^ (2 * terms + 1) / (1 - r ^ 2)) ≤ 3 / (4 * 9 ^ terms) := by
  have hrSq := pow_le_pow_left₀ h₀ h₁ 2
  have hd : 0 < 1 - r ^ 2 := by nlinarith only [hrSq]
  have hden : 1 - (1 / 3 : ℝ) ^ 2 ≤ 1 - r ^ 2 := sub_le_sub_left hrSq 1
  have hnum := pow_le_pow_left₀ h₀ h₁ (2 * terms + 1)
  calc
    _ ≤ 2 * ((1 / 3 : ℝ) ^ (2 * terms + 1) / (1 - (1 / 3 : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        ((div_le_div_of_nonneg_right hnum hd.le).trans
          (div_le_div_of_nonneg_left (by positivity) (by norm_num) hden)) (by norm_num)
    _ = _ := by
      rw [pow_succ, pow_mul]
      norm_num [div_pow]
      field_simp; ring

/-- The certificate works directly with the exact integer ratio on `0 ≤ a/b ≤ 1/3`. -/
theorem logAtanhLowerTicks_spec (scale a b terms : ℕ) (hb : 0 < b) (hsmall : 3 * a ≤ b) :
    let r : ℝ := (a : ℝ) / b
    let ticks := logAtanhLowerTicks scale a b terms
    (ticks : ℝ) ≤ scale * Real.log ((1 + r) / (1 - r)) ∧
      scale * Real.log ((1 + r) / (1 - r)) ≤ (ticks : ℝ) + logAtanhErrorTicks scale terms := by
  let r : ℝ := (a : ℝ) / b
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 / 3 := by
    apply (div_le_iff₀ hb').2
    have h : (3 : ℝ) * a ≤ b := by exact_mod_cast hsmall
    linarith
  have hrLt : r < 1 := lt_of_le_of_lt hr1 (by norm_num)
  let value := Real.log ((1 + r) / (1 - r))
  let ticks := logAtanhLowerTicks scale a b terms
  have hRound : (ticks : ℝ) ≤ 2 * scale * logPartial r terms 0 ∧
      2 * scale * logPartial r terms 0 ≤ (ticks : ℝ) + 3 :=
    logHornerTicks_spec scale a b hb hr1 terms 0
  have hBelow : logPartial r terms 0 ≤ 1 / 2 * value := by
    simpa [logPartial, value] using Real.sum_range_le_log_div hr0 hrLt terms
  have hAbove : 1 / 2 * value ≤ logPartial r terms 0 + r ^ (2 * terms + 1) / (1 - r ^ 2) := by
    simpa [logPartial, value] using Real.log_div_le_sum_range_add hr0 hrLt terms
  have hScaledTail := mul_le_mul_of_nonneg_left (logAtanh_tail_bound hr0 hr1 terms)
    (Nat.cast_nonneg scale : 0 ≤ (scale : ℝ))
  have hFloor := (divisionTicks (3 * scale) (4 * 9 ^ terms) (by positivity)).2
  push_cast at hFloor
  have hTailCast : (scale : ℝ) * (3 / (4 * 9 ^ terms)) =
      (3 : ℝ) * scale / (4 * 9 ^ terms) := by ring
  rw [hTailCast] at hScaledTail
  change (ticks : ℝ) ≤ scale * value ∧ scale * value ≤ (ticks : ℝ) + logAtanhErrorTicks scale terms
  unfold logAtanhErrorTicks
  push_cast
  constructor
  · nlinarith only [hRound.1, mul_le_mul_of_nonneg_left hBelow (Nat.cast_nonneg scale)]
  · nlinarith only [hRound.2, hScaledTail, hFloor,
      mul_le_mul_of_nonneg_left hAbove (Nat.cast_nonneg scale)]

/-- Dyadically reduce an integer norm, then return its two fixed-point endpoints. -/
def normLogBounds (scale terms n : ℕ) : ℕ × ℕ :=
  let k := n.log2
  let b := 2 ^ k
  let lower := k * logAtanhLowerTicks scale 1 3 terms +
    logAtanhLowerTicks scale (n - b) (n + b) terms
  (lower, lower + (k + 1) * logAtanhErrorTicks scale terms)

theorem normLogBounds_spec (scale terms n : ℕ) (hs : 0 < scale) (hn : 0 < n) :
    ((normLogBounds scale terms n).1 : ℝ) / scale ≤ Real.log n ∧
      Real.log n ≤ ((normLogBounds scale terms n).2 : ℝ) / scale := by
  let k := n.log2
  let b := 2 ^ k
  have hb : 0 < b := by positivity
  have hb_le : b ≤ n := Nat.log2_self_le hn.ne'
  have hn_lt : n < 2 * b := by
    simpa [k, b, pow_succ, Nat.mul_comm] using (Nat.lt_log2_self (n := n))
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsum : 0 < n + b := Nat.add_pos_left hn b
  have hsmall : 3 * (n - b) ≤ n + b := by omega
  let r : ℝ := ((n - b : ℕ) : ℝ) / ((n + b : ℕ) : ℝ)
  have hrEq : r = ((n : ℝ) - b) / ((n : ℝ) + b) := by simp [r, Nat.cast_sub hb_le]
  have hRatio : (1 + r) / (1 - r) = (n : ℝ) / b := by
    rw [hrEq]
    have hden : (n : ℝ) + b ≠ 0 := (add_pos hn' hb').ne'
    have hpos : 0 < (1 : ℝ) - ((n : ℝ) - b) / ((n : ℝ) + b) := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ (add_pos hn' hb')).2
      linarith
    field_simp [hb'.ne', hden, hpos.ne']; ring
  have hLogB : Real.log (b : ℝ) = k * Real.log 2 := by
    simp [b, Real.log_pow]
  have hLog : Real.log n = k * Real.log 2 + Real.log ((1 + r) / (1 - r)) := by
    rw [hRatio, Real.log_div hn'.ne' hb'.ne', hLogB]
    ring
  let two := logAtanhLowerTicks scale 1 3 terms
  let reduced := logAtanhLowerTicks scale (n - b) (n + b) terms
  let error := logAtanhErrorTicks scale terms
  have hTwo : (two : ℝ) ≤ scale * Real.log 2 ∧ scale * Real.log 2 ≤ (two : ℝ) + error := by
    have he : ((1 + (1 : ℝ) / 3) / (1 - (1 : ℝ) / 3)) = 2 := by norm_num
    simpa only [two, error, Nat.cast_one, Nat.cast_ofNat, he] using
      logAtanhLowerTicks_spec scale 1 3 terms (by decide) (by decide)
  have hReduced : (reduced : ℝ) ≤ scale * Real.log ((1 + r) / (1 - r)) ∧
      scale * Real.log ((1 + r) / (1 - r)) ≤ (reduced : ℝ) + error :=
    logAtanhLowerTicks_spec scale (n - b) (n + b) terms hsum hsmall
  have hs' : 0 < (scale : ℝ) := by exact_mod_cast hs
  change ((k * two + reduced : ℕ) : ℝ) / scale ≤ Real.log n ∧
    Real.log n ≤ ((k * two + reduced + (k + 1) * error : ℕ) : ℝ) / scale
  rw [hLog]
  refine ⟨(div_le_iff₀ hs').2 ?_, (le_div_iff₀ hs').2 ?_⟩ <;> push_cast
  · nlinarith only [hReduced.1, mul_le_mul_of_nonneg_left hTwo.1 (Nat.cast_nonneg k)]
  · nlinarith only [hReduced.2, mul_le_mul_of_nonneg_left hTwo.2 (Nat.cast_nonneg k)]

theorem normLogBounds_width (scale terms n : ℕ) (hn : 0 < n) (hcap : n ≤ 2 ^ 29) :
    (normLogBounds scale terms n).2 - (normLogBounds scale terms n).1 ≤
      30 * logAtanhErrorTicks scale terms := by
  have h : n.log2 ≤ 29 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).1
      ((Nat.log2_self_le hn.ne').trans hcap)
  simp only [normLogBounds, Nat.add_sub_cancel_left]
  exact Nat.mul_le_mul_right _ (by omega)

#print axioms logAtanhLowerTicks_spec
#print axioms normLogBounds_spec
#print axioms normLogBounds_width

end QuarticModel
