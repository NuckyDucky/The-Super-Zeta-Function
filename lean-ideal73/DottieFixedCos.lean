import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
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

private def cosStep (i : ℕ) : ℕ := (2 * i + 1) * (2 * i + 2)

/-- The normalized cosine polynomial has constant term one at every stage.
Only the product subtracted from that constant needs rounding. -/
private def cosHornerTicks (scale aSq bSq : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | terms + 1, i =>
    scale - cosHornerTicks scale aSq bSq terms (i + 1) * aSq / (bSq * cosStep i)

private theorem cosHornerTicks_le (scale aSq bSq terms i : ℕ) :
    cosHornerTicks scale aSq bSq terms i ≤ scale := by
  cases terms
  · simp [cosHornerTicks]
  · exact Nat.sub_le _ _

private noncomputable def cosPartial (r : ℝ) (terms i : ℕ) : ℝ :=
  ∑ j ∈ range terms,
    (-1 : ℝ)^j * r^(2 * j) * ((2 * i).factorial : ℝ) / ((2 * (i + j)).factorial : ℝ)

private theorem cosPartial_succ (r : ℝ) (terms i : ℕ) :
    cosPartial r (terms + 1) i =
      1 - cosPartial r terms (i + 1) * (r ^ 2 / (cosStep i : ℝ)) := by
  have hfac : (2 * (i + 1)).factorial = cosStep i * (2 * i).factorial := by
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by omega, Nat.factorial_succ, Nat.factorial_succ]
    unfold cosStep
    ring
  unfold cosPartial
  rw [sum_range_succ', sum_mul, sub_eq_add_neg, add_comm (1 : ℝ), ← sum_neg_distrib]
  simp only [Nat.add_zero, pow_zero, Nat.mul_zero, one_mul,
    div_self (show ((2 * i).factorial : ℝ) ≠ 0 by positivity)]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [show i + (j + 1) = (i + 1) + j by omega,
    show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, pow_succ (-1 : ℝ), hfac]
  push_cast
  have h : (cosStep i : ℝ) ≠ 0 := by unfold cosStep; positivity
  field_simp [h]; ring

private theorem cosHornerTicks_spec (scale a b : ℕ) (hb : 0 < b)
    (hab : a ≤ b) (terms i : ℕ) :
    let r : ℝ := (a : ℝ) / b
    |scale * cosPartial r terms i - (cosHornerTicks scale (a ^ 2) (b ^ 2) terms i : ℝ)| ≤ 2 := by
  let r : ℝ := (a : ℝ) / b
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := (div_le_one hb').2 (by exact_mod_cast hab)
  have hrSq : r ^ 2 ≤ 1 := pow_le_one₀ hr0 hr1
  induction terms generalizing i with
  | zero => simp [cosHornerTicks, cosPartial]
  | succ terms ih =>
    let tail := cosHornerTicks scale (a ^ 2) (b ^ 2) terms (i + 1)
    let rounded := tail * a ^ 2 / (b ^ 2 * cosStep i)
    let q := r ^ 2 / (cosStep i : ℝ)
    have hStep : (2 : ℝ) ≤ (cosStep i : ℝ) := by
      unfold cosStep
      push_cast
      nlinarith only [Nat.cast_nonneg (α := ℝ) i, sq_nonneg (i : ℝ)]
    have hq0 : 0 ≤ q := by positivity
    have hq : q ≤ 1 / 2 := by
      exact (div_le_div_of_nonneg_right hrSq (by positivity)).trans
        (one_div_le_one_div_of_le (by norm_num) hStep)
    have hDivision : (rounded : ℝ) ≤ (tail : ℝ) * q ∧
        (tail : ℝ) * q ≤ (rounded : ℝ) + 1 := by
      have h := divisionTicks (tail * a ^ 2) (b ^ 2 * cosStep i) (by unfold cosStep; positivity)
      simpa only [rounded, q, r, Nat.cast_mul, Nat.cast_pow, div_pow, div_mul_eq_div_div,
        mul_div_assoc] using h
    have hRounded : rounded ≤ scale := by
      have h : (tail : ℝ) ≤ (scale : ℝ) := by
        exact_mod_cast cosHornerTicks_le scale (a ^ 2) (b ^ 2) terms (i + 1)
      have hh : (rounded : ℝ) ≤ scale := calc
        _ ≤ (tail : ℝ) * q := hDivision.1
        _ ≤ (tail : ℝ) * 1 := mul_le_mul_of_nonneg_left
          (hq.trans (by norm_num)) (Nat.cast_nonneg tail)
        _ ≤ scale := by simpa using h
      exact_mod_cast hh
    have hTail := ih (i + 1)
    change |scale * cosPartial r terms (i + 1) - (tail : ℝ)| ≤ 2 at hTail
    have hlo := mul_le_mul_of_nonneg_right (abs_le.mp hTail).1 hq0
    have hhi := mul_le_mul_of_nonneg_right (abs_le.mp hTail).2 hq0
    change |scale * cosPartial r (terms + 1) i - ((scale - rounded : ℕ) : ℝ)| ≤ 2
    rw [cosPartial_succ, Nat.cast_sub hRounded]
    change |scale * (1 - cosPartial r terms (i + 1) * q) - (scale - (rounded : ℝ))| ≤ 2
    exact abs_le.mpr ⟨by nlinarith only [hhi, hDivision.2, hq],
      by nlinarith only [hlo, hDivision.1, hq]⟩

private theorem cosPartial_error {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (terms : ℕ) :
    |Real.cos r - cosPartial r terms 0| ≤ 1 / ((2 * terms).factorial : ℝ) := by
  let f (j : ℕ) := r ^ (2 * j) / ((2 * j).factorial : ℝ)
  have hAnti : Antitone f := by
    intro i j hij
    have hIndex := Nat.mul_le_mul_left 2 hij
    have hPow := pow_le_pow_of_le_one hr0 hr1 hIndex
    have hDen : ((2 * i).factorial : ℝ) ≤ ((2 * j).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le hIndex
    calc
      f j ≤ r ^ (2 * i) / ((2 * j).factorial : ℝ) :=
        div_le_div_of_nonneg_right hPow (by positivity)
      _ ≤ f i := div_le_div_of_nonneg_left (by positivity) (by positivity) hDen
  have hSum : Summable f := by
    have hEven := (NormedSpace.expSeries_summable' (𝕂 := ℝ) r).comp_injective
      (show Function.Injective (fun j : ℕ => 2 * j) from fun i j h => by
        change 2 * i = 2 * j at h
        omega)
    simpa [f, Function.comp_def, smul_eq_mul, div_eq_mul_inv, mul_comm] using hEven
  have h := alternating_series_error_bound f hAnti hSum terms
  calc
    _ ≤ f terms := by
      rw [Real.cos_eq_tsum]
      simpa [f, cosPartial, mul_div_assoc] using h
    _ ≤ _ := div_le_div_of_nonneg_right (pow_le_one₀ hr0 hr1) (by positivity)

/-- The returned endpoints are integers in units of `1 / 2^48`. -/
def fixedCosScale : ℕ := 2 ^ 48

/-- Cosine enclosure for the exact signed rational `numerator / denominator`. -/
def fixedCosBounds (numerator : ℤ) (denominator : ℕ) : ℤ × ℤ :=
  let ticks := cosHornerTicks fixedCosScale (numerator.natAbs ^ 2) (denominator ^ 2) 9 0
  ((ticks : ℤ) - 3, (ticks : ℤ) + 3)

theorem fixedCosBounds_spec (numerator : ℤ) (denominator : ℕ) (hb : 0 < denominator)
    (hab : numerator.natAbs ≤ denominator) :
    ((fixedCosBounds numerator denominator).1 : ℝ) / fixedCosScale ≤
        Real.cos ((numerator : ℝ) / denominator) ∧
      Real.cos ((numerator : ℝ) / denominator) ≤
        ((fixedCosBounds numerator denominator).2 : ℝ) / fixedCosScale := by
  let a := numerator.natAbs
  let b := denominator
  let r : ℝ := (a : ℝ) / b
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := (div_le_one hb').2 (by exact_mod_cast hab)
  have hAbs : |(numerator : ℝ) / b| = r := by
    have hNatAbs : (a : ℝ) = |(numerator : ℝ)| := by
      change (numerator.natAbs : ℝ) = _
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    rw [abs_div, abs_of_nonneg hb'.le, ← hNatAbs]
  have hCos : Real.cos r = Real.cos ((numerator : ℝ) / denominator) := by
    rw [← hAbs, Real.cos_abs]
  let ticks := cosHornerTicks fixedCosScale (a ^ 2) (b ^ 2) 9 0
  have hRounded : |fixedCosScale * cosPartial r 9 0 - (ticks : ℝ)| ≤ 2 :=
    cosHornerTicks_spec fixedCosScale a b hb hab 9 0
  have hTaylor := cosPartial_error hr0 hr1 9
  have hTaylorTicks : (fixedCosScale : ℝ) * (1 / ((2 * 9 : ℕ).factorial : ℝ)) ≤ 1 := by
    norm_num [fixedCosScale, Nat.factorial]
  have hTail := mul_le_mul_of_nonneg_left hTaylor (Nat.cast_nonneg fixedCosScale)
  have hTailAbs : |fixedCosScale * Real.cos r - fixedCosScale * cosPartial r 9 0| ≤ 1 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg fixedCosScale)]
    exact hTail.trans hTaylorTicks
  have h := abs_le.mp hTailAbs
  have hd : 0 < (fixedCosScale : ℝ) := by norm_num [fixedCosScale]
  rw [← hCos]
  change (((ticks : ℤ) - 3 : ℤ) : ℝ) / fixedCosScale ≤ Real.cos r ∧
    Real.cos r ≤ (((ticks : ℤ) + 3 : ℤ) : ℝ) / fixedCosScale
  push_cast
  exact ⟨(div_le_iff₀ hd).2 (by linarith only [h.1, (abs_le.mp hRounded).1]),
    (le_div_iff₀ hd).2 (by linarith only [h.2, (abs_le.mp hRounded).2])⟩

theorem fixedCosBounds_width (numerator : ℤ) (denominator : ℕ) :
    ((fixedCosBounds numerator denominator).2 : ℝ) / fixedCosScale -
        ((fixedCosBounds numerator denominator).1 : ℝ) / fixedCosScale = 6 / 2 ^ 48 := by
  simp only [fixedCosBounds, Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat,
    ← sub_div, fixedCosScale, Nat.cast_pow, Nat.cast_ofNat]
  ring

#print axioms fixedCosBounds_spec
#print axioms fixedCosBounds_width

end QuarticModel
