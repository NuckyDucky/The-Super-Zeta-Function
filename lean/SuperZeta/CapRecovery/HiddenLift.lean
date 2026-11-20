import Mathlib.Algebra.Order.Round
import SuperZeta.CapRecovery.AxisReading
import SuperZeta.CapRecovery.SpectrumRatio

/-! Decoding an unknown resonant lift from the larger-to-smaller ratio
of the two absolute Cartesian components of the cap curvature. -/
noncomputable section

namespace SuperZeta.HiddenLift

open SignWords CapDominance Complex

private def realDigit : Sign → ℝ
  | .plus => 1
  | .minus => -1

private theorem abs_digit (s : Sign) : |realDigit s| = 1 := by
  cases s <;> norm_num [realDigit]

private theorem coords (y : ℝ) (s : Sign) (w : List Sign) :
    (value ((y : ℂ)*I) (s :: w)).re = realDigit s - y*(value ((y : ℂ)*I) w).im ∧
    (value ((y : ℂ)*I) (s :: w)).im = y*(value ((y : ℂ)*I) w).re := by
  cases s <;> simp [value, digit, realDigit, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]

private theorem signed_value_snoc (t : ℂ) (w : List Sign) (s : Sign) :
    value t (w ++ [s]) = value t w + t^w.length * digit s := by
  induction w with
  | nil => simp [value]
  | cons a w ih =>
    simp only [List.cons_append, value, ih, List.length_cons, pow_succ]
    ring

/-- Reversing the coefficients converts powers of the expanding base into
powers of its reciprocal. The factor t^length only rotates and scales the axes. -/
private theorem reciprocal_value {t : ℂ} (ht : t ≠ 0) (w : List Sign) :
    t * value t w = t^w.length * value t⁻¹ w.reverse := by
  induction w with
  | nil => simp [value]
  | cons s w ih =>
    simp only [value, List.length_cons, List.reverse_cons, signed_value_snoc,
      List.length_reverse, pow_succ]
    have hc : t^w.length * (t⁻¹)^w.length = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ ht, one_pow]
    linear_combination t * ih + (-t*digit s) * hc

private theorem reciprocal_bounds {y a : ℝ} (ha : 3 ≤ a) (hy : a * |y| = 1)
    (w : List Sign) :
    |(value ((y : ℂ)*I) w).re| ≤ a^2/(a^2-1) ∧
    |(value ((y : ℂ)*I) w).im| ≤ a/(a^2-1) := by
  have ha0 : 0 < a := by linarith
  have hd : 0 < a^2-1 := by nlinarith [sq_nonneg (a-3)]
  have hyy : |y| = 1/a := (eq_div_iff ha0.ne').mpr (by linarith [mul_comm a |y|])
  induction w with
  | nil => simp [value, (div_nonneg (sq_nonneg a) hd.le), (div_nonneg ha0.le hd.le)]
  | cons s w ih =>
    rw [(coords y s w).1, (coords y s w).2, abs_mul]
    constructor
    · calc |realDigit s - y * (value ((y:ℂ)*I) w).im| ≤
              |realDigit s| + |y * (value ((y:ℂ)*I) w).im| := abs_sub _ _
           _ ≤ 1 + |y| * (a/(a^2-1)) := by
              rw [abs_digit, abs_mul]
              gcongr
              exact ih.2
           _ = _ := by rw [hyy]; field_simp
    · calc |y| * |(value ((y:ℂ)*I) w).re| ≤ |y| * (a^2/(a^2-1)) :=
              mul_le_mul_of_nonneg_left ih.1 (abs_nonneg y)
           _ = _ := by rw [hyy]; field_simp; ring

private theorem leading_coordinate {y a : ℝ} (ha : 3 ≤ a) (hy : a * |y| = 1)
    (s : Sign) (w : List Sign) :
    abs (|(value ((y : ℂ)*I) (s::w)).re| - 1) ≤ 1/(a^2-1) := by
  nth_rw 1 [← abs_digit s]
  rw [(coords y s w).1]
  calc abs (|realDigit s - y * (value ((y : ℂ)*I) w).im| - |realDigit s|) ≤
          |(realDigit s - y * (value ((y : ℂ)*I) w).im) - realDigit s| :=
          abs_abs_sub_abs_le_abs_sub _ _
       _ = |y| * |(value ((y : ℂ)*I) w).im| := by
          rw [sub_right_comm, sub_self, zero_sub, abs_neg, abs_mul]
       _ ≤ |y| * (a/(a^2-1)) := mul_le_mul_of_nonneg_left
          (reciprocal_bounds ha hy w).2 (abs_nonneg _)
       _ = _ := by rw [← mul_div_assoc, mul_comm |y| a, hy]

/-- Both components of a reversed word are controlled by its leading two
digits. The real-component estimate is reused on the one-digit-shorter word. -/
private theorem reverse_window {a y : ℝ} (ha : 3 ≤ a) (hy : a * |y| = 1)
    (s u : Sign) (w : List Sign) :
    let z := value ((y : ℂ)*I) (s :: u :: w)
    0 < |z.im| ∧ |z.im| < |z.re| ∧ abs (|z.re| / |z.im| - a) < 1 := by
  dsimp only
  apply SpectrumRatio.norm_window ha (leading_coordinate ha hy s (u::w))
  rw [(coords y s (u::w)).2, abs_mul, ← mul_assoc, hy, one_mul]
  exact leading_coordinate ha hy u w

open Resonant

/-- The same rates, written with the opposite lift and all letters flipped,
give the same entire map. -/
theorem flip_lift_map (m : ℤ) (w : List Sign) :
    eval (lift (-m)) (w.map Sign.flip) = eval (lift m) w := by
  rw [complement]
  simp [Resonant.lift]

theorem flip_lift_curvature (m : ℤ) (w : List Sign) :
    curvature (-m) (w.map Sign.flip) = curvature m w := by
  simp only [curvature, flip_lift_map]

private theorem normalized_curvature {m : ℤ} (hm : m ≠ 0) (w : List Sign) :
    curvature m w = phase m * (base m ^ (prefixes w).length *
      value (base m)⁻¹ (prefixes w).reverse) := by
  have he : lift m = phase m * base m := by
    unfold base
    linear_combination -(lift m) * phase_sq m
  rw [curvature_eq, ← value_prefixes, he, mul_assoc, reciprocal_value (base_ne_zero hm)]

open AxisReading

private theorem estimate_long {m : ℤ} (hm : m ≠ 0) (w : List Sign) (hw : 2 ≤ w.length) :
    |estimate (curvature m w) - ‖base m‖| < 1 := by
  let y : ℝ := -((base m).im)⁻¹
  have hbas : (base m)⁻¹ = (y : ℂ) * I := by
    conv_lhs => rw [base_imag m]
    simp [y, mul_comm, Complex.inv_I]
  have ha := three_le_norm_base hm
  have hy : ‖base m‖ * |y| = 1 := by
    simp [y, abs_inv, abs_im_base, base_ne_zero hm]
  have len : 2 ≤ (prefixes w).reverse.length := by simpa [length_prefixes] using hw
  obtain ⟨s,t,d,hd⟩ : ∃ s t d, (prefixes w).reverse = s :: t :: d := by
    cases he : (prefixes w).reverse with
    | nil => simp [he] at len
    | cons s u =>
      cases u with
      | nil => simp [he] at len
      | cons t d => exact ⟨_, _, _, rfl⟩
  let z := value ((y : ℂ)*I) (s :: t :: d)
  obtain ⟨hp, ho, hb⟩ := reverse_window ha hy s t d
  change 0 < |z.im| at hp
  change |z.im| < |z.re| at ho
  have he : axisRatio (curvature m w) = |z.re| / |z.im| := by
    rw [normalized_curvature hm, axisRatio_scaled_reverse _ hm, hd, hbas]
    exact show axisRatio z = _ by simp [axisRatio, max_eq_left ho.le, min_eq_right ho.le]
  rw [estimate, if_neg (show axisRatio (curvature m w) ≠ 0 by
    rw [he]; exact (div_pos (lt_trans hp ho) hp).ne'), he]
  exact hb

private theorem estimate_singleton (m : ℤ) (s : Sign) :
    estimate (curvature m [s]) = ‖base m‖ := by
  rw [curvature_eq, polynomial_cons]
  simp only [DyadicCap.polynomial, List.length_nil, Finset.range_zero, Finset.sum_empty,
    mul_zero, add_zero, mul_one]
  cases s <;> simp only [DyadicWeights.letter, Complex.ofReal_one, Complex.ofReal_neg,
    mul_one, mul_neg, neg_mul]
  all_goals
    rw [estimate_axis (Or.inl (by simp [Resonant.lift, Complex.mul_re, Complex.mul_im]))]
    simp [norm_base, Resonant.lift, norm_mul, Complex.norm_intCast, abs_of_pos Real.pi_pos]

/-- The observable from K alone is always within one of |m|π. A single
letter gives the exact scale on the imaginary axis. -/
theorem estimate_window {m : ℤ} (hm : m ≠ 0) (w : List Sign) (hw : w ≠ []) :
    |estimate (curvature m w) - m.natAbs * Real.pi| < 1 := by
  rw [Int.cast_natAbs, Int.cast_abs, ← norm_base]
  cases w with
  | nil => exact (hw rfl).elim
  | cons s w =>
    cases w with
    | nil => rw [estimate_singleton]; norm_num
    | cons t d => exact estimate_long hm _ (by simp)

/-- Read the magnitude of the integer lift directly from the complex curvature. -/
def decodeMagnitude (k : ℂ) : ℤ := round (estimate k / Real.pi)

theorem decodeMagnitude_curvature {m : ℤ} (hm : m ≠ 0) (w : List Sign) (hw : w ≠ []) :
    decodeMagnitude (curvature m w) = m.natAbs := by
  obtain ⟨hl, hr⟩ := abs_lt.mp (estimate_window hm w hw)
  have lower : (m.natAbs : ℝ) - 1/2 < estimate (curvature m w) / Real.pi :=
    (lt_div_iff₀ Real.pi_pos).mpr (by nlinarith [Real.pi_gt_three])
  have upper : estimate (curvature m w) / Real.pi < (m.natAbs : ℝ) + 1/2 :=
    (div_lt_iff₀ Real.pi_pos).mpr (by nlinarith [Real.pi_gt_three])
  rw [decodeMagnitude, round_eq, Int.floor_eq_iff, Int.cast_natCast]
  constructor <;> linarith

/-- Two nonempty words with hidden nonzero integer lifts give the same
curvature exactly when their labels agree, up to simultaneous negation. -/
theorem curvature_eq_iff {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0)
    {u v : List Sign} (hu : u ≠ []) (hv : v ≠ []) :
    curvature m u = curvature n v ↔
      (n = m ∧ v = u) ∨ (n = -m ∧ v = u.map Sign.flip) := by
  constructor
  · intro h
    have hc := congrArg decodeMagnitude h.symm
    rw [decodeMagnitude_curvature hn _ hv, decodeMagnitude_curvature hm _ hu] at hc
    have habs : n.natAbs = m.natAbs := by exact_mod_cast hc
    rcases Int.natAbs_eq_natAbs_iff.mp habs with hnm | hnm
    · subst n
      exact Or.inl ⟨rfl, (curvature_injective hm h).symm⟩
    · subst n
      exact Or.inr ⟨rfl, curvature_injective hn (h.symm.trans (flip_lift_curvature m u).symm)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact (flip_lift_curvature _ _).symm

end SuperZeta.HiddenLift
