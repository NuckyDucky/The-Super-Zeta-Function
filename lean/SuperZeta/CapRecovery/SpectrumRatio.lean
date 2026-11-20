import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

/-! Reading a scale from the two absolute Cartesian components of a cap
derivative ratio. A common factor cancels in their quotient. -/
namespace SuperZeta.SpectrumRatio

/-- If the leading and next Cartesian components have the relative
geometric-tail bounds, their quotient reads the scale to within one. -/
theorem ratio_window {a d A B : ℝ} (ha : 3 ≤ a) (hd : 0 < d)
    (hA : |A - a * d| * (a^2 - 1) ≤ a*d)
    (hB : |B - d| * (a^2 - 1) ≤ d) :
    0 < B ∧ B < A ∧ |A / B - a| < 1 := by
  let s := a^2 - 1
  have hs : 0 < s := by dsimp [s]; nlinarith [sq_nonneg (a-3)]
  have hsep : 2*a < s-1 := by dsimp [s]; nlinarith [sq_nonneg (a-3)]
  have hal : -(a*d) ≤ (A-a*d)*s := by
    calc
      -(a*d) ≤ -(|A-a*d| * s) := neg_le_neg hA
      _ ≤ _ := by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le _) hs.le
  have hau : (A-a*d)*s ≤ a*d :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hs.le).trans hA
  have hbl : -d ≤ (B-d)*s := by
    calc
      -d ≤ -(|B-d| * s) := neg_le_neg hB
      _ ≤ _ := by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le _) hs.le
  have hbu : (B-d)*s ≤ d :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) hs.le).trans hB
  have ha0 : 0 ≤ a := by linarith
  have lower : 2*a*d < B*s := by
    have hx := mul_lt_mul_of_pos_right hsep hd
    nlinarith
  have bpos : 0 < B := by
    by_contra! hn
    have hbs := mul_nonpos_of_nonpos_of_nonneg hn hs.le
    nlinarith [mul_nonneg ha0 hd.le]
  have upper : (A-a*B)*s ≤ 2*a*d := by
    nlinarith [mul_le_mul_of_nonneg_left hbl ha0]
  have bottom : -(2*a*d) ≤ (A-a*B)*s := by
    nlinarith [mul_le_mul_of_nonneg_left hbu ha0]
  have hlt : A-a*B < B := (mul_lt_mul_right hs).mp (upper.trans_lt lower)
  have hgt : -B < A-a*B := by
    apply (mul_lt_mul_right hs).mp
    rw [neg_mul]
    exact (neg_lt_neg lower).trans_le bottom
  have order : B < A := by nlinarith [mul_le_mul_of_nonneg_right ha bpos.le]
  refine ⟨bpos, order, abs_lt.mpr ⟨?_, ?_⟩⟩
  · have h : a-1 < A/B := (lt_div_iff₀ bpos).mpr (by linarith)
    linarith
  · have h : A/B < a+1 := (div_lt_iff₀ bpos).mpr (by linarith)
    linarith

/-- Normalized components: the dominant one is close to 1 and the other
is close to the reciprocal scale. -/
theorem norm_window {a U V : ℝ} (ha : 3 ≤ a)
    (hu : |U-1| ≤ 1/(a^2-1)) (hv : |a*V-1| ≤ 1/(a^2-1)) :
    0 < V ∧ V < U ∧ |U/V-a| < 1 := by
  have ha0 : 0 < a := by linarith
  have hs : 0 < a^2-1 := by nlinarith [sq_nonneg (a-3)]
  have h := ratio_window (a := a) (d := 1) (A := a*U) (B := a*V) ha zero_lt_one
  have hu' := (le_div_iff₀ hs).mp hu
  have hv' := (le_div_iff₀ hs).mp hv
  have haU : |a*U - a*1| * (a^2-1) ≤ a*1 := by
    rw [← mul_sub, abs_mul, abs_of_pos ha0, mul_assoc]
    exact mul_le_mul_of_nonneg_left hu' ha0.le
  obtain ⟨hp, ho, hr⟩ := h haU (by simpa using hv')
  refine ⟨(mul_pos_iff_of_pos_left ha0).mp hp, (mul_lt_mul_left ha0).mp ho, ?_⟩
  simpa only [mul_div_mul_left _ _ ha0.ne'] using hr

/-- Two distinct nonnegative multiples of π are more than two units apart. -/
theorem unique_multiple {m k : ℕ} {r : ℝ}
    (hm : |r - m*Real.pi| < 1) (hk : |r - k*Real.pi| < 1) : m = k := by
  wlog hmk : m ≤ k generalizing m k
  · exact (this hk hm (by omega)).symm
  by_contra hne
  have hnk : m+1 ≤ k := by omega
  have hreal : (m:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast hnk
  have hgap := mul_le_mul_of_nonneg_right hreal Real.pi_pos.le
  have a := (abs_lt.mp hm).2
  have b := (abs_lt.mp hk).1
  linarith [Real.pi_gt_three]

end SuperZeta.SpectrumRatio
