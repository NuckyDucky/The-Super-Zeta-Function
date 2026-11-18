import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The six-coefficient approximation to the target built from π.
The algebra applies to variable real inputs. The last theorem specializes the
two inputs to exp(1) and π and bounds the signed difference. -/

namespace SuperZeta.Meme

noncomputable section

def numerator (x : ℝ) : ℝ := 465 * x ^ 2 - 183 * x - 659
def denominator (x : ℝ) : ℝ := 155 * x ^ 2 + 396 * x - 936
def ratio (x : ℝ) : ℝ := numerator x / denominator x
def target (p : ℝ) : ℝ := ((p + 1) * (p + 2)) / (p ^ 2 + p - 1)

def quadratic (n d p : ℝ) : ℝ :=
  (n - d) * p ^ 2 + (n - 3 * d) * p - (n + 2 * d)

def discriminant (n d : ℝ) : ℝ := (n - d) ^ 2 + 4 * n ^ 2

theorem target_eq_ratio_iff (n d p : ℝ) (hd : d ≠ 0) (hp : p ^ 2 + p - 1 ≠ 0) :
    target p = n / d ↔ quadratic n d p = 0 := by
  unfold target quadratic
  rw [div_eq_div_iff hp hd]
  constructor <;> intro h <;> linear_combination -h

theorem completed_square (n d p : ℝ) :
    4 * (n - d) * quadratic n d p =
      (2 * (n - d) * p + (n - 3 * d)) ^ 2 - discriminant n d := by
  unfold quadratic discriminant
  ring

/-- The branch used for π-hat. -/
def plusRoot (n d : ℝ) : ℝ := (3 * d - n + Real.sqrt (discriminant n d)) / (2 * (n - d))

theorem plusRoot_is_root (n d : ℝ) (h : n - d ≠ 0) :
    quadratic n d (plusRoot n d) = 0 := by
  have hnorm : 0 ≤ discriminant n d := by unfold discriminant; positivity
  have hlinear : 2 * (n - d) * plusRoot n d + (n - 3 * d) = Real.sqrt (discriminant n d) := by
    unfold plusRoot
    field_simp [h]
    ring
  have hz : 4 * (n - d) * quadratic n d (plusRoot n d) = 0 := by
    rw [completed_square, hlinear, Real.sq_sqrt hnorm, sub_self]
  exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) h)

/-- The shift that yields the reciprocal recursion in the original calculation. -/
theorem translated_quadratic (n d p : ℝ) :
    4 * quadratic n d p =
      (n - d) * (2 * p + 3) ^ 2 - 4 * n * (2 * p + 3) - (n - d) := by
  unfold quadratic
  ring

theorem reciprocal_fixed_point (n d p : ℝ) (hnd : n - d ≠ 0)
    (hu : 2 * p + 3 ≠ 0) (hp : quadratic n d p = 0) :
    2 * p + 3 = 4 * n / (n - d) + 1 / (2 * p + 3) := by
  have ht := translated_quadratic n d p
  rw [hp, mul_zero] at ht
  field_simp [hnd, hu]
  linarith only [ht]

/-- The two inverse branches exchange by negative reciprocal in the shifted coordinate. -/
def partner (p : ℝ) : ℝ := -(3 * p + 5) / (2 * p + 3)

theorem partner_exchange (p : ℝ) (h : 2 * p + 3 ≠ 0) :
    (2 * p + 3) * (2 * partner p + 3) = -1 := by
  unfold partner
  field_simp [h]
  ring

theorem equal_target_iff (p q : ℝ) (hp : p ^ 2 + p - 1 ≠ 0) (hq : q ^ 2 + q - 1 ≠ 0) :
    target p = target q ↔ p = q ∨ (2 * p + 3) * (2 * q + 3) = -1 := by
  unfold target
  rw [div_eq_div_iff hp hq]
  have factorization :
      (p + 1) * (p + 2) * (q ^ 2 + q - 1) - (q + 1) * (q + 2) * (p ^ 2 + p - 1) =
        -(p - q) * (2 * p * q + 3 * p + 3 * q + 5) := by ring
  constructor
  · intro he
    rw [he, sub_self, eq_comm, mul_eq_zero] at factorization
    rcases factorization with h | h
    · exact Or.inl (by linarith only [h])
    · exact Or.inr (by linarith only [h])
  · rintro (he | he)
    · rw [he]
    · have hf : 2 * p * q + 3 * p + 3 * q + 5 = 0 := by linarith only [he]
      rw [hf, mul_zero] at factorization
      exact sub_eq_zero.mp factorization

theorem coefficient_quartic (x : ℝ) :
    discriminant (numerator x) (denominator x) =
      961000 * x ^ 4 - 1039740 * x ^ 3 - 1810543 * x ^ 2 + 644010 * x + 1813853 := by
  unfold discriminant numerator denominator
  ring

private theorem denominator_pos {x : ℝ} (hx : 5 / 2 ≤ x) : 0 < denominator x := by
  unfold denominator
  nlinarith [sq_nonneg (x - 5 / 2)]

private theorem ratio_increasing {x y : ℝ} (hx : 5 / 2 ≤ x) (hxy : x ≤ y) :
    ratio x ≤ ratio y := by
  have hy := hx.trans hxy
  have hk : 0 ≤ 212505 * x * y - 333095 * (x + y) + 432252 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  unfold ratio
  apply (div_le_div_iff₀ (denominator_pos hx) (denominator_pos hy)).2
  apply sub_nonneg.mp
  calc
    0 ≤ (y - x) * (212505 * x * y - 333095 * (x + y) + 432252) :=
      mul_nonneg (sub_nonneg.mpr hxy) hk
    _ = numerator y * denominator x - numerator x * denominator y := by
      unfold numerator denominator
      ring

private theorem target_decreasing {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    target y ≤ target x := by
  have hy := hx.trans hxy
  have hB (z : ℝ) (hz : 2 ≤ z) : 0 < z ^ 2 + z - 1 := by nlinarith [sq_nonneg z]
  have hx' : 0 ≤ x := by linarith
  have hy' : 0 ≤ y := by linarith
  unfold target
  apply (div_le_div_iff₀ (hB y hy) (hB x hx)).2
  apply sub_nonneg.mp
  calc
    0 ≤ (y - x) * (2 * x * y + 3 * (x + y) + 5) :=
      mul_nonneg (sub_nonneg.mpr hxy) (by positivity)
    _ = (x + 1) * (x + 2) * (y ^ 2 + y - 1) - (y + 1) * (y + 2) * (x ^ 2 + x - 1) := by ring

/-- An unconditional enclosure of the positive error, from rational
enclosures of exp(1) and π already proved in mathlib. -/
theorem signed_gap :
    2.37 / 10 ^ 20 < ratio (Real.exp 1) - target Real.pi ∧
      ratio (Real.exp 1) - target Real.pi < 2.91 / 10 ^ 20 := by
  let c : ℝ := 363916618873 / 133877442384
  let eLo := c - 1 / 10 ^ 20
  let eHi := c + 1 / 10 ^ 20
  let pLo : ℝ := 3.14159265358979323846
  let pHi : ℝ := 3.14159265358979323847
  have he := abs_le.mp Real.exp_one_near_20
  have heLo : eLo ≤ Real.exp 1 := by dsimp [eLo, c]; linarith only [he.1]
  have heHi : Real.exp 1 ≤ eHi := by dsimp [eHi, c]; linarith only [he.2]
  have hmin : 5 / 2 ≤ eLo := by norm_num [eLo, c]
  have hpMin : 2 ≤ pLo := by norm_num [pLo]
  have hpLo : pLo ≤ Real.pi := Real.pi_gt_d20.le
  have hpHi : Real.pi ≤ pHi := Real.pi_lt_d20.le
  have lo : 2.37 / 10 ^ 20 < ratio eLo - target pLo := by
    norm_num [ratio, numerator, denominator, target, eLo, c, pLo]
  have hi : ratio eHi - target pHi < 2.91 / 10 ^ 20 := by
    norm_num [ratio, numerator, denominator, target, eHi, c, pHi]
  exact ⟨lo.trans_le (sub_le_sub (ratio_increasing hmin heLo) (target_decreasing hpMin hpLo)),
    lt_of_le_of_lt (sub_le_sub (ratio_increasing (hmin.trans heLo) heHi)
      (target_decreasing (hpMin.trans hpLo) hpHi)) hi⟩

def piHat : ℝ := plusRoot (numerator (Real.exp 1)) (denominator (Real.exp 1))

theorem piHat_ne_pi : piHat ≠ Real.pi := by
  have hx : (5 : ℝ) / 2 ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hnd : numerator (Real.exp 1) - denominator (Real.exp 1) ≠ 0 := by
    apply ne_of_gt
    unfold numerator denominator
    nlinarith [sq_nonneg (Real.exp 1 - 5 / 2)]
  have hden : Real.pi ^ 2 + Real.pi - 1 ≠ 0 := by
    apply ne_of_gt
    linarith only [sq_nonneg Real.pi, Real.pi_gt_three]
  intro heq
  have hq := plusRoot_is_root _ _ hnd
  change quadratic _ _ piHat = 0 at hq
  rw [heq] at hq
  have h := (target_eq_ratio_iff _ _ _ (ne_of_gt (denominator_pos hx)) hden).2 hq
  change target Real.pi = ratio (Real.exp 1) at h
  have hgap := signed_gap.1
  rw [h, sub_self] at hgap
  norm_num at hgap

end

end SuperZeta.Meme
