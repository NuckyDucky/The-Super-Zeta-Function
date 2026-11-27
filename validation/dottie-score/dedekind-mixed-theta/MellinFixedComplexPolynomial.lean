import MellinFixedIntervalSound
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Directed complex polynomial enclosures using the existing real intervals. -/

namespace DottieOriented.NativeSpectrum.MellinFixed

open scoped BigOperators

/-- The two endpoints may be different rationals with a common denominator. -/
def rangeRatio (lo hi d : ℤ) : Box :=
  ⟨(fromRatio lo d).lo, (fromRatio hi d).hi⟩

theorem rangeRatio_contains {lo hi d : ℤ} (hd : 0 < d) {x : ℝ}
    (hlo : (lo : ℝ) / (d : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ) / (d : ℝ)) :
    Contains (rangeRatio lo hi d) x :=
  ⟨(ratio_contains lo hd).1.trans (mul_le_mul_of_nonneg_left hlo scale_pos.le),
    (mul_le_mul_of_nonneg_left hhi scale_pos.le).trans (ratio_contains hi hd).2⟩

theorem lt_of_box_lower {a : Box} {x margin : ℝ} (hx : Contains a x)
    (h : (scale : ℝ) * margin < (a.lo : ℝ)) : margin < x := by
  by_contra! h'
  linarith only [h, hx.1, mul_le_mul_of_nonneg_left h' scale_pos.le]

theorem lt_of_box_upper {a : Box} {x margin : ℝ} (hx : Contains a x)
    (h : (a.hi : ℝ) < (scale : ℝ) * margin) : x < margin := by
  by_contra! h'
  linarith only [h, hx.2, mul_le_mul_of_nonneg_left h' scale_pos.le]

structure ComplexBox where
  re : Box
  im : Box
  deriving DecidableEq, Repr

namespace ComplexBox

noncomputable section

def Contains (box : ComplexBox) (z : ℂ) : Prop :=
  MellinFixed.Contains box.re z.re ∧ MellinFixed.Contains box.im z.im

def real (a : Box) : ComplexBox := ⟨a, constant 0⟩

def zero : ComplexBox := real (constant 0)

def add (a b : ComplexBox) : ComplexBox :=
  ⟨MellinFixed.add a.re b.re, MellinFixed.add a.im b.im⟩

def mul (a b : ComplexBox) : ComplexBox :=
  ⟨sub (MellinFixed.mul a.re b.re) (MellinFixed.mul a.im b.im),
    MellinFixed.add (MellinFixed.mul a.re b.im) (MellinFixed.mul a.im b.re)⟩

def intMul (n : ℤ) (a : ComplexBox) : ComplexBox :=
  ⟨MellinFixed.mul (constant n) a.re, MellinFixed.mul (constant n) a.im⟩

theorem real_contains {a : Box} {x : ℝ} (hx : MellinFixed.Contains a x) :
    Contains (real a) (x : ℂ) :=
  ⟨by simpa only [real, Complex.ofReal_re] using hx,
    by simpa only [real, Complex.ofReal_im, Int.cast_zero] using constant_contains 0⟩

theorem zero_contains : Contains zero (0 : ℂ) := by
  simpa only [zero, Int.cast_zero, Complex.ofReal_zero] using real_contains (constant_contains 0)

theorem add_contains {a b : ComplexBox} {z w : ℂ} (hz : Contains a z) (hw : Contains b w) :
    Contains (add a b) (z + w) :=
  ⟨by simpa only [add, Complex.add_re] using MellinFixed.add_contains hz.1 hw.1,
    by simpa only [add, Complex.add_im] using MellinFixed.add_contains hz.2 hw.2⟩

theorem mul_contains {a b : ComplexBox} {z w : ℂ} (hz : Contains a z) (hw : Contains b w) :
    Contains (mul a b) (z * w) :=
  ⟨by simpa only [mul, Complex.mul_re] using
    sub_contains (MellinFixed.mul_contains hz.1 hw.1) (MellinFixed.mul_contains hz.2 hw.2),
    by simpa only [mul, Complex.mul_im] using
      MellinFixed.add_contains (MellinFixed.mul_contains hz.1 hw.2)
        (MellinFixed.mul_contains hz.2 hw.1)⟩

theorem intMul_contains (n : ℤ) {a : ComplexBox} {z : ℂ} (hz : Contains a z) :
    Contains (intMul n a) ((n : ℂ) * z) := by
  rw [← Complex.ofReal_intCast]
  exact ⟨by simpa only [intMul, Complex.re_ofReal_mul] using
    MellinFixed.mul_contains (constant_contains n) hz.1,
    by simpa only [intMul, Complex.im_ofReal_mul] using
      MellinFixed.mul_contains (constant_contains n) hz.2⟩

/-- Exact outward addition of a finite row of complex intervals. -/
def sumRange (f : ℕ → ComplexBox) : ℕ → ComplexBox
  | 0 => zero
  | n + 1 => add (sumRange f n) (f n)

theorem sumRange_contains (f : ℕ → ComplexBox) (c : ℕ → ℂ)
    {n : ℕ} (hc : ∀ k < n, Contains (f k) (c k)) :
    Contains (sumRange f n) (∑ k ∈ Finset.range n, c k) := by
  induction n with
  | zero => simpa only [sumRange, Finset.range_zero, Finset.sum_empty] using zero_contains
  | succ n ih =>
    rw [sumRange, Finset.sum_range_succ]
    exact add_contains (ih fun k hk ↦ hc k (hk.trans n.lt_succ_self)) (hc n n.lt_succ_self)

/-- Horner evaluation starts at the supplied coefficient, with powers starting at zero. -/
def horner (z : ComplexBox) (f : ℕ → ComplexBox) (start : ℕ) : ℕ → ComplexBox
  | 0 => zero
  | n + 1 => add (f start) (mul z (horner z f (start + 1) n))

theorem horner_contains {z : ℂ} {b : ComplexBox} (hz : Contains b z)
    (f : ℕ → ComplexBox) (c : ℕ → ℂ) (hc : ∀ k, Contains (f k) (c k)) (start n : ℕ) :
    Contains (horner b f start n) (∑ k ∈ Finset.range n, c (start + k) * z ^ k) := by
  induction n generalizing start with
  | zero => simpa only [horner, Finset.range_zero, Finset.sum_empty] using zero_contains
  | succ n ih =>
    have hs := add_contains (hc start) (mul_contains hz (ih (start + 1)))
    change Contains (add (f start) (mul b (horner b f (start + 1) n))) _
    convert hs using 1
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.add_zero, pow_zero, mul_one]
    rw [add_comm (c start)]
    refine congrArg (· + c start) (Finset.sum_congr rfl fun i _ ↦ ?_)
    rw [Nat.add_right_comm start 1 i, Nat.add_assoc, pow_succ]
    ring

/-- The coefficient of degree `k` after recentering. The factorial formula makes
the binomial coefficients efficient under kernel reduction as well as evaluation. -/
def shiftedCoefficient (f powers : ℕ → ComplexBox) (n k : ℕ) : ComplexBox :=
  sumRange (fun j ↦ if j < k then zero else
    intMul (Nat.fast_choose j k : ℤ) (mul (f j) (powers (j - k)))) n

theorem shiftedCoefficient_contains (f powers : ℕ → ComplexBox) (a : ℕ → ℂ) (c : ℂ)
    (ha : ∀ j, Contains (f j) (a j)) (hc : ∀ j, Contains (powers j) (c ^ j))
    (n k : ℕ) :
    Contains (shiftedCoefficient f powers n k)
      (∑ j ∈ Finset.range n, a j * c ^ (j - k) * (j.choose k : ℂ)) := by
  unfold shiftedCoefficient
  apply sumRange_contains
  intro j _
  by_cases h : j < k
  · simpa [h, Nat.choose_eq_zero_of_lt h] using zero_contains
  · simp only [h, ite_false, ← Nat.choose_eq_fast_choose]
    have hb := intMul_contains (j.choose k : ℤ) (mul_contains (ha j) (hc (j - k)))
    simpa only [Int.cast_natCast, mul_comm (j.choose k : ℂ)] using hb

private theorem shifted_sum_eq (a : ℕ → ℂ) (c z : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
      (∑ j ∈ Finset.range n, a j * c ^ (j - k) * (j.choose k : ℂ)) * z ^ k) =
        ∑ j ∈ Finset.range n, a j * (c + z) ^ j := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hsubset : Finset.range (j + 1) ⊆ Finset.range n := by
    intro k hk
    exact Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le
      (Nat.succ_le_iff.mpr (Finset.mem_range.mp hj)))
  calc
    _ = ∑ k ∈ Finset.range (j + 1), a j * c ^ (j - k) * (j.choose k : ℂ) * z ^ k := by
      symm
      apply Finset.sum_subset hsubset
      intro k _ hk
      have hlt : j < k := by have := Finset.mem_range.not.mp hk; omega
      simp only [Nat.choose_eq_zero_of_lt hlt, Nat.cast_zero, mul_zero, zero_mul]
    _ = _ := by
      rw [add_comm c z, add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- The polynomial value on the original input is enclosed by Horner evaluation
on the translated input and the recentered coefficients. -/
theorem shifted_horner_contains {z : ℂ} {box : ComplexBox} (hz : Contains box z)
    (f powers : ℕ → ComplexBox) (a : ℕ → ℂ) (c : ℂ)
    (ha : ∀ j, Contains (f j) (a j)) (hc : ∀ j, Contains (powers j) (c ^ j)) (n : ℕ) :
    Contains (horner box (shiftedCoefficient f powers n) 0 n)
      (∑ j ∈ Finset.range n, a j * (c + z) ^ j) := by
  have h := horner_contains hz (shiftedCoefficient f powers n)
    (fun k ↦ ∑ j ∈ Finset.range n, a j * c ^ (j - k) * (j.choose k : ℂ))
    (shiftedCoefficient_contains f powers a c ha hc n) 0 n
  simpa only [zero_add, shifted_sum_eq] using h

#print axioms rangeRatio_contains
#print axioms lt_of_box_lower
#print axioms lt_of_box_upper
#print axioms shifted_horner_contains

end

end ComplexBox

end DottieOriented.NativeSpectrum.MellinFixed

