import MellinFixedComplexPolynomial

/-! Evaluate the constant and linear terms at a point, and enclose the quadratic remainder. -/

namespace DottieOriented.NativeSpectrum.MellinFixed.ComplexBox

private def hornerValue (a : ℕ → ℂ) (z : ℂ) (start : ℕ) : ℕ → ℂ
  | 0 => 0
  | n + 1 => a start + z * hornerValue a z (start + 1) n

private theorem hornerValue_eq_sum (a : ℕ → ℂ) (z : ℂ) (start n : ℕ) :
    hornerValue a z start n = ∑ k ∈ Finset.range n, a (start + k) * z ^ k := by
  induction n generalizing start with
  | zero => simp [hornerValue]
  | succ n ih =>
    rw [hornerValue, ih, Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.add_zero, pow_zero, mul_one]
    rw [add_comm (a start)]
    refine congrArg (· + a start) (Finset.sum_congr rfl fun k _ ↦ ?_)
    rw [Nat.add_right_comm start 1 k, Nat.add_assoc, pow_succ]
    ring

private structure CenteredHornerBoxes where
  value : ComplexBox
  linear : ComplexBox
  remainder : ComplexBox

private def hornerDifference (center input : ComplexBox) (f : ℕ → ComplexBox) (start : ℕ) :
    ℕ → CenteredHornerBoxes
  | 0 => ⟨zero, zero, zero⟩
  | n + 1 =>
    let tail := hornerDifference center input f (start + 1) n
    ⟨add (f start) (mul center tail.value), add tail.value (mul center tail.linear),
      add tail.linear (mul input tail.remainder)⟩

private theorem hornerDifference_contains {c x : ℂ} {center input : ComplexBox}
    (hc : Contains center c) (hx : Contains input x)
    (f : ℕ → ComplexBox) (a : ℕ → ℂ) (ha : ∀ k, Contains (f k) (a k))
    (start n : ℕ) :
    let p := hornerDifference center input f start n
    Contains p.value (hornerValue a c start n) ∧
      ∃ d r : ℂ, Contains p.linear d ∧ Contains p.remainder r ∧
        hornerValue a x start n = hornerValue a c start n + (x - c) * d + (x - c) ^ 2 * r := by
  induction n generalizing start with
  | zero =>
    exact ⟨zero_contains, 0, 0, zero_contains, zero_contains, by simp [hornerValue]⟩
  | succ n ih =>
    obtain ⟨hcenter, d, r, hd, hr, he⟩ := ih (start + 1)
    refine ⟨add_contains (ha start) (mul_contains hc hcenter),
      hornerValue a c (start + 1) n + c * d, d + x * r,
      add_contains hcenter (mul_contains hc hd), add_contains hd (mul_contains hx hr), ?_⟩
    simp only [hornerValue]
    rw [he]
    ring

def centeredHorner (center offset : ComplexBox) (f : ℕ → ComplexBox) (n : ℕ) : ComplexBox :=
  let p := hornerDifference center (add center offset) f 0 n
  add (add p.value (mul offset p.linear)) (mul (mul offset offset) p.remainder)

theorem centeredHorner_contains {c z : ℂ} {center offset : ComplexBox}
    (hc : Contains center c) (hz : Contains offset z)
    (f : ℕ → ComplexBox) (a : ℕ → ℂ) (ha : ∀ k, Contains (f k) (a k)) (n : ℕ) :
    Contains (centeredHorner center offset f n) (∑ k ∈ Finset.range n, a k * (c + z) ^ k) := by
  obtain ⟨hp, d, r, hd, hr, he⟩ := hornerDifference_contains hc (add_contains hc hz) f a ha 0 n
  have h := add_contains (add_contains hp (mul_contains hz hd)) (mul_contains (mul_contains hz hz) hr)
  rw [show c + z - c = z by abel] at he
  rw [← pow_two] at h
  rw [← he, hornerValue_eq_sum] at h
  simpa only [centeredHorner, Nat.zero_add] using h

#print axioms centeredHorner_contains

end DottieOriented.NativeSpectrum.MellinFixed.ComplexBox
