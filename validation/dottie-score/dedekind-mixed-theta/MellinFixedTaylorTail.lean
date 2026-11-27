import MellinFixedComplexPolynomial
import Mathlib.Algebra.BigOperators.Intervals

/-! Integer certificates for truncating a polynomial on a rational disk. -/

namespace DottieOriented.NativeSpectrum.MellinFixed

open scoped BigOperators

noncomputable section

private def endpointMass (b : Box) : ℤ := max |b.lo| |b.hi|

private theorem abs_le_endpointMass {b : Box} {x : ℝ} (h : Contains b x) :
    |x| ≤ (endpointMass b : ℝ) / (scale : ℝ) := by
  have hx : |(scale : ℝ) * x| ≤ (endpointMass b : ℝ) := by
    apply abs_le.mpr
    simp only [endpointMass, Int.cast_max, Int.cast_abs]
    exact ⟨(neg_le_neg (le_max_left |(b.lo : ℝ)| |(b.hi : ℝ)|)).trans
      ((neg_abs_le (b.lo : ℝ)).trans h.1),
      h.2.trans ((le_abs_self (b.hi : ℝ)).trans (le_max_right _ _))⟩
  rw [le_div_iff₀ scale_pos, mul_comm |x|]
  simpa only [abs_mul, abs_of_pos scale_pos] using hx

namespace ComplexBox

def coefficientMass (b : ComplexBox) : ℤ :=
  endpointMass b.re + endpointMass b.im

theorem norm_le_coefficientMass {b : ComplexBox} {a : ℂ} (h : Contains b a) :
    ‖a‖ ≤ (coefficientMass b : ℝ) / (scale : ℝ) := by
  refine (Complex.norm_le_abs_re_add_abs_im a).trans ?_
  rw [coefficientMass, Int.cast_add, add_div]
  exact add_le_add (abs_le_endpointMass h.1) (abs_le_endpointMass h.2)

/-- The cleared-denominator coefficient mass for the disk of radius `p/q`. -/
def weightedTailMass (box : ℕ → ComplexBox) (p q m n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Ico m n, coefficientMass (box k) * (p : ℤ) ^ k * (q : ℤ) ^ (n - k)

private theorem clear_radius_power (a p q : ℝ) (hq : 0 < q)
    {k n : ℕ} (hk : k ≤ n) :
    (a / (scale : ℝ)) * (p / q) ^ k =
      a * p ^ k * q ^ (n - k) / ((scale : ℝ) * q ^ n) := by
  have hkn : k + (n - k) = n := by omega
  have h₁ : q ^ n = q ^ k * q ^ (n - k) := by rw [← pow_add, hkn]
  rw [div_pow, h₁]
  field_simp [scale_pos.ne', hq.ne']

/-- A single integer inequality bounds all discarded complex terms at every
point of the rational disk. -/
theorem polynomial_tail_le_of_weighted_mass (box : ℕ → ComplexBox)
    (a : ℕ → ℂ) {p q m n : ℕ} {budget : ℤ} {z : ℂ}
    (hq : 0 < q) (hmn : m ≤ n) (hz : ‖z‖ ≤ (p : ℝ) / (q : ℝ))
    (ha : ∀ k ∈ Finset.Ico m n, Contains (box k) (a k))
    (hMass : weightedTailMass box p q m n ≤ budget * (q : ℤ) ^ n) :
    ‖(∑ k ∈ Finset.range n, a k * z ^ k) - (∑ k ∈ Finset.range m, a k * z ^ k)‖ ≤
      (budget : ℝ) / (scale : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [← Finset.sum_Ico_eq_sub _ hmn]
  calc
    _ ≤ ∑ k ∈ Finset.Ico m n, ‖a k * z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.Ico m n, (coefficientMass (box k) : ℝ) *
        (p : ℝ) ^ k * (q : ℝ) ^ (n - k) / ((scale : ℝ) * (q : ℝ) ^ n) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← clear_radius_power _ _ _ hqR (Finset.mem_Ico.mp hk).2.le, norm_mul, norm_pow]
      exact mul_le_mul (norm_le_coefficientMass (ha k hk)) (pow_le_pow_left₀ (norm_nonneg _) hz k)
        (pow_nonneg (norm_nonneg _) _) (le_trans (norm_nonneg _) (norm_le_coefficientMass (ha k hk)))
    _ = (weightedTailMass box p q m n : ℝ) / ((scale : ℝ) * (q : ℝ) ^ n) := by
      simp only [weightedTailMass, Int.cast_sum, Int.cast_mul, Int.cast_pow,
        Int.cast_natCast, div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ((budget : ℝ) * (q : ℝ) ^ n) / ((scale : ℝ) * (q : ℝ) ^ n) :=
      div_le_div_of_nonneg_right (by exact_mod_cast hMass) (mul_pos scale_pos (pow_pos hqR n)).le
    _ = _ := by field_simp [scale_pos.ne', hqR.ne']

#print axioms polynomial_tail_le_of_weighted_mass

end ComplexBox

end

end DottieOriented.NativeSpectrum.MellinFixed
