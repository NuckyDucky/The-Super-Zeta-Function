import ContourTaylor
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace FieldTarget

open Complex Metric
open scoped BigOperators NNReal

noncomputable section

/-- The discrete Fourier coefficient computed from the numbered circle samples. -/
def contourSampleCoeff (samples : ℕ → ℂ) (ω : ℂ) (N k : ℕ) : ℂ :=
  (∑ j ∈ Finset.range N, samples j * ((ω ^ k)⁻¹) ^ j) / (N : ℂ)

/-- Evaluate the polynomial in the offset divided by the sampling radius. -/
def contourSamplePolynomial (samples : ℕ → ℂ) (ω : ℂ) (N n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, contourSampleCoeff samples ω N k * z ^ k

private theorem contourCircle_orthogonal {ω : ℂ} {N k l : ℕ}
    (hω : IsPrimitiveRoot ω N) (hk : k < N) (hl : l < N) :
    (∑ j ∈ Finset.range N, (ω ^ l / ω ^ k) ^ j) = if l = k then (N : ℂ) else 0 := by
  have hzero : ω ≠ 0 := hω.ne_zero (Nat.ne_of_gt ((Nat.zero_le k).trans_lt hk))
  by_cases h : l = k
  · subst l
    simp [div_self (pow_ne_zero k hzero)]
  · rw [ite_eq_right h]
    have hpower (i : ℕ) : (ω ^ i) ^ N = 1 := by
      rw [← pow_mul, Nat.mul_comm i N, pow_mul, hω.pow_eq_one, one_pow]
    have hroot : (ω ^ l / ω ^ k) ^ N = 1 := by
      rw [div_pow, hpower, hpower, div_one]
    have hne : ω ^ l / ω ^ k - 1 ≠ 0 := by
      intro he
      exact h (hω.pow_inj hl hk ((div_eq_one_iff_eq (pow_ne_zero k hzero)).mp (sub_eq_zero.mp he)))
    have hmul := geom_sum_mul (ω ^ l / ω ^ k) N
    rw [hroot, sub_self] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right hne

private theorem contourSampleCoeff_on_polynomial {ω : ℂ} {N k : ℕ}
    (hω : IsPrimitiveRoot ω N) (hk : k < N) (a : ℕ → ℂ) (h : ℂ) :
    contourSampleCoeff (fun j => ∑ l ∈ Finset.range N, a l * (h * ω ^ j) ^ l) ω N k =
      a k * h ^ k := by
  have hsum :
      (∑ j ∈ Finset.range N, (∑ l ∈ Finset.range N, a l * (h * ω ^ j) ^ l) * ((ω ^ k)⁻¹) ^ j) =
        ∑ l ∈ Finset.range N, (a l * h ^ l) * ∑ j ∈ Finset.range N, (ω ^ l / ω ^ k) ^ j := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hflip : (ω ^ j) ^ l = (ω ^ l) ^ j := by rw [← pow_mul, ← pow_mul, Nat.mul_comm j l]
    rw [mul_pow, hflip, div_eq_mul_inv, mul_pow]
    ring
  rw [contourSampleCoeff, hsum, Finset.sum_eq_single k]
  · rw [contourCircle_orthogonal hω hk hk, ite_eq_left rfl]
    exact mul_div_cancel_right₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ((Nat.zero_le k).trans_lt hk)))
  · intro l hl hlne
    rw [contourCircle_orthogonal hω hk (Finset.mem_range.mp hl), ite_eq_right hlne, mul_zero]
  · intro hmem
    exact False.elim (hmem (Finset.mem_range.mpr hk))

private theorem contourSampleCoeff_error_le {S T : ℕ → ℂ} {ω : ℂ} {N k : ℕ} {ε : ℝ}
    (hN : 0 < N) (hω : ‖ω‖ = 1) (hST : ∀ j < N, ‖S j - T j‖ ≤ ε) :
    ‖contourSampleCoeff S ω N k - contourSampleCoeff T ω N k‖ ≤ ε := by
  simp only [contourSampleCoeff, ← sub_div, ← Finset.sum_sub_distrib, ← sub_mul, norm_div, norm_natCast]
  apply (div_le_iff₀ (by exact_mod_cast hN : (0 : ℝ) < N)).mpr
  calc
    _ ≤ ∑ j ∈ Finset.range N, ‖(S j - T j) * ((ω ^ k)⁻¹) ^ j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range N, ε := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [norm_mul, norm_pow, norm_inv, hω, one_pow, inv_one, mul_one] using
        hST j (Finset.mem_range.mp hj)
    _ = ε * N := by simp [mul_comm]

/-- A reconstruction from `N` circle readings gives a uniform approximation
on the smaller disk. The two terms bound the target Taylor tail and the
perturbation of the Fourier coefficients, respectively. -/
theorem contourSamplePolynomial_error_le
    {F : ℂ → ℂ} {S : ℕ → ℂ} {c ω x : ℂ} {R : ℝ≥0} {h r M ε : ℝ} {N n : ℕ}
    (hF : DifferentiableOn ℂ F (closedBall c R))
    (hM : ∀ z ∈ sphere c R, ‖F z‖ ≤ M)
    (hN : 0 < N) (hn : n ≤ N) (hω : IsPrimitiveRoot ω N) (hunit : ‖ω‖ = 1)
    (hr : r < h) (hh : h < (R : ℝ)) (hx : ‖x‖ ≤ r)
    (hS : ∀ j < N, ‖S j - F (c + (h : ℂ) * ω ^ j)‖ ≤ ε) :
    ‖F (c + x) - contourSamplePolynomial S ω N n (x / (h : ℂ))‖ ≤
      M * (r / (R : ℝ)) ^ n / (1 - r / (R : ℝ)) +
        (ε + M * (h / (R : ℝ)) ^ N / (1 - h / (R : ℝ))) / (1 - r / h) := by
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hx
  have hh0 : 0 < h := hr0.trans_lt hr
  let a := contourTaylorCoeff F c R
  let T := fun j => ∑ l ∈ Finset.range N, a l * ((h : ℂ) * ω ^ j) ^ l
  let B := M * (h / (R : ℝ)) ^ N / (1 - h / (R : ℝ))
  have hData (j : ℕ) (hj : j < N) : ‖S j - T j‖ ≤ ε + B := by
    have hnode : ‖(h : ℂ) * ω ^ j‖ ≤ h := by
      simp [norm_pow, hunit, Complex.norm_real, abs_of_pos hh0]
    have ht := contourTaylor_tail_le hF hM hh hnode N
    calc
      _ ≤ ‖S j - F (c + (h : ℂ) * ω ^ j)‖ + ‖F (c + (h : ℂ) * ω ^ j) - T j‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add (hS j hj) ht
  have hB0 : 0 ≤ ε + B := (norm_nonneg _).trans (hData 0 hN)
  let P := ∑ k ∈ Finset.range n, a k * x ^ k
  let z := x / (h : ℂ)
  have hz : ‖z‖ ≤ r / h := by
    dsimp [z]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
    exact div_le_div_of_nonneg_right hx hh0.le
  have hratio0 : 0 ≤ r / h := div_nonneg hr0 hh0.le
  have hratio1 : r / h < 1 := (div_lt_one hh0).mpr hr
  have hsum : (∑ k ∈ Finset.range n, (r / h) ^ k) ≤ (1 - r / h)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hratio0 hratio1]
    exact (summable_geometric_of_lt_one hratio0 hratio1).sum_le_tsum _ (fun k _ => pow_nonneg hratio0 k)
  have hcancel (k : ℕ) : (a k * (h : ℂ) ^ k) * z ^ k = a k * x ^ k := by
    rw [mul_assoc, ← mul_pow, show (h : ℂ) * z = x by
      dsimp [z]
      rw [mul_comm (h : ℂ), div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hh0.ne')]]
  have hpoly :
      P - contourSamplePolynomial S ω N n z =
        ∑ k ∈ Finset.range n, (a k * (h : ℂ) ^ k - contourSampleCoeff S ω N k) * z ^ k := by
    simp only [P, contourSamplePolynomial, sub_mul, Finset.sum_sub_distrib, hcancel]
  have hpolyError : ‖P - contourSamplePolynomial S ω N n z‖ ≤ (ε + B) / (1 - r / h) := by
    rw [hpoly]
    calc
      _ ≤ ∑ k ∈ Finset.range n, ‖(a k * (h : ℂ) ^ k - contourSampleCoeff S ω N k) * z ^ k‖ :=
        norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range n, (ε + B) * (r / h) ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN := (Finset.mem_range.mp hk).trans_le hn
        have hform : contourSampleCoeff T ω N k = a k * (h : ℂ) ^ k :=
          contourSampleCoeff_on_polynomial hω hkN a (h : ℂ)
        have hc := contourSampleCoeff_error_le (k := k) hN hunit hData
        rw [hform] at hc
        rw [norm_mul, norm_pow, norm_sub_rev]
        gcongr
      _ ≤ _ := by
        rw [← Finset.mul_sum, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left hsum hB0
  calc
    _ ≤ ‖F (c + x) - P‖ + ‖P - contourSamplePolynomial S ω N n z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (contourTaylor_tail_le hF hM (hr.trans hh) hx n) hpolyError

#print axioms contourSamplePolynomial_error_le

end

end FieldTarget
