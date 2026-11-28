import ContourGaussianDFT

namespace FieldTarget

open Complex
open scoped BigOperators

noncomputable section

/-- The numerator of the polynomial at z/d, with denominator d^length. -/
def gaussianScaledHorner (z : GaussianInt) (d : ℕ) : List GaussianInt → GaussianInt
  | [] => 0
  | a :: as => ((d ^ (as.length + 1) : ℕ) : GaussianInt) * a + z * gaussianScaledHorner z d as

theorem gaussianPolynomialEval_eq_scaledHorner (a : List GaussianInt) (z : GaussianInt) {d : ℕ}
    (hd : d ≠ 0) :
    gaussianPolynomialEval a (gaussianScaled z d) =
      gaussianScaled (gaussianScaledHorner z d a) (d ^ a.length) := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hCast (n : ℕ) : ((n : GaussianInt) : ℂ) = (n : ℂ) := map_natCast GaussianInt.toComplex n
  induction a with
  | nil => simp [gaussianPolynomialEval, gaussianScaledHorner, gaussianScaled]
  | cons a as ih =>
    rw [gaussianPolynomialEval, gaussianScaledHorner, ih, List.length_cons]
    simp only [gaussianScaled, GaussianInt.toComplex_add, GaussianInt.toComplex_mul, hCast]
    push_cast
    field_simp [pow_succ]
    ring

/-- A square-root-free norm bound for exact Gaussian numerators. -/
def gaussianL1 (a : GaussianInt) : ℕ := a.re.natAbs + a.im.natAbs

theorem norm_gaussianInt_le_l1 (a : GaussianInt) : ‖(a : ℂ)‖ ≤ (gaussianL1 a : ℝ) := by
  rw [GaussianInt.toComplex_def]
  refine (norm_add_le _ _).trans_eq ?_
  simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast, gaussianL1, Nat.cast_add,
    Nat.cast_natAbs, Int.cast_abs]

theorem norm_gaussianScaled_le_of_l1 {a : GaussianInt} {d p q : ℕ}
    (hd : 0 < d) (hq : 0 < q) (h : gaussianL1 a * q ≤ d * p) :
    ‖gaussianScaled a d‖ ≤ (p : ℝ) / q := by
  rw [gaussianScaled, norm_div, Complex.norm_natCast]
  refine (div_le_div_of_nonneg_right (norm_gaussianInt_le_l1 a) (Nat.cast_nonneg d)).trans ?_
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr hd) (Nat.cast_pos.mpr hq), mul_comm (p : ℝ)]
  exact_mod_cast h

private theorem norm_pow_sub_pow_le_on_unit_disk {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) (k : ℕ) :
    ‖z ^ k - w ^ k‖ ≤ (k : ℝ) * ‖z - w‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := pow_le_one₀ (n := k) (norm_nonneg z) hz
    rw [Nat.cast_succ, add_mul]
    calc
      _ = ‖z ^ k * (z - w) + w * (z ^ k - w ^ k)‖ := by
        rw [pow_succ, pow_succ]
        congr 1
        ring
      _ ≤ ‖z‖ ^ k * ‖z - w‖ + ‖w‖ * ‖z ^ k - w ^ k‖ := by
        simpa only [norm_mul, norm_pow] using norm_add_le (z ^ k * (z - w)) (w * (z ^ k - w ^ k))
      _ ≤ _ := by
        have h₁ := mul_le_of_le_one_left (norm_nonneg (z - w)) h
        have h₂ := (mul_le_of_le_one_left (norm_nonneg (z ^ k - w ^ k)) hw).trans ih
        linarith only [h₁, h₂]

theorem norm_polynomial_sub_le_on_unit_disk (a : ℕ → ℂ) (n : ℕ) {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖(∑ k ∈ Finset.range n, a k * z ^ k) - ∑ k ∈ Finset.range n, a k * w ^ k‖ ≤
      (∑ k ∈ Finset.range n, (k : ℝ) * ‖a k‖) * ‖z - w‖ := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
  rw [← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le_on_unit_disk hz hw k) (norm_nonneg _)).trans_eq
    (by ring)

#print axioms gaussianPolynomialEval_eq_scaledHorner
#print axioms norm_gaussianScaled_le_of_l1
#print axioms norm_polynomial_sub_le_on_unit_disk

end
end FieldTarget
