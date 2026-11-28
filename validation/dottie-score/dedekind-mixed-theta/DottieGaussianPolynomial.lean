import DottieRationalWeight
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.Nat.Sqrt

namespace FieldTarget

open Complex
open scoped BigOperators

/-- Evaluate Gaussian-integer coefficients listed from constant term upwards. -/
def gaussianPolynomialEval : List GaussianInt → ℂ → ℂ
  | [], _ => 0
  | a :: as, z => (a : ℂ) + z * gaussianPolynomialEval as z

def gaussianPolynomialAdd : List GaussianInt → List GaussianInt → List GaussianInt
  | [], b => b
  | a, [] => a
  | a :: as, b :: bs => (a + b) :: gaussianPolynomialAdd as bs

def gaussianPolynomialMul : List GaussianInt → List GaussianInt → List GaussianInt
  | [], _ => []
  | a :: as, bs =>
      gaussianPolynomialAdd (bs.map (a * ·)) (0 :: gaussianPolynomialMul as bs)

/-- Compute one product coefficient without constructing the full product. -/
def gaussianPolynomialProductCoeff : List GaussianInt → List GaussianInt → ℕ → GaussianInt
  | [], _, _ => 0
  | a :: _, b, 0 => a * b.getD 0 0
  | a :: as, b, k + 1 => a * b.getD (k + 1) 0 + gaussianPolynomialProductCoeff as b k

theorem gaussianPolynomialAdd_getD (a b : List GaussianInt) (k : ℕ) :
    (gaussianPolynomialAdd a b).getD k 0 = a.getD k 0 + b.getD k 0 := by
  induction a generalizing b k with
  | nil => simp [gaussianPolynomialAdd]
  | cons a as ih =>
      cases b with
      | nil => simp [gaussianPolynomialAdd]
      | cons b bs =>
          cases k with
          | zero => rfl
          | succ k => exact ih bs k

private theorem gaussianPolynomialMapMul_getD (a : GaussianInt) (b : List GaussianInt) (k : ℕ) :
    (b.map (a * ·)).getD k 0 = a * b.getD k 0 := by
  induction b generalizing k with
  | nil => simp
  | cons b bs ih =>
      cases k with
      | zero => rfl
      | succ k => exact ih k

theorem gaussianPolynomialMul_getD (a b : List GaussianInt) (k : ℕ) :
    (gaussianPolynomialMul a b).getD k 0 = gaussianPolynomialProductCoeff a b k := by
  induction a generalizing k with
  | nil => simp [gaussianPolynomialMul, gaussianPolynomialProductCoeff]
  | cons a as ih =>
      rw [gaussianPolynomialMul, gaussianPolynomialAdd_getD, gaussianPolynomialMapMul_getD]
      cases k with
      | zero => rw [List.getD_cons_zero, add_zero, gaussianPolynomialProductCoeff]
      | succ k => rw [List.getD_cons_succ, ih k, gaussianPolynomialProductCoeff]

theorem gaussianPolynomialAdd_length (a b : List GaussianInt) :
    (gaussianPolynomialAdd a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => simp [gaussianPolynomialAdd]
  | cons a as ih =>
      cases b with
      | nil => simp [gaussianPolynomialAdd]
      | cons b bs => simp only [gaussianPolynomialAdd, List.length_cons, ih]; omega

theorem gaussianPolynomialMul_length {a b : List GaussianInt} (ha : a ≠ []) (hb : b ≠ []) :
    (gaussianPolynomialMul a b).length = a.length + b.length - 1 := by
  have hb' : 0 < b.length := List.length_pos_iff.mpr hb
  induction a with
  | nil => exact (ha rfl).elim
  | cons a as ih =>
      simp only [gaussianPolynomialMul, gaussianPolynomialAdd_length, List.length_map, List.length_cons]
      cases as with
      | nil => simp only [gaussianPolynomialMul, List.length_nil]; omega
      | cons a' as' => rw [ih (List.cons_ne_nil _ _)]; omega

theorem gaussianPolynomialEval_add (a b : List GaussianInt) (z : ℂ) :
    gaussianPolynomialEval (gaussianPolynomialAdd a b) z =
      gaussianPolynomialEval a z + gaussianPolynomialEval b z := by
  induction a generalizing b with
  | nil => simp [gaussianPolynomialAdd, gaussianPolynomialEval]
  | cons x xs ih =>
      cases b with
      | nil => simp [gaussianPolynomialAdd, gaussianPolynomialEval]
      | cons y ys =>
          simp only [gaussianPolynomialAdd, gaussianPolynomialEval, GaussianInt.toComplex_add, ih]
          ring

private theorem gaussianPolynomialEval_map_mul (a : GaussianInt) (bs : List GaussianInt) (z : ℂ) :
    gaussianPolynomialEval (bs.map (a * ·)) z = (a : ℂ) * gaussianPolynomialEval bs z := by
  induction bs with
  | nil => simp [gaussianPolynomialEval]
  | cons b bs ih =>
      simp only [List.map_cons, gaussianPolynomialEval, GaussianInt.toComplex_mul, ih]
      ring

theorem gaussianPolynomialEval_mul (a b : List GaussianInt) (z : ℂ) :
    gaussianPolynomialEval (gaussianPolynomialMul a b) z =
      gaussianPolynomialEval a z * gaussianPolynomialEval b z := by
  induction a with
  | nil => simp [gaussianPolynomialMul, gaussianPolynomialEval]
  | cons x xs ih =>
      simp only [gaussianPolynomialMul, gaussianPolynomialEval_add, gaussianPolynomialEval_map_mul,
        gaussianPolynomialEval, GaussianInt.toComplex_zero, zero_add, ih]
      ring

theorem gaussianPolynomialEval_ofFn {n : ℕ} (a : Fin n → GaussianInt) (z : ℂ) :
    gaussianPolynomialEval (List.ofFn a) z = ∑ k : Fin n, (a k : ℂ) * z ^ (k : ℕ) := by
  induction n with
  | zero => simp [gaussianPolynomialEval]
  | succ n ih =>
      rw [List.ofFn_succ, gaussianPolynomialEval, ih, Fin.sum_univ_succ, Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
      congr 1
      exact Finset.sum_congr rfl fun k _ ↦ by ring

/-- Clear a single common denominator without changing the centered polynomial. -/
theorem dottieRationalWeight_eq_gaussianPolynomialEval {n : ℕ} (a : Fin n → GaussianInt)
    (den : ℕ) (c z : ℂ) :
    dottieRationalWeight c (fun k ↦ ((a k).re / (den : ℚ), (a k).im / (den : ℚ))) z =
      gaussianPolynomialEval (List.ofFn a) (z - c) / (den : ℂ) := by
  rw [dottieRationalWeight, gaussianPolynomialEval_ofFn, Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [GaussianInt.toComplex_def]
  push_cast
  ring

/-- An integer upper bound on the complex norm of a Gaussian integer. -/
def gaussianNormCeiling (a : GaussianInt) : ℕ := a.norm.natAbs.sqrt + 1

theorem norm_gaussianInt_toComplex_le (a : GaussianInt) : ‖(a : ℂ)‖ ≤ (gaussianNormCeiling a : ℝ) := by
  have hs : ((a.norm.natAbs : ℕ) : ℝ) < (gaussianNormCeiling a : ℝ)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' a.norm.natAbs
  rw [GaussianInt.natCast_natAbs_norm, GaussianInt.intCast_real_norm, Complex.normSq_eq_norm_sq] at hs
  exact (lt_of_pow_lt_pow_left₀ 2 (by positivity) hs).le

/-- A rational bound on the norm at every point of a centered closed disk. -/
def gaussianPolynomialNormBound : List GaussianInt → ℚ → ℚ
  | [], _ => 0
  | a :: as, r => (gaussianNormCeiling a : ℚ) + r * gaussianPolynomialNormBound as r

theorem norm_gaussianPolynomialEval_le (a : List GaussianInt) {z : ℂ} {r : ℚ}
    (hz : ‖z‖ ≤ (r : ℝ)) : ‖gaussianPolynomialEval a z‖ ≤ (gaussianPolynomialNormBound a r : ℝ) := by
  induction a with
  | nil => simp [gaussianPolynomialEval, gaussianPolynomialNormBound]
  | cons a as ih =>
      simp only [gaussianPolynomialEval, gaussianPolynomialNormBound, Rat.cast_add, Rat.cast_mul,
        Rat.cast_natCast]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      exact add_le_add (norm_gaussianInt_toComplex_le a)
        (mul_le_mul hz ih (norm_nonneg _) ((norm_nonneg z).trans hz))

/-- A uniform model error and a polynomial residual give a pointwise bound. -/
theorem dottie_weighted_reading_norm_le {F P W : ℂ} {C D E : ℝ}
    (hW : ‖W‖ ≤ C) (hD : ‖W * P + I‖ ≤ D) (hE : ‖F - P‖ ≤ E) :
    ‖W * F + I‖ ≤ D + C * E := by
  have hEq : W * F + I = (W * P + I) + W * (F - P) := by ring
  rw [hEq]
  refine (norm_add_le _ _).trans (add_le_add hD ?_)
  rw [norm_mul]
  exact mul_le_mul hW hE (norm_nonneg _) ((norm_nonneg W).trans hW)

#print axioms gaussianPolynomialEval_add
#print axioms gaussianPolynomialEval_mul
#print axioms gaussianPolynomialMul_getD
#print axioms dottieRationalWeight_eq_gaussianPolynomialEval
#print axioms norm_gaussianPolynomialEval_le
#print axioms dottie_weighted_reading_norm_le

end FieldTarget
