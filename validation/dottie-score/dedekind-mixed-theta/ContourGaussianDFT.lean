import ContourCircleSamples
import DottieGaussianPolynomial

namespace FieldTarget

open Complex
open scoped BigOperators

/-- A Gaussian integer read with one common denominator. -/
noncomputable def gaussianScaled (a : GaussianInt) (d : ℕ) : ℂ := (a : ℂ) / (d : ℂ)

theorem norm_gaussianScaled_le_of_nat_bound {a : GaussianInt} {d p q : ℕ}
    (hd : 0 < d) (hq : 0 < q) (h : gaussianNormCeiling a * q ≤ d * p) :
    ‖gaussianScaled a d‖ ≤ (p : ℝ) / q := by
  rw [gaussianScaled, norm_div, Complex.norm_natCast]
  refine (div_le_div_of_nonneg_right (norm_gaussianInt_toComplex_le a) (Nat.cast_nonneg d)).trans ?_
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr hd) (Nat.cast_pos.mpr hq), mul_comm (p : ℝ)]
  exact_mod_cast h

/-- An exact sum for one DFT coefficient, before division by the sample count. -/
def gaussianDFTSum (s phases : ℕ → GaussianInt) (N k : ℕ) : ℕ → GaussianInt
  | 0 => 0
  | j + 1 => gaussianDFTSum s phases N k j + s j * phases ((j * k) % N)

theorem coe_gaussianDFTSum (s phases : ℕ → GaussianInt) (N k n : ℕ) :
    (gaussianDFTSum s phases N k n : ℂ) =
      ∑ j ∈ Finset.range n, (s j : ℂ) * (phases ((j * k) % N) : ℂ) := by
  induction n with
  | zero => simp [gaussianDFTSum, GaussianInt.toComplex_zero]
  | succ n ih =>
      rw [gaussianDFTSum, GaussianInt.toComplex_add, GaussianInt.toComplex_mul, ih,
        Finset.sum_range_succ]

noncomputable def gaussianDFTCoeff (s phases : ℕ → GaussianInt) (N k ds dp : ℕ) : ℂ :=
  gaussianScaled (gaussianDFTSum s phases N k N) (N * ds * dp)

theorem gaussianDFTCoeff_eq_sum (s phases : ℕ → GaussianInt) (N k ds dp : ℕ) :
    gaussianDFTCoeff s phases N k ds dp =
      (∑ j ∈ Finset.range N, gaussianScaled (s j) ds *
        gaussianScaled (phases ((j * k) % N)) dp) / (N : ℂ) := by
  simp only [gaussianDFTCoeff, gaussianScaled, coe_gaussianDFTSum, Nat.cast_mul,
    div_mul_div_comm, ← Finset.sum_div]
  rw [div_div]
  congr 1
  ring

private theorem contour_phase_mod {ω : ℂ} {N : ℕ} (hω : ω ^ N = 1) (j k : ℕ) :
    ((ω ^ k)⁻¹) ^ j = (ω⁻¹) ^ ((j * k) % N) := by
  have hInv : (ω⁻¹) ^ N = 1 := by rw [inv_pow, hω, inv_one]
  calc
    _ = (ω⁻¹) ^ (j * k) := by rw [← inv_pow, ← pow_mul, Nat.mul_comm k j]
    _ = (ω⁻¹) ^ ((j * k) % N + N * ((j * k) / N)) := by rw [Nat.mod_add_div]
    _ = _ := by rw [pow_add, pow_mul, hInv, one_pow, mul_one]

/-- Every coefficient pays the same sample bound times the uniform phase error. -/
theorem norm_contourSampleCoeff_sub_gaussianDFT_le
    {ω : ℂ} {N k ds dp : ℕ} {C δ : ℝ} {s phases : ℕ → GaussianInt}
    (hN : 0 < N) (hω : ω ^ N = 1)
    (hS : ∀ j < N, ‖gaussianScaled (s j) ds‖ ≤ C)
    (hPhase : ∀ j < N, ‖(ω⁻¹) ^ j - gaussianScaled (phases j) dp‖ ≤ δ) :
    ‖contourSampleCoeff (fun j ↦ gaussianScaled (s j) ds) ω N k -
      gaussianDFTCoeff s phases N k ds dp‖ ≤ C * δ := by
  rw [contourSampleCoeff, gaussianDFTCoeff_eq_sum, ← sub_div, norm_div, Complex.norm_natCast,
    div_le_iff₀ (Nat.cast_pos.mpr hN), ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ j ∈ Finset.range N, C * δ := by
      refine Finset.sum_le_sum fun j hj ↦ ?_
      have hS' := hS j (Finset.mem_range.mp hj)
      rw [norm_mul, contour_phase_mod hω]
      exact mul_le_mul hS' (hPhase _ (Nat.mod_lt _ hN)) (norm_nonneg _)
        ((norm_nonneg _).trans hS')
    _ = _ := by simp [mul_comm]

theorem gaussianDFTCoeff_sub_scaled (s phases : ℕ → GaussianInt) {N k ds dp e : ℕ}
    (hn : N ≠ 0) (hs : ds ≠ 0) (hp : dp ≠ 0) (he : e ≠ 0) (a : GaussianInt) :
    gaussianDFTCoeff s phases N k ds dp - gaussianScaled a (ds * e) =
      gaussianScaled ((e : GaussianInt) * gaussianDFTSum s phases N k N -
        (N * dp : GaussianInt) * a) (N * ds * dp * e) := by
  simp only [gaussianDFTCoeff, gaussianScaled, map_sub, map_mul, map_natCast, Nat.cast_mul]
  field_simp [show (N : ℂ) ≠ 0 by exact_mod_cast hn, show (ds : ℂ) ≠ 0 by exact_mod_cast hs,
    show (dp : ℂ) ≠ 0 by exact_mod_cast hp, show (e : ℂ) ≠ 0 by exact_mod_cast he]

/-- Check the propagation using multiplication by the exact unit phase. -/
theorem norm_unitPowers_sub_le {u g : ℂ} {q : ℕ → ℂ} {N : ℕ} {B ε₀ ε₁ : ℝ}
    (hu : ‖u‖ = 1) (hq0 : q 0 = 1) (hg : ‖u - g‖ ≤ ε₀)
    (hSize : ∀ j < N, ‖q j‖ ≤ B)
    (hStep : ∀ j, j + 1 < N → ‖g * q j - q (j + 1)‖ ≤ ε₁) :
    ∀ j < N, ‖u ^ j - q j‖ ≤ (j : ℝ) * (B * ε₀ + ε₁) := by
  intro j
  induction j with
  | zero => simp [hq0]
  | succ j ih =>
      intro hj
      have hPrev := ih (by omega)
      have hSize' := hSize j (by omega)
      calc
        _ = ‖u * (u ^ j - q j) + (u - g) * q j + (g * q j - q (j + 1))‖ := by
          rw [pow_succ']
          congr 1
          ring
        _ ≤ ‖u * (u ^ j - q j)‖ + ‖(u - g) * q j‖ + ‖g * q j - q (j + 1)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ (j : ℝ) * (B * ε₀ + ε₁) + ε₀ * B + ε₁ := by
          simp only [norm_mul, hu, one_mul]
          exact add_le_add (add_le_add hPrev
            (mul_le_mul hg hSize' (norm_nonneg _) ((norm_nonneg _).trans hg))) (hStep j hj)
        _ = _ := by push_cast; ring

theorem gaussianScaled_mul_sub (g q next : GaussianInt) {d : ℕ} (hd : d ≠ 0) :
    gaussianScaled g d * gaussianScaled q d - gaussianScaled next d =
      gaussianScaled (g * q - (d : GaussianInt) * next) (d * d) := by
  simp only [gaussianScaled, map_sub, map_mul, map_natCast, Nat.cast_mul]
  field_simp [show (d : ℂ) ≠ 0 by exact_mod_cast hd]

#print axioms norm_gaussianScaled_le_of_nat_bound
#print axioms norm_contourSampleCoeff_sub_gaussianDFT_le
#print axioms gaussianDFTCoeff_sub_scaled
#print axioms norm_unitPowers_sub_le
#print axioms gaussianScaled_mul_sub

end FieldTarget
