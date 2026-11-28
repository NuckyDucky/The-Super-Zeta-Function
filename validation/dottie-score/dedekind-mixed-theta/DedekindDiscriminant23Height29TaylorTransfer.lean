import DedekindDiscriminant23Height29TaylorData
import DedekindDiscriminant23Height29QuadratureCertificate
import Discriminant23ClassMellinCentered

namespace FieldTarget

open Complex Metric SuperZeta.StirlingCorrection

noncomputable section

local notation "c29" => discriminant23Height29TaylorCenter

private def height29Offset (j : ℕ) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) * discriminant23Height29Root ^ j

private theorem height29_reading_point_eq (j : ℕ) :
    discriminant23Height29ReadingPoint j = c29 + height29Offset j := by
  rw [discriminant23Height29ReadingPoint, discriminant23_height29_dottie_geometry.1]
  rfl

private theorem height29_offset_norm (j : ℕ) : ‖height29Offset j‖ = 1 / 2 := by
  rw [height29Offset, norm_mul, norm_pow, discriminant23_height29_root_primitive.norm'_eq_one (by norm_num),
    one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
  norm_num

private theorem height29_offset_rounding {j : ℕ} (hj : j < 128) :
    ‖height29Offset j - height29RoundedOffset j‖ ≤ (1 / 2) * (1 / 10 ^ 24) := by
  let r := contourRoot128
  let q := gaussianScaled (contourRoot128PhaseNumerator j) contourRoot128Scale
  have hNorm : ‖r‖ = 1 := contourRoot128_isPrimitive.norm'_eq_one (by norm_num)
  have hInv : r⁻¹ = (starRingEnd ℂ) r := by
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hNorm, one_pow, inv_one, Complex.ofReal_one, mul_one]
  have hRounded : height29RoundedOffset j = (1 / 2 : ℂ) * (starRingEnd ℂ) q := by
    unfold height29RoundedOffset height29RoundedOffsetDenominator height29RoundedOffsetNumerator q gaussianScaled
    simp only [GaussianInt.toComplex_star, map_div₀, map_natCast, Nat.cast_mul, Nat.cast_ofNat]
    have hDen : (contourRoot128Scale : ℂ) ≠ 0 := by norm_num [contourRoot128Scale]
    field_simp
  have hEq : height29Offset j - height29RoundedOffset j =
      (1 / 2 : ℂ) * (starRingEnd ℂ) ((r⁻¹) ^ j - q) := by
    rw [hRounded, map_sub, map_pow, hInv, Complex.conj_conj]
    change ((1 / 2 : ℝ) : ℂ) * r ^ j - (1 / 2 : ℂ) * (starRingEnd ℂ) q = _
    push_cast
    ring
  rw [hEq, norm_mul, Complex.norm_conj, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num [norm_div]]
  exact mul_le_mul_of_nonneg_left (contourRoot128_phase_error j hj) (by norm_num)

private theorem height29_rounded_offset_norm {j : ℕ} (hj : j < 128) :
    ‖height29RoundedOffset j‖ ≤ 1 := by
  have h := norm_le_norm_sub_add (height29RoundedOffset j) (height29Offset j)
  rw [norm_sub_rev, height29_offset_norm] at h
  linarith only [h, height29_offset_rounding hj]

private theorem height29_point_norm_and_denominator {d : ℂ} (hd : ‖d‖ ≤ 1) :
    ‖c29 + d‖ ≤ 31 ∧ 784 ≤ ‖(c29 + d) * (1 - (c29 + d))‖ := by
  have hc : ‖c29‖ ≤ (3 / 4 : ℝ) + 29 := by
    unfold discriminant23Height29TaylorCenter
    exact (norm_add_le _ _).trans_eq (by norm_num [norm_mul, norm_div])
  have hx : ‖c29 + d‖ ≤ 31 := by linarith only [norm_add_le c29 d, hc, hd]
  have him : 28 ≤ (c29 + d).im := by
    have h := (abs_le.mp ((abs_im_le_norm d).trans hd)).1
    rw [Complex.add_im, show Complex.im c29 = 29 by norm_num [discriminant23Height29TaylorCenter, Complex.mul_im]]
    linarith only [h]
  have h₁ := him.trans ((le_abs_self _).trans (abs_im_le_norm (c29 + d)))
  have h₂ : 28 ≤ ‖1 - (c29 + d)‖ := by
    have h := abs_im_le_norm (1 - (c29 + d))
    rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at h
    exact him.trans ((le_abs_self _).trans h)
  refine ⟨hx, ?_⟩
  rw [norm_mul, show (784 : ℝ) = 28 * 28 by norm_num]
  exact mul_le_mul h₁ h₂ (by norm_num) (norm_nonneg _)

private def height29Pole (w : ℂ) : ℂ := (3 / 2 : ℂ) / (w * (1 - w))

private theorem height29_pole_shift_le {d e : ℂ} (hd : ‖d‖ ≤ 1) (he : ‖e‖ ≤ 1) :
    ‖height29Pole (c29 + d) - height29Pole (c29 + e)‖ ≤ ‖d - e‖ / 1000 := by
  let w := c29 + d
  let v := c29 + e
  let D := w * (1 - w)
  let E := v * (1 - v)
  obtain ⟨hw, hD⟩ := height29_point_norm_and_denominator hd
  obtain ⟨hv, hE⟩ := height29_point_norm_and_denominator he
  have hDpos : 0 < ‖D‖ := (by norm_num : (0 : ℝ) < 784).trans_le hD
  have hEpos : 0 < ‖E‖ := (by norm_num : (0 : ℝ) < 784).trans_le hE
  have hDen : 784 * 784 ≤ ‖D‖ * ‖E‖ := mul_le_mul hD hE (by norm_num) hDpos.le
  have hArg : E - D = (v - w) * (1 - w - v) := by unfold D E; ring
  have hOne : ‖1 - w - v‖ ≤ 63 := by
    have h₁ := norm_sub_le (1 - w) v
    have h₂ := norm_sub_le (1 : ℂ) w
    rw [norm_one] at h₂
    linarith only [h₁, h₂, hw, hv]
  have hDist : ‖v - w‖ = ‖d - e‖ := by
    rw [norm_sub_rev, show w - v = d - e by unfold w v; ring]
  have hNum : ‖(3 / 2 : ℂ) * (E - D)‖ ≤ (3 / 2) * (‖d - e‖ * 63) := by
    rw [hArg, norm_mul, norm_mul, hDist, show ‖(3 / 2 : ℂ)‖ = (3 / 2 : ℝ) by norm_num [norm_div]]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hOne (norm_nonneg _)) (by norm_num)
  change ‖height29Pole w - height29Pole v‖ ≤ _
  rw [show height29Pole w - height29Pole v = (3 / 2 : ℂ) * (E - D) / (D * E) by
    change (3 / 2 : ℂ) / D - (3 / 2 : ℂ) / E = _
    field_simp [norm_pos_iff.mp hDpos, norm_pos_iff.mp hEpos]]
  rw [norm_div, norm_mul _ E]
  calc
    _ ≤ ((3 / 2 : ℝ) * (‖d - e‖ * 63)) / (‖D‖ * ‖E‖) :=
      div_le_div_of_nonneg_right hNum (by positivity)
    _ ≤ ((3 / 2 : ℝ) * (‖d - e‖ * 63)) / (784 * 784) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hDen
    _ ≤ _ := by linarith only [norm_nonneg (d - e)]

private theorem height29_base_rounded_comparison {j : ℕ} (hj : j < 128) (hCheck : Height29TaylorComparison j) :
    ‖discriminant23Height29TaylorPolynomial true (height29RoundedOffset j) -
      height29Pole (height29RoundedPoint j) - discriminant23Height29BaseApprox j‖ ≤ 1 / 10 ^ 27 := by
  let v := height29RoundedPoint j
  let D := v * (1 - v)
  let P := discriminant23Height29TaylorPolynomial true (height29RoundedOffset j)
  let A := discriminant23Height29BaseApprox j
  have hD : (784 : ℝ) ≤ ‖D‖ := (height29_point_norm_and_denominator (height29_rounded_offset_norm hj)).2
  have hp : (0 : ℝ) < ‖D‖ := (by norm_num : (0 : ℝ) < 784).trans_le hD
  have hEq : (P - height29Pole v - A) * D = (P - A) * D - (3 / 2 : ℂ) := by
    change (P - (3 / 2 : ℂ) / D - A) * D = _
    field_simp [norm_pos_iff.mp hp]
    ring
  have h := height29_base_residual_le hCheck.1
  change ‖(P - A) * D - (3 / 2 : ℂ)‖ ≤ _ at h
  rw [← hEq, norm_mul] at h
  change ‖P - height29Pole v - A‖ ≤ _
  have h' := (mul_le_mul_of_nonneg_left hD (norm_nonneg (P - height29Pole v - A))).trans h
  linarith only [h']

private theorem height29_polynomial_phase_error (total : Bool) {j : ℕ} (hj : j < 128) :
    ‖discriminant23Height29TaylorPolynomial total (height29Offset j) -
      discriminant23Height29TaylorPolynomial total (height29RoundedOffset j)‖ ≤ 1 / 10 ^ 27 := by
  have hd : ‖height29Offset j‖ ≤ 1 := by rw [height29_offset_norm]; norm_num
  have he := height29_rounded_offset_norm hj
  have h := norm_polynomial_sub_le_on_unit_disk (discriminant23Height29TaylorApprox total) 36 hd he
  refine h.trans ?_
  have h₁ := mul_le_mul (height29Taylor_derivative_budget total) (height29_offset_rounding hj)
    (norm_nonneg _) (by norm_num)
  exact h₁.trans (by norm_num)

private theorem height29_taylor_rounded_poly_error (total : Bool)
    (hCoeff : ∀ k < 36, ‖discriminant23ClassCombinationTaylorCoeff
      (if total then 2 else -1) c29 k - discriminant23Height29TaylorApprox total k‖ ≤ 1 / 10 ^ 27)
    (j : ℕ) :
    ‖discriminant23ClassCombinationQuadrature (if total then 2 else -1) (discriminant23Height29ReadingPoint j) -
      discriminant23Height29TaylorPolynomial total (height29Offset j)‖ ≤ 4 / 10 ^ 26 := by
  let d := height29Offset j
  let a := discriminant23ClassCombinationTaylorCoeff (if total then 2 else -1) c29
  let b := discriminant23Height29TaylorApprox total
  let P := ∑ k ∈ Finset.range 36, a k * d ^ k
  have hTaylor : ‖discriminant23ClassCombinationQuadrature (if total then 2 else -1) (c29 + d) - P‖ ≤
      1 / 10 ^ 28 := by
    apply discriminant23_classCombination_taylor_error
    · cases total <;> norm_num
    · norm_num [discriminant23Height29TaylorCenter, Complex.mul_re]
    · norm_num [discriminant23Height29TaylorCenter, Complex.mul_re]
    · rw [height29_offset_norm]
  have hRound : ‖P - discriminant23Height29TaylorPolynomial total d‖ ≤ 36 / 10 ^ 27 := by
    change ‖(∑ k ∈ Finset.range 36, a k * d ^ k) -
      ∑ k ∈ Finset.range 36, b k * d ^ k‖ ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ k ∈ Finset.range 36, ‖a k * d ^ k - b k * d ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ _ ∈ Finset.range 36, (1 / 10 ^ 27 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        have h := hCoeff k (Finset.mem_range.mp hk)
        rw [← sub_mul, norm_mul, norm_pow, height29_offset_norm]
        exact (mul_le_of_le_one_right (norm_nonneg _)
          (pow_le_one₀ (by norm_num) (by norm_num))).trans h
      _ = _ := by norm_num
  rw [height29_reading_point_eq]
  exact ((norm_sub_le_norm_sub_add_norm_sub _ P _).trans (add_le_add hTaylor hRound)).trans
    (by norm_num)

theorem discriminant23_height29_base_quadrature_of_taylor
    (hCoeff : ∀ k < 36, ‖discriminant23ClassCombinationTaylorCoeff 2 c29 k -
      discriminant23Height29TaylorApprox true k‖ ≤ 1 / 10 ^ 27)
    {j : ℕ} (hj : j < 128) (hCheck : Height29TaylorComparison j) :
    ‖discriminant23Height29BaseQuadrature (discriminant23Height29ReadingPoint j) -
      discriminant23Height29BaseApprox j‖ ≤ 8 / 10 ^ 26 := by
  let d := height29Offset j
  let e := height29RoundedOffset j
  let Q := discriminant23ClassCombinationQuadrature 2 (discriminant23Height29ReadingPoint j)
  let P := discriminant23Height29TaylorPolynomial true d
  let R := discriminant23Height29TaylorPolynomial true e
  let A := discriminant23Height29BaseApprox j
  let p := height29Pole (c29 + d)
  let q := height29Pole (c29 + e)
  have hQ : ‖Q - P‖ ≤ 4 / 10 ^ 26 := height29_taylor_rounded_poly_error true hCoeff j
  have hP : ‖P - R‖ ≤ 1 / 10 ^ 27 := height29_polynomial_phase_error true hj
  have hR : ‖R - q - A‖ ≤ 1 / 10 ^ 27 := height29_base_rounded_comparison hj hCheck
  have hd : ‖d‖ ≤ 1 := by dsimp only [d]; rw [height29_offset_norm]; norm_num
  have hPole : ‖q - p‖ ≤ 1 / 10 ^ 27 := by
    rw [norm_sub_rev]
    have h := height29_pole_shift_le hd (height29_rounded_offset_norm hj)
    linarith only [h, height29_offset_rounding hj]
  rw [discriminant23Height29BaseQuadrature, show
    (3 / 2 : ℂ) / (discriminant23Height29ReadingPoint j * (1 - discriminant23Height29ReadingPoint j)) =
      p by rw [height29_reading_point_eq]; rfl]
  change ‖Q - p - A‖ ≤ _
  rw [show Q - p - A = (Q - P) + (P - R) + (q - p) + (R - q - A) by ring]
  calc
    _ ≤ ‖Q - P‖ + ‖P - R‖ + ‖q - p‖ + ‖R - q - A‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by linarith only [hQ, hP, hR, hPole]

theorem discriminant23_height29_hecke_quadrature_of_taylor
    (hCoeff : ∀ k < 36, ‖discriminant23ClassCombinationTaylorCoeff (-1) c29 k -
      discriminant23Height29TaylorApprox false k‖ ≤ 1 / 10 ^ 27)
    {j : ℕ} (hj : j < 128) (hCheck : Height29TaylorComparison j) :
    ‖discriminant23ClassCombinationQuadrature (-1) (discriminant23Height29ReadingPoint j) -
      discriminant23Height29HeckeApprox j‖ ≤ 8 / 10 ^ 26 := by
  let d := height29Offset j
  let e := height29RoundedOffset j
  let Q := discriminant23ClassCombinationQuadrature (-1) (discriminant23Height29ReadingPoint j)
  let P := discriminant23Height29TaylorPolynomial false d
  let R := discriminant23Height29TaylorPolynomial false e
  let A := discriminant23Height29HeckeApprox j
  have hQ : ‖Q - P‖ ≤ 4 / 10 ^ 26 := height29_taylor_rounded_poly_error false hCoeff j
  have hP : ‖P - R‖ ≤ 1 / 10 ^ 27 := height29_polynomial_phase_error false hj
  have hR : ‖R - A‖ ≤ 1 / 10 ^ 27 := height29_hecke_residual_le hCheck.2
  change ‖Q - A‖ ≤ _
  calc
    _ ≤ ‖Q - P‖ + ‖P - R‖ + ‖R - A‖ :=
      (norm_sub_le_norm_sub_add_norm_sub _ R _).trans
        (add_le_add (norm_sub_le_norm_sub_add_norm_sub _ P _) le_rfl)
    _ ≤ _ := by linarith only [hQ, hP, hR]

#print axioms discriminant23_height29_base_quadrature_of_taylor
#print axioms discriminant23_height29_hecke_quadrature_of_taylor

end
end FieldTarget
