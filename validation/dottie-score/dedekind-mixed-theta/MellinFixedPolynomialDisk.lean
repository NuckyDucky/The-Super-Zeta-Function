import MellinFixedTaylorTail

/-! A constant-term margin and one weighted integer sum certify a disk. -/

namespace DottieOriented.NativeSpectrum.MellinFixed

open scoped BigOperators

noncomputable section

namespace ComplexBox

theorem re_pos_of_polynomial_budget (box : ℕ → ComplexBox) (a : ℕ → ℂ)
    {p q n : ℕ} {error tail : ℤ} {z actual : ℂ}
    (hq : 0 < q) (hn : 1 ≤ n) (hz : ‖z‖ ≤ (p : ℝ) / (q : ℝ))
    (ha : ∀ k < n, Contains (box k) (a k))
    (hTail : weightedTailMass box p q 1 n ≤ tail * (q : ℤ) ^ n)
    (hApprox : ‖actual - ∑ k ∈ Finset.range n, a k * z ^ k‖ ≤ (error : ℝ) / (scale : ℝ))
    (hMargin : error + tail < (box 0).re.lo) :
    0 < actual.re := by
  have hRest : ‖(∑ k ∈ Finset.range n, a k * z ^ k) - a 0‖ ≤ (tail : ℝ) / (scale : ℝ) := by
    simpa only [Finset.sum_range_one, pow_zero, mul_one] using
      polynomial_tail_le_of_weighted_mass box a hq hn hz
        (fun k hk ↦ ha k (Finset.mem_Ico.mp hk).2) hTail
  have hError : ‖actual - a 0‖ ≤ ((error : ℝ) + (tail : ℝ)) / (scale : ℝ) := by
    rw [add_div]
    exact (norm_sub_le_norm_sub_add_norm_sub _ (∑ k ∈ Finset.range n, a k * z ^ k) _).trans
      (add_le_add hApprox hRest)
  have hConstant : ((error : ℝ) + (tail : ℝ)) / (scale : ℝ) < (a 0).re := by
    apply lt_of_box_lower (ha 0 (by omega)).1
    have hScale : (scale : ℝ) * (((error : ℝ) + (tail : ℝ)) / (scale : ℝ)) =
        (error : ℝ) + (tail : ℝ) := by field_simp [scale_pos.ne']
    rw [hScale]
    exact_mod_cast hMargin
  have hRe := abs_le.mp ((Complex.abs_re_le_norm (actual - a 0)).trans hError)
  rw [Complex.sub_re] at hRe
  linarith only [hConstant, hRe.1]

end ComplexBox

/-- A polynomial enclosure for a rotated reading on a closed rational disk. -/
structure PolynomialDiskCertificate (reading : ℂ → ℂ) (center : ℂ) (p q : ℕ) where
  denominator_pos : 0 < q
  terms : ℕ
  terms_pos : 1 ≤ terms
  direction : ℂ
  coefficient : ℕ → ℂ
  boxes : ℕ → ComplexBox
  enclosure : ∀ k < terms, ComplexBox.Contains (boxes k) (coefficient k)
  approximationBudget : ℤ
  tailBudget : ℤ
  weighted_tail : ComplexBox.weightedTailMass boxes p q 1 terms ≤ tailBudget * (q : ℤ) ^ terms
  margin : approximationBudget + tailBudget < (boxes 0).re.lo
  approximation : ∀ z : ℂ, ‖z‖ ≤ (p : ℝ) / (q : ℝ) →
    ‖direction * reading (center + z) - ∑ k ∈ Finset.range terms, coefficient k * z ^ k‖ ≤
      (approximationBudget : ℝ) / (scale : ℝ)

theorem PolynomialDiskCertificate.nonzero {reading : ℂ → ℂ} {center w : ℂ} {p q : ℕ}
    (cert : PolynomialDiskCertificate reading center p q)
    (hw : ‖w - center‖ ≤ (p : ℝ) / (q : ℝ)) :
    reading w ≠ 0 := by
  have hIdentity : center + (w - center) = w := by ring
  have h := ComplexBox.re_pos_of_polynomial_budget cert.boxes cert.coefficient
    cert.denominator_pos cert.terms_pos hw cert.enclosure cert.weighted_tail
    (cert.approximation (w - center) hw) cert.margin
  rw [hIdentity] at h
  intro hz
  simp [hz] at h

#print axioms ComplexBox.re_pos_of_polynomial_budget
#print axioms PolynomialDiskCertificate.nonzero

end

end DottieOriented.NativeSpectrum.MellinFixed
