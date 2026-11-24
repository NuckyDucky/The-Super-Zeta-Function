import DottieLowerContourData
import DottieRectangleResidue

/-! Shift the lower smoothing discrepancy across the pole at zero on a
finite rectangle. At height T_D the Gamma poles lie below this rectangle. -/

namespace QuarticModel

open Complex Finset MeasureTheory Set
open scoped ComplexConjugate
open private range_polynomial_hasDerivAt from DottieRangeContourLocal
open private verticalPoint horizontalPoint from ArchivedDottieContourShift
set_option autoImplicit false

private noncomputable def lowerContourNumerator (S : Finset ℕ) (w z : ℂ) : ℂ :=
  dottieRangePolynomial S (w+z) * Gamma (w+z) *
    Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)

noncomputable def dottieLeftSegment (S : Finset ℕ) (w : ℂ) : ℂ :=
  ∫ u : ℝ in (-20 : ℝ)..20, dottieRightIntegrand S w (verticalPoint (-7) u)

noncomputable def dottieLowerHorizontalEdge (S : Finset ℕ) (w : ℂ) (h : ℝ) : ℂ :=
  ∫ x : ℝ in (-7 : ℝ)..1, dottieRightIntegrand S w (horizontalPoint h x)

noncomputable def dottieRightExterior (S : Finset ℕ) (w : ℂ) : ℂ :=
  ∫ u in (Set.Ioc (-20 : ℝ) 20)ᶜ, dottieRangeIntegrand S w u

noncomputable def dottieLowerContourRemainder (S : Finset ℕ) (w : ℂ) : ℂ :=
  (dottieLeftSegment S w + I*(dottieLowerHorizontalEdge S w (-20) -
    dottieLowerHorizontalEdge S w 20) + dottieRightExterior S w) /
    (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ))

private theorem lower_numerator_differentiable (S : Finset ℕ) (w : ℂ)
    (hw : 21 < w.im) (hS : ∀ n ∈ S, n ≠ 0) :
    DifferentiableOn ℂ (lowerContourNumerator S w) {z : ℂ | -21 < z.im} := by
  intro z hz
  have him : 0 < (w+z).im := by
    have hh : -21 < z.im := hz
    rw [add_im]
    linarith
  have ha : DifferentiableAt ℂ (fun x : ℂ => w+x) z :=
    (differentiableAt_const w).add differentiableAt_id
  have hp := (range_polynomial_hasDerivAt S hS (w+z)).differentiableAt.comp z ha
  have hg : DifferentiableAt ℂ Gamma (w+z) := by
    apply Complex.differentiableAt_Gamma
    intro n hn
    have hi := congrArg Complex.im hn
    simp only [neg_im, natCast_im, neg_zero] at hi
    exact him.ne' hi
  have he : DifferentiableAt ℂ (fun x : ℂ => Complex.exp (x^2-I*(Real.pi : ℂ)*x/2)) z := by
    fun_prop
  exact ((hp.mul (hg.comp z ha)).mul he).differentiableWithinAt

theorem dottie_lower_side_eq_finite_contour (S : Finset ℕ) {w : ℂ}
    (hw₀ : 0 < w.re+1) (hw₁ : 21 < w.im) (hS : ∀ n ∈ S, n ≠ 0) :
    dottieRangeSide S w - dottieFiniteSharpSide S w = dottieLowerContourRemainder S w := by
  have hopen : IsOpen {z : ℂ | -21 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hsub : Complex.reProdIm (Icc (-7 : ℝ) 1) (Icc (-20 : ℝ) 20) ⊆
      {z : ℂ | -21 < z.im} := by
    intro z hz
    have hh : z.im ∈ Icc (-20 : ℝ) 20 := hz.2
    exact (by norm_num : (-21 : ℝ) < -20).trans_le hh.1
  have hres := dottie_rectangle_residue (F := lowerContourNumerator S w)
    (by norm_num : (0 : ℝ) < 20) hopen hsub (lower_numerator_differentiable S w hw₁ hS)
  have hkernel (z : ℂ) : lowerContourNumerator S w z / z = dottieRightIntegrand S w z := rfl
  simp_rw [hkernel] at hres
  have he (u : ℝ) : dottieRightIntegrand S w (1+(u : ℂ)*I) = dottieRangeIntegrand S w u := rfl
  have hf0 : lowerContourNumerator S w 0 = dottieRangePolynomial S w * Gamma w := by
    simp [lowerContourNumerator]
  simp_rw [he, hf0] at hres
  have hres' : (∫ u : ℝ in (-20 : ℝ)..20, dottieRangeIntegrand S w u) -
      dottieLeftSegment S w =
      I*(dottieLowerHorizontalEdge S w (-20)-dottieLowerHorizontalEdge S w 20) +
      2*(Real.pi : ℂ)*(dottieRangePolynomial S w*Gamma w) := by
    simpa only [dottieLeftSegment, dottieLowerHorizontalEdge, verticalPoint,
      horizontalPoint, Complex.ofReal_neg, Complex.ofReal_ofNat] using hres
  have hi := integral_add_compl (s := Set.Ioc (-20 : ℝ) 20) measurableSet_Ioc
    (dottie_range_integrand_integrable S hw₀ hS)
  rw [← intervalIntegral.integral_of_le (by norm_num : (-20 : ℝ) ≤ 20)] at hi
  change (∫ u : ℝ in (-20 : ℝ)..20, dottieRangeIntegrand S w u) +
    dottieRightExterior S w = (∫ u : ℝ, dottieRangeIntegrand S w u) at hi
  rw [dottieRangeSide, ← hi, dottieFiniteSharpSide, dottieLowerContourRemainder]
  have hscale := Complex.ofReal_ne_zero.mpr archivedDottieCompletionScale_pos.ne'
  have hpi := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have htwo : (2*(Real.pi : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) hpi
  have hmul : dottieRangePolynomial S w * Gamma w / (archivedDottieCompletionScale : ℂ) =
      (2*(Real.pi : ℂ)*(dottieRangePolynomial S w * Gamma w)) /
        (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)) := by
    apply (div_eq_div_iff hscale (mul_ne_zero htwo hscale)).2
    ring
  rw [hmul, ← sub_div]
  congr 1
  linear_combination hres'

theorem dottie_lower_smoothing_eq_finite_contours {w : ℂ}
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) (hw₂ : 21 < w.im) :
    let S := Finset.Ioc dottiePrefixEnd dottieOmittedSharpEnd
    dottieOmittedLowerSmoothingError w =
      dottieLowerContourRemainder S w + conj (dottieLowerContourRemainder S (1-conj w)) := by
  rw [dottie_lower_smoothing_eq_two_sides hw₀ hw₁]
  let S := Finset.Ioc dottiePrefixEnd dottieOmittedSharpEnd
  have hS : ∀ n ∈ S, n ≠ 0 := fun _ hn =>
    (Nat.zero_le dottiePrefixEnd |>.trans_lt (Finset.mem_Ioc.mp hn).1).ne'
  have hm : 0 < (1-conj w).re+1 := by simp only [sub_re, one_re, conj_re]; linarith
  have ht : 21 < (1-conj w).im := by simpa using hw₂
  rw [dottie_lower_side_eq_finite_contour S (by linarith : 0 < w.re+1) hw₂ hS,
    dottie_lower_side_eq_finite_contour S hm ht hS]

#print axioms dottie_lower_side_eq_finite_contour
#print axioms dottie_lower_smoothing_eq_finite_contours

end QuarticModel
