import ArchivedDottieRangeIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Local regularity of the signed Gaussian range contour. -/

namespace QuarticModel

open Complex Finset Set
open private dottieContour from ArchivedDottieTailPartition

private theorem contour_re (u : ℝ) : (dottieContour u).re = 1 := by
  simp [dottieContour]

/-- The finite conductor-scaled Dirichlet polynomial with its logarithmic weight. -/
noncomputable def dottieRangeLogPolynomial (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, (archivedLatticeCoeff n : ℂ) * ((archivedThetaScale / (n : ℝ) : ℝ) : ℂ)^s *
    (Real.log (archivedThetaScale / (n : ℝ)) : ℂ)

private theorem range_polynomial_hasDerivAt (S : Finset ℕ) (hS : ∀ n ∈ S, n ≠ 0) (s : ℂ) :
    HasDerivAt (dottieRangePolynomial S) (dottieRangeLogPolynomial S s) s := by
  unfold dottieRangePolynomial dottieRangeLogPolynomial
  refine HasDerivAt.fun_sum fun n hn => ?_
  let b := archivedThetaScale / (n : ℝ)
  have hb : 0 < b := div_pos archivedThetaScale_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hS n hn)))
  have hp := (hasDerivAt_id' s).const_cpow (c := (b : ℂ)) (Or.inl (ofReal_ne_zero.mpr hb.ne'))
  simpa only [mul_one, ← mul_assoc, ← Complex.ofReal_log hb.le] using
    hp.const_mul (archivedLatticeCoeff n : ℂ)

private theorem gamma_differentiableAt_pos {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gamma s := by
  refine Complex.differentiableAt_Gamma s fun n hn => ?_
  have h := congrArg Complex.re hn
  rw [Complex.neg_re, Complex.natCast_re] at h
  linarith only [h, hs, Nat.cast_nonneg (α := ℝ) n]

private theorem completed_range_differentiableAt (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z => dottieRangePolynomial S z * Gamma z) s :=
  (range_polynomial_hasDerivAt S hS s).differentiableAt.mul (gamma_differentiableAt_pos hs)

private theorem range_integrand_hasDerivAt (S : Finset ℕ) {w : ℂ}
    (hw : 0 < w.re + 1) (hS : ∀ n ∈ S, n ≠ 0) (u : ℝ) :
    HasDerivAt (fun x => dottieRangeIntegrand S x u)
      (deriv (fun s => dottieRangePolynomial S s * Gamma s) (w + dottieContour u) *
        Complex.exp ((dottieContour u)^2 - I * (Real.pi : ℂ) * dottieContour u / 2) /
          dottieContour u) w := by
  have hs : 0 < (w + dottieContour u).re := by
    simpa only [Complex.add_re, contour_re] using hw
  have shifted := (completed_range_differentiableAt S hS hs).hasDerivAt.comp w
    ((hasDerivAt_id' w).add_const (dottieContour u))
  simpa only [dottieRangeIntegrand, Function.comp_apply, mul_one] using
    (shifted.mul_const (Complex.exp ((dottieContour u)^2 - I * (Real.pi : ℂ) * dottieContour u / 2)))
      |>.div_const (dottieContour u)

/-- Differentiate only the polynomial and Gamma factors at a fixed contour parameter. -/
theorem dottie_range_integrand_hasDerivAt (S : Finset ℕ) {w : ℂ}
    (hw : 0 < w.re + 1) (hS : ∀ n ∈ S, n ≠ 0) (u : ℝ) :
    let z := 1 + (u : ℂ) * I
    let s := w + z
    HasDerivAt (fun x => dottieRangeIntegrand S x u)
      ((dottieRangeLogPolynomial S s * Gamma s + dottieRangePolynomial S s * deriv Gamma s) *
        Complex.exp (z^2 - I * (Real.pi : ℂ) * z / 2) / z) w := by
  let z := dottieContour u
  let s := w + z
  have hs : 0 < s.re := by simpa only [s, z, Complex.add_re, contour_re] using hw
  have completed := (range_polynomial_hasDerivAt S hS s).mul (gamma_differentiableAt_pos hs).hasDerivAt
  change HasDerivAt (fun x => dottieRangeIntegrand S x u)
    ((dottieRangeLogPolynomial S s * Gamma s + dottieRangePolynomial S s * deriv Gamma s) *
      Complex.exp (z^2 - I * (Real.pi : ℂ) * z / 2) / z) w
  rw [← completed.deriv]
  exact range_integrand_hasDerivAt S hw hS u

theorem dottie_range_integrand_differentiableAt (S : Finset ℕ) {w : ℂ}
    (hw : 0 < w.re + 1) (hS : ∀ n ∈ S, n ≠ 0) (u : ℝ) :
    DifferentiableAt ℂ (fun x => dottieRangeIntegrand S x u) w :=
  (range_integrand_hasDerivAt S hw hS u).differentiableAt

private theorem weighted_contour_continuous {g : ℂ → ℂ} {w : ℂ}
    (hw : 0 < w.re + 1) (hg : ContinuousOn g {s : ℂ | 0 < s.re}) :
    Continuous (fun u => g (w + dottieContour u) *
      Complex.exp ((dottieContour u)^2 - I * (Real.pi : ℂ) * dottieContour u / 2) /
        dottieContour u) := by
  have hc : Continuous dottieContour := by unfold dottieContour; fun_prop
  have hc_ne (u : ℝ) : dottieContour u ≠ 0 := by
    intro h
    exact one_ne_zero (by simpa only [contour_re, Complex.zero_re] using congrArg Complex.re h)
  have hg_cont : Continuous (fun u => g (w + dottieContour u)) :=
    hg.comp_continuous (continuous_const.add hc) (fun u => by
      change 0 < (w + dottieContour u).re
      simpa only [Complex.add_re, contour_re] using hw)
  have hweight : Continuous (fun u =>
      Complex.exp ((dottieContour u)^2 - I * (Real.pi : ℂ) * dottieContour u / 2)) :=
    Continuous.cexp ((hc.pow 2).sub ((continuous_const.mul hc).div_const 2))
  exact (hg_cont.mul hweight).div hc hc_ne

theorem dottie_range_integrand_continuous (S : Finset ℕ) {w : ℂ}
    (hw : 0 < w.re + 1) (hS : ∀ n ∈ S, n ≠ 0) :
    Continuous (dottieRangeIntegrand S w) :=
  weighted_contour_continuous hw (g := fun s => dottieRangePolynomial S s * Gamma s)
    (fun _ hs => (completed_range_differentiableAt S hS hs).continuousAt.continuousWithinAt)

theorem dottie_range_integrand_deriv_continuous (S : Finset ℕ) {w : ℂ}
    (hw : 0 < w.re + 1) (hS : ∀ n ∈ S, n ≠ 0) :
    Continuous (fun u => deriv (fun x => dottieRangeIntegrand S x u) w) := by
  have hd : DifferentiableOn ℂ (fun s => dottieRangePolynomial S s * Gamma s) {s : ℂ | 0 < s.re} :=
    fun s hs => (completed_range_differentiableAt S hS hs).differentiableWithinAt
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  rw [funext fun u => (range_integrand_hasDerivAt S hw hS u).deriv]
  exact weighted_contour_continuous hw (hd.analyticOnNhd hopen).deriv.continuousOn

#print axioms dottieRangeLogPolynomial
#print axioms dottie_range_integrand_hasDerivAt
#print axioms dottie_range_integrand_differentiableAt
#print axioms dottie_range_integrand_continuous
#print axioms dottie_range_integrand_deriv_continuous

end QuarticModel
