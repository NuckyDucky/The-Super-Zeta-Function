import DottiePowerTailMass
import DottieRightContourShift

/-! The far fixed contour estimate factors into an explicit arithmetic
constant and a real integral for the tilted Gamma ratio. The bound applies
to any finite subset, without enumerating Gaussian ideals in that set. -/

namespace QuarticModel

open Complex Finset MeasureTheory
open scoped ComplexConjugate
open SuperZeta.StirlingCorrection
open private verticalPoint from ArchivedDottieContourShift
set_option autoImplicit false

noncomputable def dottieFarScalar (X : ℕ) (w : ℂ) : ℝ :=
  let p := w.re+7
  (archivedThetaScale^p *
    ((1+(X.sqrt : ℝ)⁻¹)*((X : ℝ)^(1-p)*(p/(p-1))))) *
    Real.exp 49 / (14*Real.pi*archivedThetaScale^2)

private theorem far_polynomial_abs_le (S : Finset ℕ) {X : ℕ} (hX : 0 < X)
    (hS : ∀ n ∈ S, X < n) {s : ℂ} (hs : 1 < s.re) :
    ‖dottieRangePolynomial S s‖ ≤
      archivedThetaScale^s.re *
        ((1+(X.sqrt : ℝ)⁻¹)*((X : ℝ)^(1-s.re)*(s.re/(s.re-1)))) := by
  unfold dottieRangePolynomial
  apply (norm_sum_le _ _).trans
  have hB := archivedThetaScale_pos
  calc
    _ = ∑ n ∈ S, archivedThetaScale^s.re *
        (|(archivedLatticeCoeff n : ℝ)| * (n : ℝ)^(-s.re)) := by
      apply sum_congr rfl
      intro n hn
      have hN : 0 < (n : ℝ) := Nat.cast_pos.mpr (hX.trans (hS n hn))
      rw [norm_mul, Complex.norm_intCast, norm_cpow_eq_rpow_re_of_pos (div_pos hB hN),
        Real.div_rpow hB.le hN.le, Real.rpow_neg hN.le]
      ring
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (archived_power_tail_mass_le S hX hS hs) (by positivity)

/-- A scalar Gamma majorant supplies the absolute bound on the exact
shifted one-sided contour. Both sides still use the original normalization. -/
theorem dottie_right_seven_norm_le_of_tilted_gamma (S : Finset ℕ) {X : ℕ}
    (hX : 0 < X) (hS : ∀ n ∈ S, X < n) {w : ℂ} (hw : 0 < w.re)
    (g : ℝ → ℝ) (hg : Integrable g)
    (hgamma : ∀ u : ℝ,
      ‖Gamma (w+verticalPoint 7 u)‖ * Real.exp (-u^2+Real.pi*u/2) ≤
        ‖Gamma (2+(dottieHeight : ℂ)*I)‖ * g u) :
    ‖dottieRightSide S w 7‖ ≤ dottieFarScalar X w * ∫ u : ℝ, g u := by
  let p := w.re+7
  let M := (1+(X.sqrt : ℝ)⁻¹)*((X : ℝ)^(1-p)*(p/(p-1)))
  let C := archivedThetaScale^p*M*Real.exp 49/7
  let G := ‖Gamma (2+(dottieHeight : ℂ)*I)‖
  have hG : 0 < G := by
    exact norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hp : 1 < p := by dsimp [p]; linarith
  have hp₀ : 0 < p := zero_lt_one.trans hp
  have hpm : 0 < p-1 := sub_pos.mpr hp
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hBp : 0 ≤ archivedThetaScale^p := Real.rpow_nonneg archivedThetaScale_pos.le _
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hpoint (u : ℝ) : ‖dottieRightIntegrand S w (verticalPoint 7 u)‖ ≤ (C*G)*g u := by
    let z := verticalPoint 7 u
    have hzr : z.re = 7 := by simp [z, verticalPoint]
    have hzi : z.im = u := by simp [z, verticalPoint]
    have hs : (w+z).re = p := by rw [Complex.add_re, hzr]
    have hpoly : ‖dottieRangePolynomial S (w+z)‖ ≤ archivedThetaScale^p*M := by
      have ht := far_polynomial_abs_le S hX hS (hs.symm ▸ hp)
      rw [hs] at ht
      exact ht
    have hden : (7 : ℝ) ≤ ‖z‖ := by
      simpa only [hzr, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7)] using Complex.abs_re_le_norm z
    have hexp :
        ‖Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)‖ =
          Real.exp 49 * Real.exp (-u^2+Real.pi*u/2) := by
      have he : (z^2-I*(Real.pi : ℂ)*z/2).re = z.re^2-z.im^2+Real.pi*z.im/2 := by
        simp [pow_two, Complex.mul_re, Complex.mul_im]
        ring
      rw [Complex.norm_exp, ← Real.exp_add, he, hzr, hzi]
      congr 1
      ring
    change ‖dottieRightIntegrand S w z‖ ≤ _
    rw [dottieRightIntegrand, norm_div, norm_mul, norm_mul, hexp]
    calc
      _ ≤ (archivedThetaScale^p*M*‖Gamma (w+z)‖*
          (Real.exp 49*Real.exp (-u^2+Real.pi*u/2)))/7 := by
        apply div_le_div₀ (by positivity) ?_ (by norm_num) hden
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpoly (norm_nonneg _)) (by positivity)
      _ = C*(‖Gamma (w+z)‖ * Real.exp (-u^2+Real.pi*u/2)) := by dsimp [C]; ring
      _ ≤ (C*G)*g u := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hgamma u) hC
  have hi := norm_integral_le_of_norm_le ((hg.const_mul (C*G)))
    (Filter.Eventually.of_forall hpoint)
  rw [integral_const_mul] at hi
  have hscale : 0 < 2*Real.pi*archivedDottieCompletionScale :=
    mul_pos (by positivity) archivedDottieCompletionScale_pos
  have hd : (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)) =
      ((2*Real.pi*archivedDottieCompletionScale : ℝ) : ℂ) := by norm_cast
  rw [dottieRightSide, norm_div, hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hscale]
  refine (div_le_div_of_nonneg_right hi hscale.le).trans_eq ?_
  change C*G*(∫ u : ℝ, g u)/(2*Real.pi*(archivedThetaScale^2*G)) = _
  unfold dottieFarScalar
  change C*G*(∫ u : ℝ, g u)/(2*Real.pi*(archivedThetaScale^2*G)) =
    archivedThetaScale^p*M*Real.exp 49/(14*Real.pi*archivedThetaScale^2)*(∫ u : ℝ, g u)
  dsimp only [C]
  field_simp [hG.ne', Real.pi_ne_zero, archivedThetaScale_pos.ne']
  ring

theorem dottie_far_omitted_norm_le_of_tilted_gamma {w : ℂ}
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) (g gMirror : ℝ → ℝ)
    (hg : Integrable g) (hgMirror : Integrable gMirror)
    (hgamma : ∀ u : ℝ,
      ‖Gamma (w+verticalPoint 7 u)‖ * Real.exp (-u^2+Real.pi*u/2) ≤
        ‖Gamma (2+(dottieHeight : ℂ)*I)‖ * g u)
    (hgammaMirror : ∀ u : ℝ,
      ‖Gamma (1-conj w+verticalPoint 7 u)‖ * Real.exp (-u^2+Real.pi*u/2) ≤
        ‖Gamma (2+(dottieHeight : ℂ)*I)‖ * gMirror u) :
    ‖dottieOmittedFarSmooth w‖ ≤
      dottieFarScalar dottieOmittedFarCut w * (∫ u : ℝ, g u) +
      dottieFarScalar dottieOmittedFarCut (1-conj w) * (∫ u : ℝ, gMirror u) := by
  let S := dottieOmittedNorms.filter (fun n => dottieOmittedFarCut < n)
  have hX : 0 < dottieOmittedFarCut := by decide +kernel
  have hS : ∀ n ∈ S, dottieOmittedFarCut < n := fun _ hn => (mem_filter.mp hn).2
  have hm : 0 < (1-conj w).re := by simpa only [sub_re, one_re, conj_re, sub_pos]
  rw [dottie_omitted_far_eq_right_contours hw₀ hw₁]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj]
  exact add_le_add (dottie_right_seven_norm_le_of_tilted_gamma S hX hS hw₀ g hg hgamma)
    (dottie_right_seven_norm_le_of_tilted_gamma S hX hS hm gMirror hgMirror hgammaMirror)

#print axioms dottie_right_seven_norm_le_of_tilted_gamma
#print axioms dottie_far_omitted_norm_le_of_tilted_gamma

end QuarticModel
