import DottieLowerGammaRightTail
import DottieLowerLeftBound

/-! Absolute exterior estimate on the original contour, with the same
normalization for the retained prefix and the lower omitted range. -/

namespace QuarticModel

open Complex Finset MeasureTheory Set
open SuperZeta.StirlingCorrection
open private dottieContour from ArchivedDottieTailPartition
set_option autoImplicit false
set_option maxRecDepth 4096

private theorem right_polynomial_normalized_mass_le (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^13) {s : ℂ}
    (hs₀ : 0 ≤ s.re) (hs₁ : s.re ≤ 2) :
    ‖dottieRangePolynomial S s‖/archivedThetaScale^2 ≤ 2*10^13 := by
  let B := archivedThetaScale
  have hB : 0 < B := archivedThetaScale_pos
  have hB₁ : 1 ≤ B := by
    change (1 : ℝ) ≤ archivedThetaScale
    linarith only [dottie_theta_scale_gt_three_halves_million]
  have hmass : (∑ n ∈ S, |(archivedLatticeCoeff n : ℝ)|) ≤ (2*10^13 : ℝ) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      dottie_finite_absolute_mass_le S (L := 10^13) hS
  apply (div_le_iff₀ (pow_pos hB 2)).2
  unfold dottieRangePolynomial
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ n ∈ S, |(archivedLatticeCoeff n : ℝ)| * B^2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (hS n hn).1
      have hn₁ : 1 ≤ (n : ℝ) := by
        exact_mod_cast (show 1 ≤ n from (hS n hn).1)
      have hb : 0 < B/(n : ℝ) := div_pos hB hn₀
      change ‖(archivedLatticeCoeff n : ℂ) * ((B/(n : ℝ) : ℝ) : ℂ)^s‖ ≤ _
      rw [norm_mul, Complex.norm_intCast, norm_cpow_eq_rpow_re_of_pos hb]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [← Real.rpow_two]
      exact (Real.rpow_le_rpow hb.le (div_le_self hB.le hn₁) hs₀).trans
        (Real.rpow_le_rpow_of_exponent_le hB₁ hs₁)
    _ ≤ _ := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right hmass (sq_nonneg B)

/-- The normalized exterior of the exact original right contour is small
for any finite norm set below the lower smoothing cutoff. -/
theorem dottie_normalized_right_exterior_bound (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^13) {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieRightExterior S w / (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ))‖ ≤
      1/10^39 := by
  let B := archivedThetaScale
  let G := ‖Gamma (2+(dottieHeight : ℂ)*I)‖
  let den : ℂ := 2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)
  let C : ℝ := (2*10^13)*(2/10^100)*3
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hden : ‖den‖ = 2*Real.pi*(B^2*G) := by
    have hd : den = ((2*Real.pi*archivedDottieCompletionScale : ℝ) : ℂ) := by
      dsimp only [den]
      norm_cast
    calc
      ‖den‖ = 2*Real.pi*archivedDottieCompletionScale := by
        rw [hd, Complex.norm_real, Real.norm_eq_abs, abs_of_pos
          (mul_pos (by positivity) archivedDottieCompletionScale_pos)]
      _ = _ := rfl
  have hpoint (u : ℝ) (hu : u ∈ (Set.Ioc (-20 : ℝ) 20)ᶜ) :
      ‖dottieRangeIntegrand S w u/den‖ ≤ C*Real.exp (-(1/8 : ℝ)*u^2) := by
    let z := dottieContour u
    have hz₀ : z.re = 1 := by simp [z, dottieContour]
    have hz₁ : z.im = u := by simp [z, dottieContour]
    have hz : (1 : ℝ) ≤ ‖z‖ := by simpa [hz₀] using Complex.abs_re_le_norm z
    have hprod : (1 : ℝ) ≤ ‖z‖*(2*Real.pi) := by
      have hp : (1 : ℝ) ≤ 2*Real.pi := by linarith only [Real.pi_gt_three]
      simpa using mul_le_mul hz hp (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg z)
    have hs : w+z = ⟨w.re+1,w.im+u⟩ := by apply Complex.ext <;> simp [hz₀, hz₁]
    have hu' : 20 ≤ |u| := by
      rcases le_or_gt u (-20) with h | h
      · rw [abs_of_nonpos (by linarith only [h])]
        linarith only [h]
      · have h' : 20 < u := lt_of_not_ge (fun hu' => hu ⟨h, hu'⟩)
        exact h'.le.trans (le_abs_self u)
    have hg : ‖Gamma (w+z)‖*Real.exp (Real.pi*u/2-u^2)/G ≤
        (2/10^100 : ℝ)*Real.exp (-(1/8 : ℝ)*u^2) := by
      rw [hs]
      exact dottie_lower_right_tail_gamma_envelope hr hi hu'
    have hpoly : ‖dottieRangePolynomial S (w+z)‖/B^2 ≤ 2*10^13 := by
      apply right_polynomial_normalized_mass_le S hS
      · rw [add_re,hz₀]
        linarith only [hr.1]
      · rw [add_re,hz₀]
        linarith only [hr.2]
    have hexp : ‖Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)‖ =
        Real.exp 1 * Real.exp (Real.pi*u/2-u^2) := by
      have he : (z^2-I*(Real.pi : ℂ)*z/2).re = z.re^2-z.im^2+Real.pi*z.im/2 := by
        simp [pow_two, Complex.mul_re, Complex.mul_im]
        ring
      rw [Complex.norm_exp, he, hz₀, hz₁, ← Real.exp_add]
      congr 1
      ring
    change ‖(dottieRangePolynomial S (w+z) * Gamma (w+z) *
      Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)/z)/den‖ ≤ _
    rw [norm_div, norm_div, norm_mul, norm_mul, hexp, hden]
    calc
      _ = (‖dottieRangePolynomial S (w+z)‖/B^2) *
          (‖Gamma (w+z)‖*Real.exp (Real.pi*u/2-u^2)/G) *
          Real.exp 1/(‖z‖*(2*Real.pi)) := by ring
      _ ≤ (2*10^13)*((2/10^100)*Real.exp (-(1/8 : ℝ)*u^2))*Real.exp 1/1 := by
        apply div_le_div₀ (by positivity) ?_ (by norm_num) hprod
        exact mul_le_mul_of_nonneg_right (mul_le_mul hpoly hg (by positivity) (by positivity))
          (Real.exp_pos _).le
      _ ≤ _ := by
        rw [div_one]
        refine (mul_le_mul_of_nonneg_left Real.exp_one_lt_three.le (by positivity)).trans_eq ?_
        dsimp only [C]
        ring
  have hb : Integrable (fun u : ℝ => C*Real.exp (-(1/8 : ℝ)*u^2)) :=
    (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1/8 by norm_num)).const_mul C
  change ‖dottieRightExterior S w/den‖ ≤ _
  rw [dottieRightExterior, ← MeasureTheory.integral_div]
  refine (MeasureTheory.norm_integral_le_of_norm_le hb.integrableOn ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc.compl] with u hu using hpoint u hu
  · refine (setIntegral_le_integral hb (Filter.Eventually.of_forall (fun u =>
      mul_nonneg hC (Real.exp_pos (-(1/8 : ℝ)*u^2)).le))).trans ?_
    rw [integral_const_mul, integral_gaussian]
    have hG : √(Real.pi/(1/8 : ℝ)) ≤ 6 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith only [Real.pi_lt_four]⟩
    refine (mul_le_mul_of_nonneg_left hG hC).trans ?_
    dsimp only [C]
    norm_num

#print axioms dottie_normalized_right_exterior_bound

end QuarticModel
