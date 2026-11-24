import DottieRangeContourLocal
import DottieRangeDifferentiation
import ArchivedDottieContourShift
import ArchivedDottieOmittedBudget
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Finite Gaussian norm blocks can be moved farther right without changing
their integral. This allows the far block to use a larger power of the norm
than the original line at real part one. -/

namespace QuarticModel

open Complex Filter Finset MeasureTheory Set
open scoped Topology ComplexConjugate
open private verticalPoint horizontalPoint from ArchivedDottieContourShift
open private norm_gamma_of_re_pos dottieContour from ArchivedDottieTailPartition
open private gamma_differentiableAt_pos range_polynomial_hasDerivAt from DottieRangeContourLocal

noncomputable def dottieRightIntegrand (S : Finset ℕ) (w z : ℂ) : ℂ :=
  dottieRangePolynomial S (w+z) * Gamma (w+z) *
    Complex.exp (z^2-I*(Real.pi : ℂ)*z/2) / z

noncomputable def dottieRightSide (S : Finset ℕ) (w : ℂ) (c : ℝ) : ℂ :=
  (∫ u : ℝ, dottieRightIntegrand S w (verticalPoint c u)) /
    (2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ))

private theorem right_integrand_differentiableAt (S : Finset ℕ) (w : ℂ) {z : ℂ}
    (hz : 0 < z.re) (hs : 0 < (w+z).re) (hS : ∀ n ∈ S, n ≠ 0) :
    DifferentiableAt ℂ (dottieRightIntegrand S w) z := by
  have ha : DifferentiableAt ℂ (fun x : ℂ => w+x) z :=
    (differentiableAt_const w).add differentiableAt_id
  have hp := (range_polynomial_hasDerivAt S hS (w+z)).differentiableAt.comp z ha
  have hG := (gamma_differentiableAt_pos hs).comp z ha
  have ht : DifferentiableAt ℂ (fun x : ℂ => Complex.exp (x^2-I*(Real.pi : ℂ)*x/2)) z := by
    fun_prop
  exact ((hp.mul hG).mul ht).div differentiableAt_id (fun he => by simp [he] at hz)

private noncomputable def rightContourFactor (S : Finset ℕ) (w : ℂ) (c : ℝ) : ℝ :=
  (∑ n ∈ S, ‖(archivedLatticeCoeff n : ℂ)‖ *
    (archivedThetaScale/(n : ℝ))^(w.re+c)) *
    Real.Gamma (w.re+c) * Real.exp (c^2+Real.pi^2/8)

private theorem right_integrand_bound (S : Finset ℕ) (w z : ℂ)
    (hz : 1 ≤ z.re) (hs : 0 < (w+z).re) (hS : ∀ n ∈ S, n ≠ 0) :
    ‖dottieRightIntegrand S w z‖ ≤
      rightContourFactor S w z.re * Real.exp (-((1/2 : ℝ)*z.im^2)) := by
  have hPoly : ‖dottieRangePolynomial S (w+z)‖ ≤
      ∑ n ∈ S, ‖(archivedLatticeCoeff n : ℂ)‖ *
        (archivedThetaScale/(n : ℝ))^(w.re+z.re) := by
    unfold dottieRangePolynomial
    refine (norm_sum_le _ _).trans (sum_le_sum fun n hn => ?_)
    have hb : 0 < archivedThetaScale/(n : ℝ) :=
      div_pos archivedThetaScale_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hS n hn)))
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hb, add_re]
  have hG : ‖Gamma (w+z)‖ ≤ Real.Gamma (w.re+z.re) := norm_gamma_of_re_pos hs
  have ht : ‖Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)‖ ≤
      Real.exp (z.re^2+Real.pi^2/8) * Real.exp (-((1/2 : ℝ)*z.im^2)) := by
    rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
    have hre : (z^2-I*(Real.pi : ℂ)*z/2).re = z.re^2-z.im^2+Real.pi*z.im/2 := by
      simp [pow_two, Complex.mul_re, Complex.mul_im]
      ring
    rw [hre]
    nlinarith only [sq_nonneg (z.im-Real.pi/2)]
  have hdenom : 1 ≤ ‖z‖ := hz.trans ((le_abs_self _).trans (abs_re_le_norm z))
  rw [dottieRightIntegrand, norm_div, norm_mul, norm_mul, rightContourFactor, mul_assoc _ (Real.exp _) _]
  refine (div_le_self (by positivity) hdenom).trans ?_
  exact mul_le_mul (mul_le_mul hPoly hG (norm_nonneg _) ((norm_nonneg _).trans hPoly))
    ht (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hPoly) ((norm_nonneg _).trans hG))

private theorem right_contour_factor_continuousOn (S : Finset ℕ) (w : ℂ) {c : ℝ}
    (hw : 0 < w.re+1) (hS : ∀ n ∈ S, n ≠ 0) :
    ContinuousOn (rightContourFactor S w) (Icc 1 c) := by
  have hRe : Continuous (fun a : ℝ => w.re+a) := continuous_const.add continuous_id
  have hGamma : ContinuousOn (fun a : ℝ => Real.Gamma (w.re+a)) (Icc 1 c) :=
    Real.differentiableOn_Gamma_Ioi.continuousOn.comp hRe.continuousOn (fun x hx => by
      have h₁ := (mem_Icc.mp hx).1
      change 0 < w.re+x
      linarith)
  unfold rightContourFactor
  refine ((continuousOn_finsetSum S fun n hn => ?_).mul hGamma).mul (by fun_prop)
  have hb : 0 < archivedThetaScale/(n : ℝ) :=
    div_pos archivedThetaScale_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hS n hn)))
  exact continuousOn_const.mul ((Real.continuous_const_rpow hb.ne').comp hRe).continuousOn

private theorem right_vertical_re (a u : ℝ) : (verticalPoint a u).re = a := by
  simp [verticalPoint]

private theorem right_vertical_im (a u : ℝ) : (verticalPoint a u).im = u := by
  simp [verticalPoint]

private theorem right_horizontal_re (u a : ℝ) : (horizontalPoint u a).re = a := by
  simp [horizontalPoint]

private theorem right_horizontal_im (u a : ℝ) : (horizontalPoint u a).im = u := by
  simp [horizontalPoint]

theorem dottie_right_side_eq_range_side (S : Finset ℕ) (w : ℂ) {c : ℝ}
    (hc : 1 ≤ c) (hw : 0 < w.re+1) (hS : ∀ n ∈ S, n ≠ 0) :
    dottieRightSide S w c = dottieRangeSide S w := by
  let f := dottieRightIntegrand S w
  have hd {z : ℂ} (hz : 1 ≤ z.re) : DifferentiableAt ℂ f z := by
    apply right_integrand_differentiableAt S w (by linarith)
      (by rw [add_re]; linarith) hS
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (right_contour_factor_continuousOn S w (c := c) hw hS)
  have hb (z : ℂ) (hz : z.re ∈ Icc 1 c) :
      ‖f z‖ ≤ M * Real.exp (-((1/2 : ℝ)*z.im^2)) := by
    refine (right_integrand_bound S w z hz.1 (by rw [add_re]; linarith [hz.1]) hS).trans ?_
    exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hM z.re hz)) (Real.exp_pos _).le
  have hv (a : ℝ) (ha : a ∈ Icc 1 c) :
      Integrable (fun u => f (verticalPoint a u)) := by
    have hcont : Continuous (fun u => f (verticalPoint a u)) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      exact (hd (by simpa only [right_vertical_re] using ha.1)).continuousAt.comp
        (show Continuous (verticalPoint a) by unfold verticalPoint; fun_prop).continuousAt
    have hint := (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1/2 by norm_num)).const_mul M
    refine hint.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    simpa only [right_vertical_im, neg_mul] using hb (verticalPoint a u)
      (by simpa only [right_vertical_re] using ha)
  have hlim : Tendsto (fun T : ℝ => Real.exp (-((1/2 : ℝ)*T^2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    exact tendsto_neg_atTop_atBot.comp
      ((tendsto_pow_atTop (n := 2) (by norm_num : 2 ≠ 0)).const_mul_atTop
        (by norm_num : (0 : ℝ) < 1/2))
  have hdec (e : ℝ) (he : e^2 = 1) :
      Tendsto (fun T : ℝ => ∫ a in (1 : ℝ)..c, f (horizontalPoint (e*T) a)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [mul_zero] using hlim.const_mul (M*(c-1)))
      (Eventually.of_forall fun _ => norm_nonneg _) (Eventually.of_forall fun T => ?_)
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (1 : ℝ)) (b := c) (C := M*Real.exp (-((1/2 : ℝ)*T^2)))
      (f := fun a => f (horizontalPoint (e*T) a)) (fun a ha => by
        rw [uIoc_of_le hc] at ha
        simpa only [right_horizontal_im, mul_pow, he, one_mul] using
          hb (horizontalPoint (e*T) a) (by simpa only [right_horizontal_re] using
            (show a ∈ Icc 1 c from ⟨ha.1.le,ha.2⟩)))
    rwa [abs_of_nonneg (sub_nonneg.mpr hc), mul_right_comm] at hbound
  have hdec₁ := hdec 1 (by norm_num)
  have hdec₂ := hdec (-1) (by norm_num)
  simp only [one_mul, neg_one_mul] at hdec₁ hdec₂
  have hC (T : ℝ) :
      (∫ u in -T..T, f (verticalPoint c u)) -
        (∫ u in -T..T, f (verticalPoint 1 u)) =
      I*((∫ a in (1 : ℝ)..c, f (horizontalPoint (-T) a)) -
        (∫ a in (1 : ℝ)..c, f (horizontalPoint T a))) := by
    have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f
      ⟨1,-T⟩ ⟨c,T⟩ (fun z hz => (hd (by
        have hz' : z.re ∈ Set.uIcc (1 : ℝ) c := hz.1
        rw [uIcc_of_le hc] at hz'
        exact hz'.1)).differentiableWithinAt)
    simp only [horizontalPoint, verticalPoint, smul_eq_mul] at h ⊢
    linear_combination (-I)*h + ((∫ u in -T..T, f ((c : ℂ)+(u : ℂ)*I)) -
      (∫ u in -T..T, f ((1 : ℝ)+(u : ℂ)*I))) * Complex.I_sq
  have hl (a : ℝ) (ha : a ∈ Icc 1 c) :=
    intervalIntegral_tendsto_integral (hv a ha) tendsto_neg_atTop_atBot tendsto_id
  have hzero := ((hdec₂.sub hdec₁).const_mul I).congr' (Eventually.of_forall fun T => (hC T).symm)
  simp only [sub_self, mul_zero] at hzero
  have heq : (∫ u : ℝ, f (verticalPoint c u)) = (∫ u : ℝ, f (verticalPoint 1 u)) :=
    sub_eq_zero.mp (tendsto_nhds_unique ((hl c ⟨hc,le_rfl⟩).sub (hl 1 ⟨le_rfl,hc⟩)) hzero)
  unfold dottieRightSide dottieRangeSide
  rw [heq]
  rfl

/-- The horizontal derivative can also be taken on the shifted contour. -/
theorem dottie_right_side_hasDerivAt (S : Finset ℕ) {w : ℂ} {c : ℝ}
    (hc : 1 ≤ c) (hw : 0 < w.re+1) (hS : ∀ n ∈ S, n ≠ 0) :
    HasDerivAt (fun v => dottieRightSide S v c) (dottieRangeSideDerivative S w) w := by
  have hcont : Continuous (fun v : ℂ => v.re+1) := continuous_re.add continuous_const
  have hn : ∀ᶠ v in 𝓝 w, 0 < v.re+1 :=
    (isOpen_lt continuous_const hcont).mem_nhds hw
  exact (dottie_range_side_hasDerivAt S hw hS).congr_of_eventuallyEq <|
    hn.mono (fun v hv => dottie_right_side_eq_range_side S v hc hv hS)

/-- Express the actual finite far block on the line used for its absolute
error bound, retaining both sheets of the Gaussian reflection. -/
theorem dottie_omitted_far_eq_right_contours {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    let S := dottieOmittedNorms.filter (fun n => dottieOmittedFarCut < n)
    dottieOmittedFarSmooth w =
      dottieRightSide S w 7 + conj (dottieRightSide S (1-conj w) 7) := by
  dsimp only
  let S := dottieOmittedNorms.filter (fun n => dottieOmittedFarCut < n)
  have hS : ∀ n ∈ S, n ≠ 0 := by
    intro n hn
    have h := (Finset.mem_filter.mp hn).2
    omega
  have hMirror : 0 < (1-conj w).re+1 := by
    simp only [sub_re, one_re, conj_re]
    linarith
  change (∑ n ∈ S, dottieSmoothTerm w n) =
    dottieRightSide S w 7 + conj (dottieRightSide S (1-conj w) 7)
  rw [dottie_right_side_eq_range_side S w (by norm_num) (by linarith) hS,
    dottie_right_side_eq_range_side S (1-conj w) (by norm_num) hMirror hS,
    dottie_range_side_eq_sum S (by linarith : 0 < w.re+1) hS,
    dottie_range_side_eq_sum S hMirror hS, map_sum, ← Finset.sum_add_distrib]
  rfl

#print axioms dottie_right_side_eq_range_side
#print axioms dottie_right_side_hasDerivAt
#print axioms dottie_omitted_far_eq_right_contours

end QuarticModel
