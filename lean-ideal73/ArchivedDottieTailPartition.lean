import ArchivedDottieRing
import ArchivedQuarticLatticeCoefficients
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The exact smoothed norm terms and the intervals retained by the Dottie
circle calculation. See the repository's Gaussian rectangle bounds. -/

open Complex MeasureTheory Set
open scoped ComplexConjugate

namespace QuarticModel

open SuperZeta.StirlingCorrection

def dottiePrefixEnd : ℕ := 1442840576

def dottieRetainedNorm (n : ℕ) : Bool := decide (
  n ≤ dottiePrefixEnd ∨
  1854467118035498894 ≤ n ∧ n ≤ 1854467118035629965 ∨
  1854467118035629966 ≤ n ∧ n ≤ 1854467118035634061 ∨
  3708934236071001884 ≤ n ∧ n ≤ 3708934236071264027 ∨
  3708934236071264028 ≤ n ∧ n ≤ 3708934236071268123 ∨
  7417868472142007863 ≤ n ∧ n ≤ 7417868472142532150 ∨
  7417868472142532151 ≤ n ∧ n ≤ 7417868472142536246 ∨
  179178262476838746198975364 < n)

private noncomputable def dottieContour (u : ℝ) : ℂ := 1+(u : ℂ)*I

noncomputable def dottieContourIntegrand (w : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  let z := dottieContour u
  ((archivedThetaScale / (n : ℝ) : ℝ) : ℂ)^(w+z) * Gamma (w+z) *
    Complex.exp (z^2-I*(Real.pi : ℂ)*z/2) / z

/-- One normalized term of the positive-height contour integral. The height
tilt and the line Re(z)=1 match the archived weights. -/
noncomputable def dottieSmoothSide (w : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    (archivedLatticeCoeff n : ℂ) /
      (2 * (Real.pi : ℂ) * (archivedDottieCompletionScale : ℂ)) *
    ∫ u : ℝ, dottieContourIntegrand w n u

private theorem norm_gamma_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ‖Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx' : 0 < x := hx
  rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le,
    norm_cpow_eq_rpow_re_of_pos hx']
  rfl

private noncomputable def dottieContourMajorant (w : ℂ) (n : ℕ) (u : ℝ) : ℝ :=
  (archivedThetaScale/(n : ℝ))^(w.re+1) * Real.Gamma (w.re+1) *
    Real.exp (1+Real.pi^2/8) * Real.exp (-((1/2 : ℝ)*u^2))

private theorem norm_dottieContourIntegrand_le {w : ℂ} (hw : 0 < w.re+1)
    {n : ℕ} (hn : n ≠ 0) (u : ℝ) :
    ‖dottieContourIntegrand w n u‖ ≤ dottieContourMajorant w n u := by
  let z := dottieContour u
  have hz : z.re = 1 := by simp [z, dottieContour]
  have hzre : (w+z).re = w.re+1 := by simp only [add_re, hz]
  have hz₁ : 1 ≤ ‖z‖ := by simpa [hz] using (Complex.abs_re_le_norm z)
  have hbase : 0 < archivedThetaScale / (n : ℝ) :=
    div_pos archivedThetaScale_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  have hgamma := norm_gamma_of_re_pos (show 0 < (w+z).re by rwa [hzre])
  rw [hzre] at hgamma
  have hexpr : (z^2-I*(Real.pi : ℂ)*z/2).re = 1-u^2+Real.pi*u/2 := by
    simp [pow_two, z, dottieContour, Complex.mul_re, Complex.mul_im]
    ring
  have hexp : ‖Complex.exp (z^2-I*(Real.pi : ℂ)*z/2)‖ ≤
      Real.exp (1+Real.pi^2/8) * Real.exp (-((1/2 : ℝ)*u^2)) := by
    rw [Complex.norm_exp, hexpr, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith only [sq_nonneg (u-Real.pi/2)])
  unfold dottieContourMajorant
  change ‖((archivedThetaScale/(n : ℝ) : ℝ) : ℂ)^(w+z) * Gamma (w+z) *
    Complex.exp (z^2-I*(Real.pi : ℂ)*z/2) / z‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hbase, hzre]
  refine (div_le_self (by positivity) hz₁).trans ?_
  rw [mul_assoc _ (Real.exp _) (Real.exp _)]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hgamma (Real.rpow_nonneg hbase.le _))
    hexp (norm_nonneg _) (by positivity)

/-- The exact smoothed integrand is absolutely integrable on the real
parameter of its contour. This is a prerequisite for summing over norms. -/
theorem dottieContourIntegrand_integrable {w : ℂ} (hw : 0 < w.re+1)
    {n : ℕ} (hn : n ≠ 0) :
    Integrable (dottieContourIntegrand w n) := by
  have hM : Integrable (dottieContourMajorant w n) := by
    unfold dottieContourMajorant
    simp only [← neg_mul]
    exact (integrable_exp_neg_mul_sq (show (0 : ℝ) < 1/2 by norm_num)).const_mul
      ((archivedThetaScale/(n : ℝ))^(w.re+1) * Real.Gamma (w.re+1) *
        Real.exp (1+Real.pi^2/8))
  refine hM.mono' ?_ (Filter.Eventually.of_forall (norm_dottieContourIntegrand_le hw hn))
  have hc : Continuous dottieContour := by unfold dottieContour; fun_prop
  have hz (u : ℝ) : (dottieContour u).re = 1 := by simp [dottieContour]
  have hcNe (u : ℝ) : dottieContour u ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    rw [hz, Complex.zero_re] at this
    norm_num at this
  have hg : Continuous (fun u => Gamma (w+dottieContour u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    apply (Complex.continuousAt_Gamma _ ?_).comp (continuous_const.add hc).continuousAt
    intro m he
    have he' : (w+dottieContour u).re = (-(m : ℂ)).re := congrArg Complex.re he
    simp only [add_re, hz, neg_re, natCast_re] at he'
    linarith only [hw, he', Nat.cast_nonneg (α := ℝ) m]
  have hb : (((archivedThetaScale/(n : ℝ) : ℝ) : ℂ)) ≠ 0 :=
    ofReal_ne_zero.mpr (div_pos archivedThetaScale_pos
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
  have hp : Continuous (fun u : ℝ => (((archivedThetaScale/(n : ℝ) : ℝ) : ℂ)) ^
      (w+dottieContour u)) := by
    simp_rw [cpow_def_of_ne_zero hb]
    fun_prop
  exact ((hp.mul hg).mul (Continuous.cexp (by fun_prop))).div hc hcNe |>.aestronglyMeasurable

noncomputable def dottieSmoothTerm (w : ℂ) (n : ℕ) : ℂ :=
  dottieSmoothSide w n + conj (dottieSmoothSide (1-conj w) n)

private noncomputable def dottieSharpSide (w : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    (archivedLatticeCoeff n : ℂ) * ((archivedThetaScale / (n : ℝ) : ℝ) : ℂ)^w *
      Gamma w / (archivedDottieCompletionScale : ℂ)

/-- The positive reference unit used in the interval arithmetic, prior to
checking its nonzero numerical enclosure. -/
noncomputable def dottieCircleReference : ℝ :=
  let w := archivedRightCenter dottieHeight - (1/64 : ℂ)
  ‖∑ n ∈ Finset.range (276824064+1),
    (dottieSharpSide w n + conj (dottieSharpSide (1-conj w) n))‖

noncomputable def dottieRetained (w : ℂ) : ℂ :=
  ∑' n : ℕ, if dottieRetainedNorm n then dottieSmoothTerm w n else 0

noncomputable def dottieOmitted (w : ℂ) : ℂ :=
  ∑' n : ℕ, if dottieRetainedNorm n then 0 else dottieSmoothTerm w n

/-- Split the normalized full sum at every circle input. The contour identity
and absolute convergence are the analytic input to this arithmetic partition. -/
theorem dottie_normalized_remainder_eq_omitted {w : ℂ}
    (habs : Summable (fun n => ‖dottieSmoothTerm w n‖))
    (hfull : HasSum (dottieSmoothTerm w) (archivedMellin w/(archivedDottieCompletionScale : ℂ))) :
    archivedMellin w/(archivedDottieCompletionScale : ℂ) - dottieRetained w = dottieOmitted w := by
  let p := fun n => if dottieRetainedNorm n then dottieSmoothTerm w n else 0
  let q := fun n => if dottieRetainedNorm n then 0 else dottieSmoothTerm w n
  have hp : Summable p := Summable.of_norm_bounded habs fun n => by
    by_cases hn : dottieRetainedNorm n = true <;> simp [p, hn]
  have hq : Summable q := Summable.of_norm_bounded habs fun n => by
    by_cases hn : dottieRetainedNorm n = true <;> simp [q, hn]
  have hsplit : ∀ n : ℕ, p n + q n = dottieSmoothTerm w n := by
    intro n
    by_cases hn : dottieRetainedNorm n = true <;> simp [p, q, hn]
  have hsum : dottieRetained w + dottieOmitted w =
      archivedMellin w/(archivedDottieCompletionScale : ℂ) := by
    change (∑' n, p n) + (∑' n, q n) = _
    rw [← hp.tsum_add hq, tsum_congr hsplit, hfull.tsum_eq]
  rw [← hsum]
  abel

/-- The ring test with the exact reference and explicit omitted intervals
used by the archived smoothed calculation. -/
theorem dottie_ring_zero_free_of_explicit_tail
    (hS : 0 < dottieCircleReference)
    (habs : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      Summable (fun n => ‖dottieSmoothTerm w n‖))
    (hfull : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      HasSum (dottieSmoothTerm w) (archivedMellin w/(archivedDottieCompletionScale : ℂ)))
    (model : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieRetained w).im ≤ -(190*((w.re-1/2)*dottieCircleReference)))
    (tail : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieOmitted w).im ≤ 189*((w.re-1/2)*dottieCircleReference))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) :
    archivedGaussianFactor w ≠ 0 ∧ archivedGaussianFactor (1-conj w) ≠ 0 := by
  refine archivedDottieRing_zero_free_of_replay hS dottieRetained model ?_ hw
  intro z hz
  rw [dottie_normalized_remainder_eq_omitted (habs z hz) (hfull z hz)]
  exact tail z hz

#print axioms dottie_normalized_remainder_eq_omitted
#print axioms dottieContourIntegrand_integrable
#print axioms dottie_ring_zero_free_of_explicit_tail

end QuarticModel
