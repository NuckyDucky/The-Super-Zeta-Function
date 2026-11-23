import QuarticSlope
import QuarticCertificateFromCells

open MeasureTheory Set GaussianSideIntegral

namespace QuarticKernel

private theorem poly_antitone_extended :
    AntitoneOn QuarticSlope.lowerPoly (Icc (0:ℝ) (87/20)) := by
  let P (x : ℝ) := -x*(44697+20348*(19-x^2)+1902*(19-x^2)^2+
    12*(19-x^2)^3+(19-x^2)^4)/3991680
  have hd (x : ℝ) : HasDerivAt QuarticSlope.lowerPoly (P x) x := by
    unfold QuarticSlope.lowerPoly
    have h := hasDerivAt_id x
    convert (((((hasDerivAt_const x (1:ℝ)).sub ((h.pow 2).div_const 6)).add
      ((h.pow 4).div_const 120)).sub ((h.pow 6).div_const 5040)).add
      ((h.pow 8).div_const 362880)).sub ((h.pow 10).div_const 39916800) using 1
    simp [id, P]
    ring
  have hh : Differentiable ℝ QuarticSlope.lowerPoly := fun x => (hd x).differentiableAt
  refine antitoneOn_of_deriv_nonpos (convex_Icc 0 _) hh.continuous.continuousOn
    hh.differentiableOn fun x hx => ?_
  rw [(hd x).deriv]
  have h := interior_subset hx
  have hx0 : 0 ≤ x := h.1
  have hx1 : x ≤ 87/20 := h.2
  have hx2 : 0 ≤ 19-x^2 := by
    have hb := pow_le_pow_left₀ hx0 hx1 2
    nlinarith only [hb]
  unfold P
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx0)
    (by positivity)) (by norm_num)

theorem sinc_global_floor (x : ℝ) : -(23/100:ℝ) ≤ sinc x := by
  rw [← QuarticSlope.sinc_abs x]
  by_cases h : |x| ≤ 87/20
  · exact (by norm_num [QuarticSlope.lowerPoly] :
      -(23/100:ℝ) ≤ QuarticSlope.lowerPoly (87/20)).trans
      ((poly_antitone_extended ⟨abs_nonneg x,h⟩ ⟨by norm_num, le_rfl⟩ h).trans
        (QuarticSlope.poly_le_sinc (abs_nonneg x)))
  · have hu : 0 < |x| := (by norm_num : (0:ℝ) < 87/20).trans (lt_of_not_ge h)
    rw [sinc, if_neg hu.ne']
    apply (le_div_iff₀ hu).2
    linarith only [lt_of_not_ge h, Real.neg_one_le_sin |x|]

/-- Only the negative part of the sine weight can reduce the reading
under the horizontal deformation. -/
private theorem sharp_slope {K : ℝ → ℝ} {Λ : ℂ → ℂ}
    (cert : GaussianSideSign.Certificate Λ K) {a t : ℝ} (ha : |a| ≤ 1/20)
    (ht : |t| ≤ 27/100) : 400000 < GaussianSideIntegral.slope K a t := by
  let m := GaussianSideSign.mass K
  let v := fun x : ℝ => sinc (t*x)
  let c := fun x : ℝ => GaussianSideError.averageCosh (a*x)
  let diff := fun x : ℝ => m x * v x - m x * v x * c x
  have hcEq (x) : c x = sinhc (a*x) := GaussianSideError.averageCosh_eq _
  have hmass (x : ℝ) (hx : x ∈ Ici 0) : 0 ≤ m x := by
    change 0 ≤ 2*K x*x^2
    exact mul_nonneg (mul_nonneg (by norm_num) (cert.kernel_nonneg x hx)) (sq_nonneg _)
  have hcore : Icc (0:ℝ) 18 ⊆ Ici 0 := fun _ hx => hx.1
  have htail : Ioi (18:ℝ) ⊆ Ici 0 := fun _ hx => (by norm_num : (0:ℝ) ≤ 18).trans hx.le
  have hside : IntegrableOn (fun x => m x*v x*c x) (Ici 0) := by
    simp only [hcEq,v,m]
    exact cert.slope_integrable a t ha ht
  have hdiff : IntegrableOn diff (Ici 0) := (cert.base_integrable t ht).sub hside
  have hmI : IntegrableOn m (Ici 0) := cert.mass_integrable
  have hdebt (x : ℝ) (hx : 0 ≤ x) :
      diff x ≤ m x * ((23/100:ℝ)*(c x-1)) := by
    have h₁ : 0 ≤ c x - 1 := sub_nonneg.mpr (GaussianSideError.one_le_averageCosh _)
    have h := mul_le_mul_of_nonneg_right (neg_le_neg (sinc_global_floor (t*x))) h₁
    have HD : diff x = m x*((-v x)*(c x-1)) := by dsimp [diff]; ring
    rw [HD]
    exact mul_le_mul_of_nonneg_left (by simpa only [v,neg_neg] using h) (hmass x hx)
  have hend : GaussianSideError.averageCosh (9/10) ≤ 11407/10000 := by
    rw [GaussianSideError.averageCosh_eq, if_neg (by norm_num)]
    linarith [GaussianSideConstants.sinh_ratio]
  have hcost : (∫ x in Icc 0 18, diff x) ≤ (23/100*(1407/10000):ℝ) *
      (∫ x in Icc 0 18, m x) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hdiff.mono_set hcore) ((hmI.mono_set hcore).const_mul _) measurableSet_Icc
    intro x hx
    have ha' : |a*x| ≤ |(9/10:ℝ)| := by
      rw [abs_mul,abs_of_nonneg hx.1,abs_of_pos (by norm_num : (0:ℝ) < 9/10)]
      linarith only [mul_le_mul_of_nonneg_right ha hx.1,hx.2]
    have hc := (GaussianSideError.averageCosh_abs_mono ha').trans hend
    have hc' : c x-1 ≤ 1407/10000 := by dsimp [c]; linarith only [hc]
    refine (hdebt x hx.1).trans ?_
    rw [mul_comm _ (m x)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc' (by norm_num)) (hmass x hx.1)
  have hmeas := (hmI.mono_set htail).aestronglyMeasurable
  have hE : Continuous (fun x : ℝ => Real.exp (x/20)) :=
    Real.continuous_exp.comp (continuous_id.div_const _)
  obtain ⟨hTI,hTB⟩ := GaussianSideError.tail_of_kernel_majorant
    (fun x hx => cert.kernel_nonneg x (htail hx)) cert.theta_tail
    (hmeas.mul hE.aestronglyMeasurable)
  have hfar : (∫ x in Ioi 18, diff x) ≤ ∫ x in Ioi 18, m x * Real.exp (x/20) := by
    apply setIntegral_mono_on (hdiff.mono_set htail) hTI measurableSet_Ioi
    intro x hx
    have hx0 : 0 ≤ x := htail hx
    have ha' : |a*x| ≤ x/20 := by
      rw [abs_mul,abs_of_nonneg hx0]
      linarith only [mul_le_mul_of_nonneg_right ha hx0]
    have he := (GaussianSideError.averageCosh_le_exp_abs (a*x)).trans (Real.exp_le_exp.mpr ha')
    have he' : (23/100:ℝ)*(c x-1) ≤ Real.exp (x/20) := by
      dsimp [c]
      linarith only [he,Real.exp_pos (x/20)]
    exact (hdebt x hx0).trans (mul_le_mul_of_nonneg_left he' (hmass x hx0))
  have hm : ∫ x in Icc 0 18, m x ≤ ∫ x in Ici 0, m x :=
    setIntegral_mono_set hmI ((ae_restrict_iff' measurableSet_Ici).mpr
      (Filter.Eventually.of_forall hmass)) hcore.eventuallyLE
  have hdis : Disjoint (Icc (0:ℝ) 18) (Ioi 18) :=
    Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy)
  have hsplit := setIntegral_union hdis measurableSet_Ioi (hdiff.mono_set hcore) (hdiff.mono_set htail)
  rw [Icc_union_Ioi_eq_Ici (by norm_num : (0:ℝ) ≤ 18)] at hsplit
  have htotal : (∫ x in Ici 0, diff x) = (∫ x in Ici 0, m x * v x) -
      (∫ x in Ici 0, m x * v x * c x) := integral_sub (cert.base_integrable t ht) hside
  have hl := cert.line_floor t ht
  have hcurv := cert.curvature
  have hh : 400000 < ∫ x in Ici 0, m x*v x*c x := by
    change (519994:ℝ) < ∫ x in Ici 0, m x*v x at hl
    change (∫ x in Ici 0, m x) ≤ 3565602 at hcurv
    change (∫ x in Ioi 18, m x*Real.exp (x/20)) < 1/10^10 at hTB
    linarith only [hcost,hfar,hm,hsplit,htotal,hl,hcurv,hTB]
  simpa only [hcEq,m,v,GaussianSideSign.mass,GaussianSideIntegral.slope] using hh

theorem sharp_quantitative_reading {Λ K} (cert : GaussianSideSign.Certificate Λ K) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) :
    (Λ (GaussianSideSign.point a t)).im = a*t*GaussianSideIntegral.slope K a t ∧
      400000 < GaussianSideIntegral.slope K a t :=
  ⟨(GaussianSideSign.quantitative_reading cert ha ht).1, sharp_slope cert ha ht⟩

#print axioms sinc_global_floor
#print axioms sharp_quantitative_reading

end QuarticKernel
