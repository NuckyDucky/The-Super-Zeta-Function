import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Scalar Stieltjes formula used in the spectral contour deformation. -/
noncomputable section
namespace SuperZeta.Stieltjes
open Complex MeasureTheory Set
open Filter Metric
open scoped Topology

/-- The reciprocal resolvent for a single eigenvalue. -/
def integrand (s z : ℂ) (t : ℝ) : ℂ := (t:ℂ)^(-s)/((t:ℂ)+z)

private def compactify (x : ℝ) := (1+x)⁻¹
private def jac (x : ℝ) := -(1/(1+x)^2)

private theorem compactify_deriv (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) :
    HasDerivWithinAt compactify (jac x) (Ioi 0) x := by
  have h := ((hasDerivAt_id x).const_add 1).inv (by dsimp; linarith [mem_Ioi.mp hx])
  simpa [compactify,jac,neg_div] using h.hasDerivWithinAt (s:=Ioi 0)

private theorem compactify_inj : InjOn compactify (Ioi (0:ℝ)) := by
  intro x _ y _ h
  exact add_left_cancel (inv_injective h)

private theorem compactify_image : compactify '' Ioi 0 = Ioo 0 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' := mem_Ioi.mp ht
    exact ⟨by unfold compactify; positivity, by unfold compactify; exact inv_lt_one_of_one_lt₀ (by linarith)⟩
  · rintro ⟨hx, hx'⟩
    refine ⟨x⁻¹-1, ?_, ?_⟩
    · change 0 < x⁻¹-1
      exact sub_pos.mpr ((one_lt_inv₀ hx).mpr hx')
    · simp [compactify]

private def betaTerm (s : ℂ) (x : ℝ) : ℂ := (x:ℂ)^(s-1)*(1-(x:ℂ))^(-s)

private theorem transformed (s : ℂ) {x : ℝ} (hx : x ∈ Ioi (0:ℝ)) :
    |jac x| • betaTerm s (compactify x) = integrand s 1 x := by
  have hx' := mem_Ioi.mp hx
  let a := compactify x
  have ha : 0<a := by dsimp [a,compactify]; positivity
  have hxa : 1-(a:ℂ) = (x:ℂ)*(a:ℂ) := by
    dsimp [a,compactify]
    push_cast
    have h : (1:ℂ)+x ≠ 0 := by exact_mod_cast (show (1:ℝ)+x≠0 by linarith)
    field_simp
  have hj : |jac x| = a^2 := by
    simp [jac,a,compactify,abs_of_nonneg (by positivity : 0 ≤ (1:ℝ)/(1+x)^2), inv_pow]
    positivity
  have hne : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hpow : (a:ℂ)^(s-1)*(a:ℂ)^(-s)=(a:ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hne, show s-1+-s = -1 by ring, Complex.cpow_neg_one]
  change |jac x| • ((a:ℂ)^(s-1)*(1-(a:ℂ))^(-s)) = _
  rw [hj, Complex.real_smul, Complex.ofReal_pow, hxa, Complex.mul_cpow_ofReal_nonneg hx'.le ha.le]
  calc
    _ = (a:ℂ)^2*((a:ℂ)^(s-1)*(a:ℂ)^(-s))*(x:ℂ)^(-s) := by ring
    _ = (a:ℂ)*(x:ℂ)^(-s) := by rw [hpow]; field_simp; ring
    _ = _ := by simp [integrand, a, compactify, div_eq_mul_inv, add_comm, mul_comm]

/-- Absolute convergence and Euler's beta evaluation for the unit eigenvalue. -/
theorem unit_integral {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    IntegrableOn (integrand s 1) (Ioi 0) ∧
    (∫ t in Ioi (0:ℝ), integrand s 1 t) = (Real.pi:ℂ)/Complex.sin ((Real.pi:ℂ)*s) := by
  have h1 : 0 < (1-s).re := by simp; linarith
  have hb := betaIntegral_convergent hs h1
  have hbi : IntegrableOn (betaTerm s) (Ioo (0:ℝ) 1) := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo, ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa [betaTerm, show (1-s)-1 = -s by ring] using hb
  have hg := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    compactify_deriv compactify_inj (betaTerm s))
  rw [compactify_image] at hg
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    compactify_deriv compactify_inj (betaTerm s)
  rw [compactify_image] at hi
  refine ⟨(hg.mp hbi).congr_fun (fun _ hx => transformed s hx) measurableSet_Ioi, ?_⟩
  have he : betaIntegral s (1-s) = (∫ t in Ioi (0:ℝ), integrand s 1 t) := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    simp only [show 1-s-1 = -s by ring]
    change (∫ x in Ioo (0:ℝ) 1, betaTerm s x) = _
    rw [hi]
    exact setIntegral_congr_fun measurableSet_Ioi (fun _ hx => transformed s hx)
  have hG := Gamma_mul_Gamma_eq_betaIntegral hs h1
  rw [show s+(1-s)=1 by ring, Gamma_one, one_mul, Gamma_mul_Gamma_one_sub] at hG
  exact he.symm.trans hG.symm

private theorem dilation {l x : ℝ} (hl : 0 < l) (hx : 0 < x) (s : ℂ) :
    integrand s (l:ℂ) (l*x) = ((l:ℂ)^(-s)/(l:ℂ))*integrand s 1 x := by
  unfold integrand
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hl.le hx.le, ← mul_add_one]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A single positive eigenvalue, with its principal power, throughout the
full complex convergence strip. -/
theorem positive_integral {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) {l : ℝ} (hl : 0 < l) :
    IntegrableOn (integrand s (l:ℂ)) (Ioi 0) ∧
    Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ)*(∫ t in Ioi (0:ℝ), integrand s (l:ℂ) t) =
      (l:ℂ)^(-s) := by
  obtain ⟨hi, he⟩ := unit_integral hs hs'
  have hscale : EqOn (fun t => integrand s (l:ℂ) (l*t))
      (fun t => ((l:ℂ)^(-s)/(l:ℂ))*integrand s 1 t) (Ioi 0) := fun x hx => dilation hl hx s
  have hf := IntegrableOn.congr_fun (hi.const_mul ((l:ℂ)^(-s)/(l:ℂ))) hscale.symm measurableSet_Ioi
  have hInt := (integrableOn_Ioi_comp_mul_left_iff (integrand s (l:ℂ)) 0 hl).mp hf
  rw [mul_zero] at hInt
  refine ⟨hInt, ?_⟩
  have h := integral_comp_mul_left_Ioi (integrand s (l:ℂ)) 0 hl
  rw [mul_zero, setIntegral_congr_fun measurableSet_Ioi hscale,
    integral_const_mul, he, Complex.real_smul, Complex.ofReal_inv] at h
  have hpi : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hl' : (l:ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have hsin : Complex.sin ((Real.pi:ℂ)*s) ≠ 0 := by
    intro hz
    have hag := Complex.Gamma_mul_Gamma_one_sub s
    rw [hz, div_zero] at hag
    exact (mul_ne_zero (Gamma_ne_zero_of_re_pos hs)
      (Gamma_ne_zero_of_re_pos (by simp; linarith))) hag
  field_simp [hl', hpi, hsin] at h ⊢
  apply mul_right_cancel₀ hl'
  linear_combination -h

/-- The argument counts repeated eigenvalues separately via their indices. -/
theorem finite_positive {ι : Type*} (I : Finset ι) (l : ι → ℝ)
    (hl : ∀ j ∈ I, 0 < l j) {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ)*
      (∫ t in Ioi (0:ℝ), ∑ j ∈ I, integrand s (l j:ℂ) t) = ∑ j ∈ I, (l j:ℂ)^(-s) := by
  rw [integral_finset_sum I (fun j hj => (positive_integral hs hs' (hl j hj)).1),
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun j hj => (positive_integral hs hs' (hl j hj)).2

/-- Every slit-plane eigenvalue has a neighborhood with uniform domination
by the unit-eigenvalue resolvent on the entire integration ray. -/
theorem resolvent_bound {z : ℂ} (hz : z ∈ slitPlane) :
    ∃ r K : ℝ, 0 < r ∧ 0 < K ∧ ∀ w ∈ ball z r, ∀ t : ℝ, 0 ≤ t →
      r ≤ ‖(t:ℂ)+w‖ ∧ 1+t ≤ K*‖(t:ℂ)+w‖ := by
  obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp Complex.isOpen_slitPlane z hz
  let r := d/2
  have hr : 0 < r := by dsimp [r]; linarith
  let M := ‖z-1‖+r
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨r, 1+M/r, hr, by positivity, ?_⟩
  intro w hw t ht
  have hwz : ‖w-z‖ < r := by simpa [mem_ball,dist_eq_norm] using hw
  have hdt : d ≤ ‖(t:ℂ)+z‖ := by
    by_contra! h
    have hdist : dist (-(t:ℂ)) z = ‖(t:ℂ)+z‖ := by rw [dist_eq_norm, ← neg_add', norm_neg]
    have hm : -(t:ℂ) ∈ slitPlane := hball (by simpa [mem_ball,hdist] using h)
    exact (not_lt_of_ge ht) (Complex.neg_ofReal_mem_slitPlane.mp hm)
  have htri : ‖(t:ℂ)+z‖ ≤ ‖(t:ℂ)+w‖+‖w-z‖ := by
    calc
      _ = ‖((t:ℂ)+w)-(w-z)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  have hwr : r ≤ ‖(t:ℂ)+w‖ := by dsimp [r] at *; linarith
  have hMbound : ‖1-w‖ ≤ M := by
    calc
      _ = ‖-((z-1)+(w-z))‖ := by congr 1; ring
      _ ≤ _ := by rw [norm_neg]; exact (norm_add_le _ _).trans (add_le_add_left hwz.le _)
  have htr : 1+t ≤ ‖(t:ℂ)+w‖+M := by
    have h := norm_add_le ((t:ℂ)+w) (1-w)
    have hh : (t:ℂ)+w+(1-w) = ((1+t:ℝ):ℂ) := by push_cast; ring
    rw [hh, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)] at h
    linarith
  refine ⟨hwr, htr.trans ?_⟩
  rw [add_mul, one_mul]
  exact add_le_add_left (by
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    exact mul_le_mul_of_nonneg_left hwr hM) _

private def integrandDeriv (s z : ℂ) (t : ℝ) : ℂ := -(t:ℂ)^(-s)/((t:ℂ)+z)^2

private theorem numerator_meas (s : ℂ) : AEStronglyMeasurable
    (fun x : ℝ => (x:ℂ)^(-s)) (volume.restrict (Ioi 0)) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  exact fun x hx => (continuousAt_ofReal_cpow_const x (-s) (Or.inr hx.ne')).continuousWithinAt

private theorem value_meas (s z : ℂ) :
    AEStronglyMeasurable (integrand s z) (volume.restrict (Ioi 0)) := by
  have hden : Continuous (fun t : ℝ => (t:ℂ)+z) := Complex.continuous_ofReal.add continuous_const
  exact ((numerator_meas s).aemeasurable.div hden.aemeasurable).aestronglyMeasurable

private theorem norm_bounds {r K t : ℝ} {s z : ℂ} (hr : 0<r) (ht : 0 ≤ t)
    (h1 : r ≤ ‖(t:ℂ)+z‖) (h2 : 1+t ≤ K*‖(t:ℂ)+z‖) :
    ‖integrand s z t‖ ≤ K*‖integrand s 1 t‖ ∧
      ‖integrandDeriv s z t‖ ≤ (K/r)*‖integrand s 1 t‖ := by
  have hd := hr.trans_le h1
  have hu : ‖(t:ℂ)+1‖ = 1+t := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith),add_comm]
  have hu' : 0 < 1+t := by linarith
  have hk : ‖(t:ℂ)^(-s)‖/‖(t:ℂ)+z‖ ≤ K*(‖(t:ℂ)^(-s)‖/(1+t)) := by
    rw [← mul_div_assoc, div_le_div_iff₀ hd hu']
    nlinarith only [mul_le_mul_of_nonneg_left h2 (norm_nonneg ((t:ℂ)^(-s)))]
  simp only [integrand,integrandDeriv,norm_div,norm_neg,norm_pow,hu]
  refine ⟨hk, ?_⟩
  calc
    _ = (‖(t:ℂ)^(-s)‖/‖(t:ℂ)+z‖)/‖(t:ℂ)+z‖ := by rw [div_div, sq]
    _ ≤ (K*(‖(t:ℂ)^(-s)‖/(1+t)))/r :=
      div_le_div₀ ((div_nonneg (norm_nonneg _) hd.le).trans hk) hk hr h1
    _ = _ := by ring

private theorem slit_differentiable {s z : ℂ} (hs : 0 < s.re) (hs' : s.re < 1)
    (hz : z ∈ slitPlane) : IntegrableOn (integrand s z) (Ioi 0) ∧
      DifferentiableAt ℂ (fun w => ∫ t in Ioi (0:ℝ), integrand s w t) z := by
  obtain ⟨r,K,hr,hK,hb⟩ := resolvent_bound hz
  have hi := (unit_integral hs hs').1
  have hB (w : ℂ) (hw : w ∈ ball z r) (t : ℝ) (ht : 0<t) :=
    norm_bounds (s:=s) hr ht.le (hb w hw t ht.le).1 (hb w hw t ht.le).2
  have hInt : IntegrableOn (integrand s z) (Ioi 0) := by
    apply (hi.norm.const_mul K).mono' (value_meas s z)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hB z (mem_ball_self hr) t ht).1
  refine ⟨hInt, ?_⟩
  have hdm : AEStronglyMeasurable (integrandDeriv s z) (volume.restrict (Ioi 0)) := by
    have hden : Continuous (fun t : ℝ => ((t:ℂ)+z)^2) :=
      (Complex.continuous_ofReal.add continuous_const).pow 2
    exact ((numerator_meas s).aemeasurable.neg.div hden.aemeasurable).aestronglyMeasurable
  have hg := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := integrand s)
    (F' := integrandDeriv s) (bound := fun t => (K/r)*‖integrand s 1 t‖)
    hr (Eventually.of_forall (value_meas s)) hInt hdm (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact fun w hw => (hB w hw t ht).2) (hi.norm.const_mul (K/r)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro w hw
      have hn : (t:ℂ)+w ≠ 0 := norm_pos_iff.mp (hr.trans_le (hb w hw t (mem_Ioi.mp ht).le).1)
      have h := (hasDerivAt_const w ((t:ℂ)^(-s))).div
        ((hasDerivAt_id w).const_add (t:ℂ)) hn
      simpa [integrand,integrandDeriv] using h)
  exact hg.2.differentiableAt

/-- The full principal-cut scalar Stieltjes formula, including the nonreal
eigenvalues that occur in a reflected quartet. -/
theorem slit_integral {s z : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) (hz : z ∈ slitPlane) :
    IntegrableOn (integrand s z) (Ioi 0) ∧
    Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ)*(∫ t in Ioi (0:ℝ), integrand s z t) = z^(-s) := by
  let F (w : ℂ) := Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ)*(∫ t in Ioi (0:ℝ), integrand s w t)
  have hF : DifferentiableOn ℂ F slitPlane := fun w hw =>
    ((slit_differentiable hs hs' hw).2.const_mul _).differentiableWithinAt
  have hg : DifferentiableOn ℂ (fun w : ℂ => w^(-s)) slitPlane :=
    fun w hw => (differentiableAt_id.cpow_const hw).differentiableWithinAt
  have hc : IsPreconnected slitPlane := by
    apply isPreconnected_of_forall (1:ℂ)
    intro w hw
    exact ⟨segment ℝ 1 w, Complex.starConvex_one_slitPlane.segment_subset hw,
      left_mem_segment .., right_mem_segment .., (convex_segment ..).isPreconnected⟩
  refine ⟨(slit_differentiable hs hs' hz).1, ?_⟩
  apply (hF.analyticOnNhd Complex.isOpen_slitPlane).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd Complex.isOpen_slitPlane) hc (z₀:=1) Complex.one_mem_slitPlane _ hz
  have hreal : ∃ᶠ (x : ℝ) in 𝓝[≠] (1:ℝ), F (x:ℂ) = (x:ℂ)^(-s) := by
    apply Eventually.frequently
    filter_upwards [(eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono
      (nhdsWithin_le_nhds (s:={(1:ℝ)}ᶜ))] with x hx
    exact (positive_integral hs hs' hx).2
  rw [frequently_iff_seq_forall] at hreal ⊢
  obtain ⟨xs, hx, he⟩ := hreal
  refine ⟨fun n => (xs n:ℂ), ?_, he⟩
  rw [tendsto_nhdsWithin_iff] at hx ⊢
  exact ⟨by simpa using Complex.continuous_ofReal.continuousAt.tendsto.comp hx.1,
    by simpa using hx.2⟩

theorem finite_slit {ι : Type*} (I : Finset ι) (l : ι → ℂ) (hl : ∀ j ∈ I, l j ∈ slitPlane)
    {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1) :
    Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ)*
      (∫ t in Ioi (0:ℝ), ∑ j ∈ I, integrand s (l j) t) = ∑ j ∈ I, (l j)^(-s) := by
  rw [integral_finset_sum I (fun j hj => (slit_integral hs hs' (hl j hj)).1), Finset.mul_sum]
  exact Finset.sum_congr rfl fun j hj => (slit_integral hs hs' (hl j hj)).2

/-- Dilation gives the exact L¹ scaling needed for a countable spectrum. -/
theorem positive_norm_integral (s : ℂ) {l : ℝ} (hl : 0 < l) :
    (∫ t in Ioi (0:ℝ), ‖integrand s (l:ℂ) t‖) =
      l^(-s.re)*(∫ t in Ioi (0:ℝ), ‖integrand s 1 t‖) := by
  have hscale : EqOn (fun t => ‖integrand s (l:ℂ) (l*t)‖)
      (fun t => (l^(-s.re)/l)*‖integrand s 1 t‖) (Ioi 0) := by
    intro t ht
    dsimp only
    rw [dilation hl ht s,norm_mul,norm_div,Complex.norm_of_nonneg hl.le,
      Complex.norm_cpow_eq_rpow_re_of_pos hl,Complex.neg_re]
  have h := integral_comp_mul_left_Ioi (fun t => ‖integrand s (l:ℂ) t‖) 0 hl
  rw [mul_zero, setIntegral_congr_fun measurableSet_Ioi hscale,
    integral_const_mul, smul_eq_mul] at h
  field_simp [hl.ne'] at h
  linear_combination -h

/-- The sector condition controls every resolvent on the integration ray
by the positive resolvent at the same modulus. -/
theorem sector_norm_integral {s z : ℂ} (hs : 0 < s.re) (hs' : s.re < 1)
    (hz : z ∈ slitPlane) {d : ℝ} (hd : 0 < d)
    (margin : ∀ t : ℝ, 0 ≤ t → d*(t+‖z‖) ≤ ‖(t:ℂ)+z‖) :
    (∫ t in Ioi (0:ℝ), ‖integrand s z t‖) ≤
      (d⁻¹*(∫ t in Ioi (0:ℝ), ‖integrand s 1 t‖))*‖z‖^(-s.re) := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  have hi := (positive_integral hs hs' hz').1.norm.const_mul d⁻¹
  have hle : (∫ t in Ioi (0:ℝ), ‖integrand s z t‖) ≤
      ∫ t in Ioi (0:ℝ), d⁻¹*‖integrand s (‖z‖:ℂ) t‖ := by
    apply integral_mono_ae (slit_integral hs hs' hz).1.norm hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' := mem_Ioi.mp ht
    have hm := margin t ht'.le
    have hp : 0 < t+‖z‖ := by positivity
    have hh : 0 < ‖(t:ℂ)+z‖ := (mul_pos hd hp).trans_le hm
    have hn : ‖(t:ℂ)+(‖z‖:ℂ)‖ = t+‖z‖ := by
      rw [← Complex.ofReal_add,Complex.norm_of_nonneg hp.le]
    simp only [integrand,norm_div,hn]
    rw [← mul_div_assoc, div_le_div_iff₀ hh hp]
    have hb := mul_le_mul_of_nonneg_left hm (norm_nonneg ((t:ℂ)^(-s)))
    rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hd]
    nlinarith only [hb]
  rw [integral_const_mul, positive_norm_integral s hz'] at hle
  convert hle using 1
  ring

/-- Countably many eigenvalues with their full multiplicities. Absolute
spectral summability and a common sector margin suffice for interchange. -/
theorem countable_slit {ι : Type*} [Countable ι] (l : ι → ℂ)
    (hl : ∀ j, l j ∈ slitPlane) {s : ℂ} (hs : 0 < s.re) (hs' : s.re < 1)
    {d : ℝ} (hd : 0 < d) (margin : ∀ j (t : ℝ), 0 ≤ t → d*(t+‖l j‖) ≤ ‖(t:ℂ)+l j‖)
    (hseries : Summable fun j => ‖l j‖^(-s.re)) :
    HasSum (fun j => (l j)^(-s))
      (Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ)*
        ∫ t in Ioi (0:ℝ), (t:ℂ)^(-s)*(∑' j, ((t:ℂ)+l j)⁻¹)) := by
  have hL : Summable (fun j => ∫ t in Ioi (0:ℝ), ‖integrand s (l j) t‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (fun j => sector_norm_integral hs hs' (hl j) hd (margin j)) (hseries.mul_left _)
  have he := hasSum_integral_of_summable_integral_norm
    (fun j => (slit_integral hs hs' (hl j)).1) hL
  have h := he.mul_left (Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ))
  simp_rw [(slit_integral hs hs' (hl _)).2] at h
  simpa only [integrand, div_eq_mul_inv, tsum_mul_left] using h

end SuperZeta.Stieltjes
