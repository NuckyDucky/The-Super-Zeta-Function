import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Weighted circle integrals for two enclosed zeros of an analytic function. -/

namespace SuperZeta.TwoRootCircleIntegral
open Complex Filter Metric Set
open scoped Real Topology
noncomputable section

/-- An analytic zero of order two has vanishing ordinary derivative. -/
theorem deriv_eq_zero_of_order_two {f : ℂ → ℂ} {a : ℂ} (hf : AnalyticAt ℂ f a)
    (h₂ : hf.order = 2) : deriv f a = 0 := by
  obtain ⟨g, hg, _, he⟩ := (hf.order_eq_nat_iff (n := 2)).mp (by simpa using h₂)
  have he' : f =ᶠ[𝓝 a] fun z => (z - a)^2 * g z := by simpa [smul_eq_mul] using he
  have hd := ((((hasDerivAt_id a).sub_const a).pow 2).mul hg.differentiableAt.hasDerivAt)
  have hd' : HasDerivAt (fun z : ℂ => (z - a)^2 * g z) 0 a := by simpa using hd
  exact (hd'.congr_of_eventuallyEq he').deriv

private theorem logDeriv_two_factors {a b z : ℂ} {g : ℂ → ℂ} (hg : DifferentiableAt ℂ g z)
    (ha : z ≠ a) (hb : z ≠ b) (hg₀ : g z ≠ 0) :
    logDeriv (fun w => (w - a) * (w - b) * g w) z =
      (z - a)⁻¹ + (z - b)⁻¹ + deriv g z / g z := by
  have hd := (((hasDerivAt_id z).sub_const a).mul ((hasDerivAt_id z).sub_const b)).mul
    hg.hasDerivAt
  simp only [id_eq] at hd
  rw [logDeriv_apply, hd.deriv]
  field_simp [sub_ne_zero.mpr ha, sub_ne_zero.mpr hb, hg₀]
  ring

/-- Cauchy's integral formula recovers both point evaluations, including multiplicity
when the two roots coincide. The factor g may have zeros elsewhere in the plane. -/
theorem circleIntegral_weighted_logDeriv {a b c : ℂ} {R : ℝ} {g p : ℂ → ℂ}
    (ha : a ∈ ball c R) (hb : b ∈ ball c R) (hg : Differentiable ℂ g)
    (hg₀ : ∀ z ∈ closedBall c R, g z ≠ 0) (hp : Differentiable ℂ p) :
    (∮ z in C(c, R), p z * logDeriv (fun w => (w - a) * (w - b) * g w) z) =
      (2 * π * I : ℂ) * (p a + p b) := by
  have hR : 0 ≤ R := (lt_of_le_of_lt dist_nonneg (mem_ball.mp ha)).le
  have hne {r z : ℂ} (hr : r ∈ ball c R) (hz : z ∈ sphere c R) : z ≠ r := by
    rintro rfl
    exact (ne_of_lt (mem_ball.mp hr)) (mem_sphere.mp hz)
  let q (r z : ℂ) := (z - r)⁻¹ * p z
  let h (z : ℂ) := p z * (deriv g z / g z)
  have hq {r : ℂ} (hr : r ∈ ball c R) : CircleIntegrable (q r) c R := by
    apply ContinuousOn.circleIntegrable hR
    exact ((continuous_id.sub continuous_const).continuousOn.inv₀
      (fun z hz => sub_ne_zero.mpr (hne hr hz))).mul hp.continuous.continuousOn
  have hdg : Differentiable ℂ (deriv g) := differentiableOn_univ.mp
    (hg.differentiableOn.deriv isOpen_univ)
  have hhd {z : ℂ} (hz : z ∈ closedBall c R) : DifferentiableAt ℂ h z :=
    (hp z).mul ((hdg z).div (hg z) (hg₀ z hz))
  have hhc : ContinuousOn h (closedBall c R) :=
    fun z hz => (hhd hz).continuousAt.continuousWithinAt
  have hh : CircleIntegrable h c R :=
    ContinuousOn.circleIntegrable hR (hhc.mono sphere_subset_closedBall)
  have hi : (∮ z in C(c, R), h z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR countable_empty
      hhc (fun z hz => hhd (ball_subset_closedBall hz.1))
  have hc {r : ℂ} (hr : r ∈ ball c R) : (∮ z in C(c, R), q r z) =
      (2 * π * I : ℂ) * p r := by
    simpa [q, smul_eq_mul] using hp.differentiableOn.circleIntegral_sub_inv_smul hr
  calc
    _ = ∮ z in C(c, R), (q a z + q b z) + h z := by
      apply circleIntegral.integral_congr hR
      intro z hz
      change p z * logDeriv _ z = q a z + q b z + h z
      rw [logDeriv_two_factors (hg z) (hne ha hz) (hne hb hz)
        (hg₀ z (sphere_subset_closedBall hz))]
      dsimp [q, h]
      ring
    _ = _ := by
      have hs := circleIntegral.integral_add ((hq ha).add (hq hb)) hh
      simp only [Pi.add_apply] at hs
      rw [hs, circleIntegral.integral_add (hq ha) (hq hb), hc ha, hc hb, hi]
      ring

private theorem differentiable_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (r : ℂ) :
    Differentiable ℂ (dslope f r) :=
  differentiableOn_univ.mp ((Complex.differentiableOn_dslope (univ_mem : univ ∈ 𝓝 r)).mpr
    hf.differentiableOn)

/-- For an entire f, listing the two distinct simple zeros on the closed disk suffices.
Two applications of removable division construct the zero-free cofactor used above. -/
theorem circleIntegral_of_two_simple_zeros {f p : ℂ → ℂ} {a b c : ℂ} {R : ℝ}
    (hf : Differentiable ℂ f) (hp : Differentiable ℂ p) (ha : a ∈ ball c R)
    (hb : b ∈ ball c R) (hab : a ≠ b) (hfa : f a = 0) (hfb : f b = 0)
    (hda : deriv f a ≠ 0) (hdb : deriv f b ≠ 0)
    (hlist : ∀ z ∈ closedBall c R, f z = 0 → z = a ∨ z = b) :
    (∮ z in C(c, R), p z * logDeriv f z) = (2 * π * I : ℂ) * (p a + p b) := by
  let h := dslope f a
  let g := dslope h b
  have hh : Differentiable ℂ h := differentiable_dslope hf a
  have hg : Differentiable ℂ g := differentiable_dslope hh b
  have eh (z : ℂ) : (z - a) * h z = f z := by
    simpa [h, smul_eq_mul, hfa] using sub_smul_dslope f a z
  have hb₀ : h b = 0 := (mul_eq_zero.mp ((eh b).trans hfb)).resolve_left
    (sub_ne_zero.mpr hab.symm)
  have eg (z : ℂ) : (z - b) * g z = h z := by
    simpa [g, smul_eq_mul, hb₀] using sub_smul_dslope h b z
  have fac : (fun z => (z - a) * (z - b) * g z) = f := by
    funext z
    rw [mul_assoc, eg, eh]
  have hd := (((hasDerivAt_id b).sub_const a).mul (hh b).hasDerivAt)
  simp only [id_eq, hb₀, mul_zero, zero_add] at hd
  have ehf : (fun z => (z - a) * h z) = f := funext eh
  rw [ehf] at hd
  have hg₀ (z : ℂ) (hz : z ∈ closedBall c R) : g z ≠ 0 := by
    intro gz
    have fz : f z = 0 := by rw [← congrFun fac z]; simp [gz]
    rcases hlist z hz fz with rfl | rfl
    · apply hda
      rw [← dslope_same f z]
      change h z = 0
      rw [← eg z, gz, mul_zero]
    · apply hdb
      have hhz : deriv h z = 0 := by simpa [g, dslope_same] using gz
      rw [hd.deriv, hhz, mul_zero]
  have result := circleIntegral_weighted_logDeriv ha hb hg hg₀ hp
  rwa [fac] at result

/-- At a single enclosed zero of analytic order two, the same integral returns twice
the value of the test weight. The value of the second divided difference at the zero
is determined by continuity from the punctured neighborhood. -/
theorem circleIntegral_of_one_double_zero {f p : ℂ → ℂ} {a c : ℂ} {R : ℝ}
    (hf : Differentiable ℂ f) (hp : Differentiable ℂ p) (ha : a ∈ ball c R)
    (h₂ : (hf.analyticAt a).order = 2)
    (hlist : ∀ z ∈ closedBall c R, f z = 0 → z = a) :
    (∮ z in C(c, R), p z * logDeriv f z) = (2 * π * I : ℂ) * (p a + p a) := by
  obtain ⟨u, hu, hu₀, he⟩ := ((hf.analyticAt a).order_eq_nat_iff (n := 2)).mp
    (by simpa using h₂)
  have hfa : f a = 0 := by simpa using he.self_of_nhds
  let h := dslope f a
  let g := dslope h a
  have hg : Differentiable ℂ g := differentiable_dslope (differentiable_dslope hf a) a
  have hha : h a = 0 := by
    simpa [h, dslope_same] using deriv_eq_zero_of_order_two (hf.analyticAt a) h₂
  have eh (z : ℂ) : (z - a) * h z = f z := by
    simpa [h, smul_eq_mul, hfa] using sub_smul_dslope f a z
  have eg (z : ℂ) : (z - a) * g z = h z := by
    simpa [g, smul_eq_mul, hha] using sub_smul_dslope h a z
  have fac : (fun z => (z - a) * (z - a) * g z) = f := by
    funext z
    rw [mul_assoc, eg, eh]
  have hqu : g =ᶠ[𝓝[≠] a] u := by
    filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hza
    have hn := sub_ne_zero.mpr (show z ≠ a from hza)
    apply mul_left_cancel₀ (mul_ne_zero hn hn)
    simpa [pow_two, smul_eq_mul] using (congrFun fac z).trans hz
  have hua : g a = u a := tendsto_nhds_unique
    ((hg a).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    ((hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' hqu.symm)
  have hg₀ (z : ℂ) (hz : z ∈ closedBall c R) : g z ≠ 0 := by
    intro gz
    have fz : f z = 0 := by rw [← congrFun fac z]; simp [gz]
    have hza := hlist z hz fz
    exact hu₀ (hua.symm.trans (hza ▸ gz))
  have result := circleIntegral_weighted_logDeriv ha ha hg hg₀ hp
  rwa [fac] at result

/-- The four signed coordinate distances to the sides are positive in the interior. -/
def rectangleMargin (left right bottom top : ℝ) (z : ℂ) : ℝ :=
  min (min (z.re - left) (right - z.re)) (min (z.im - bottom) (top - z.im))

/-- A continuously followed solution that leaves a rectangle attains its target on
one of the four closed edge segments at a strictly intermediate time. -/
theorem solution_meets_rectangle_edge {f : ℂ → ℂ} {w : ℝ → ℂ} {v : ℝ → ℂ}
    {t₀ t₁ left right bottom top : ℝ} (ht : t₀ < t₁)
    (hw : ContinuousOn w (Icc t₀ t₁))
    (hsol : ∀ t ∈ Icc t₀ t₁, f (w t) = v t)
    (hin : (left < (w t₀).re ∧ (w t₀).re < right) ∧
      (bottom < (w t₀).im ∧ (w t₀).im < top))
    (hout : ((w t₁).re < left ∨ right < (w t₁).re) ∨
      ((w t₁).im < bottom ∨ top < (w t₁).im)) :
    ∃ t ∈ Ioo t₀ t₁, f (w t) = v t ∧
      (w t).re ∈ Icc left right ∧ (w t).im ∈ Icc bottom top ∧
      ((w t).re = left ∨ (w t).re = right ∨ (w t).im = bottom ∨ (w t).im = top) := by
  let m (t : ℝ) := rectangleMargin left right bottom top (w t)
  have hcMargin : Continuous (rectangleMargin left right bottom top) :=
    ((Complex.continuous_re.sub continuous_const).min (continuous_const.sub Complex.continuous_re)).min
      ((Complex.continuous_im.sub continuous_const).min (continuous_const.sub Complex.continuous_im))
  have hm : ContinuousOn m (Icc t₀ t₁) := hcMargin.comp_continuousOn hw
  have hstart : 0 < m t₀ := by simpa [m, rectangleMargin, lt_min_iff, sub_pos] using hin
  have hfinish : m t₁ < 0 := by simpa [m, rectangleMargin, min_lt_iff, sub_neg] using hout
  obtain ⟨t, htime, hz⟩ := intermediate_value_Icc' ht.le hm
    (show (0 : ℝ) ∈ Icc (m t₁) (m t₀) from ⟨hfinish.le, hstart.le⟩)
  have htime' : t ∈ Ioo t₀ t₁ := by
    refine ⟨lt_of_le_of_ne htime.1 ?_, lt_of_le_of_ne htime.2 ?_⟩
    · rintro rfl
      exact (ne_of_gt hstart) hz
    · rintro rfl
      exact (ne_of_lt hfinish) hz
  have hc : ((w t).re ∈ Icc left right) ∧ ((w t).im ∈ Icc bottom top) := by
    simpa [m, rectangleMargin, le_min_iff, sub_nonneg, mem_Icc] using hz.ge
  refine ⟨t, htime', hsol t htime, hc.1, hc.2, ?_⟩
  by_cases hl : (w t).re = left
  · exact Or.inl hl
  by_cases hr' : (w t).re = right
  · exact Or.inr (Or.inl hr')
  by_cases hb' : (w t).im = bottom
  · exact Or.inr (Or.inr (Or.inl hb'))
  by_cases ht' : (w t).im = top
  · exact Or.inr (Or.inr (Or.inr ht'))
  have hpos : 0 < m t := by
    simp only [m, rectangleMargin, lt_min_iff, sub_pos]
    exact ⟨⟨lt_of_le_of_ne hc.1.1 (Ne.symm hl), lt_of_le_of_ne hc.1.2 hr'⟩,
      ⟨lt_of_le_of_ne hc.2.1 (Ne.symm hb'), lt_of_le_of_ne hc.2.2 ht'⟩⟩
  exact ((ne_of_gt hpos) hz).elim

end
end SuperZeta.TwoRootCircleIntegral

#print axioms SuperZeta.TwoRootCircleIntegral.deriv_eq_zero_of_order_two
#print axioms SuperZeta.TwoRootCircleIntegral.circleIntegral_weighted_logDeriv
#print axioms SuperZeta.TwoRootCircleIntegral.circleIntegral_of_two_simple_zeros
#print axioms SuperZeta.TwoRootCircleIntegral.circleIntegral_of_one_double_zero
#print axioms SuperZeta.TwoRootCircleIntegral.solution_meets_rectangle_edge
