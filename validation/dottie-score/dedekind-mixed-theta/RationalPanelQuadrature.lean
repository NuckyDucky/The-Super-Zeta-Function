import ContourTaylor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! A finite rational quadrature rule can be checked through moment errors.
The node and weight table needs only rational inequalities. -/

namespace FieldTarget

open MeasureTheory Metric Set
open scoped BigOperators Interval NNReal

noncomputable section

def panelMoment (k : ℕ) : ℚ := (1 - (-1 : ℚ) ^ (k + 1)) / (k + 1 : ℚ)

def rationalPanelRule {m : ℕ} (nodes weights : Fin m → ℚ) (f : ℝ → ℂ)
    (c h : ℝ) : ℂ :=
  (h : ℂ) * ∑ i, (weights i : ℂ) * f (c + h * (nodes i : ℝ))

def rationalCompositeRule {m : ℕ} (nodes weights : Fin m → ℚ) (f : ℝ → ℂ)
    (a h : ℝ) (p : ℕ) : ℂ :=
  ∑ j ∈ Finset.range p, rationalPanelRule nodes weights f (a + (2 * (j : ℝ) + 1) * h) h

private theorem integral_shiftedMonomial (c h : ℝ) (k : ℕ) :
    (∫ x in c - h..c + h, ((x - c : ℝ) : ℂ) ^ k) =
      (h : ℂ) * (h : ℂ) ^ k * (panelMoment k : ℂ) := by
  have hs := intervalIntegral.integral_comp_sub_right
    (a := c - h) (b := c + h) (f := fun x : ℝ ↦ (x : ℂ) ^ k) c
  rw [show c - h - c = -h by ring, show c + h - c = h by ring] at hs
  rw [hs]
  simp_rw [← Complex.ofReal_pow]
  rw [intervalIntegral.integral_ofReal, integral_pow]
  unfold panelMoment
  push_cast
  rw [← neg_one_mul (h : ℂ), mul_pow, pow_succ (h : ℂ)]
  ring

private theorem rule_monomial {m : ℕ} (nodes weights : Fin m → ℚ) (c h : ℝ) (k : ℕ) :
    rationalPanelRule nodes weights (fun x ↦ ((x - c : ℝ) : ℂ) ^ k) c h =
      (h : ℂ) * (h : ℂ) ^ k * (∑ i, (weights i : ℂ) * (nodes i : ℂ) ^ k) := by
  unfold rationalPanelRule
  rw [mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  beta_reduce
  rw [add_sub_cancel_left, Complex.ofReal_mul, Complex.ofReal_ratCast, mul_pow]
  ring

private theorem rule_polynomial {m : ℕ} (nodes weights : Fin m → ℚ) (a : ℕ → ℂ)
    (c h : ℝ) (n : ℕ) :
    rationalPanelRule nodes weights (fun x ↦ ∑ k ∈ Finset.range n, a k * ((x - c : ℝ) : ℂ) ^ k) c h =
      ∑ k ∈ Finset.range n, a k *
        rationalPanelRule nodes weights (fun x ↦ ((x - c : ℝ) : ℂ) ^ k) c h := by
  unfold rationalPanelRule
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem rule_sub_norm_le {m : ℕ} (nodes weights : Fin m → ℚ)
    {f g : ℝ → ℂ} {c h E W : ℝ} (hh : 0 ≤ h) (hE : 0 ≤ E)
    (hnodes : ∀ i, |(nodes i : ℝ)| ≤ 1) (hweights : ∑ i, |(weights i : ℝ)| ≤ W)
    (herr : ∀ x ∈ Icc (c - h) (c + h), ‖f x - g x‖ ≤ E) :
    ‖rationalPanelRule nodes weights f c h - rationalPanelRule nodes weights g c h‖ ≤ h * W * E := by
  have hloc (i : Fin m) : c + h * (nodes i : ℝ) ∈ Icc (c - h) (c + h) := by
    obtain ⟨hl, hr⟩ := abs_le.mp (hnodes i)
    have h₁ := mul_le_mul_of_nonneg_left hl hh
    have h₂ := mul_le_mul_of_nonneg_left hr hh
    exact ⟨by linarith only [h₁], by linarith only [h₂]⟩
  unfold rationalPanelRule
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hh]
  simp_rw [← mul_sub]
  calc
    _ ≤ h * ∑ i, ‖(weights i : ℂ) * (f (c + h * (nodes i : ℝ)) -
        g (c + h * (nodes i : ℝ)))‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) hh
    _ ≤ h * ∑ i, |(weights i : ℝ)| * E := by
      gcongr with i _
      rw [norm_mul, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (herr _ (hloc i)) (abs_nonneg _)
    _ ≤ h * W * E := by rw [← Finset.sum_mul, mul_assoc]; gcongr

private theorem polynomial_moment_error {m : ℕ} (nodes weights : Fin m → ℚ)
    (a : ℕ → ℂ) (c : ℝ) {h R M δ : ℝ} (n : ℕ) (hh : 0 ≤ h) (hR : 0 < R)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hr : h < R)
    (ha : ∀ k < n, ‖a k‖ ≤ M * R⁻¹ ^ k)
    (hmoments : ∀ k < n,
      |(panelMoment k : ℝ) - ∑ i, (weights i : ℝ) * (nodes i : ℝ) ^ k| ≤ δ) :
    ‖(∫ x in c - h..c + h, ∑ k ∈ Finset.range n, a k * ((x - c : ℝ) : ℂ) ^ k) -
      rationalPanelRule nodes weights (fun x ↦ ∑ k ∈ Finset.range n, a k * ((x - c : ℝ) : ℂ) ^ k) c h‖ ≤
      h * M * δ / (1 - h / R) := by
  let q := h / R
  have hq₀ : 0 ≤ q := div_nonneg hh hR.le
  have hq₁ : q < 1 := (div_lt_one hR).mpr hr
  have hg := hasSum_geometric_of_lt_one hq₀ hq₁
  have hsum : (∑ k ∈ Finset.range n, q ^ k) ≤ 1 / (1 - q) := by
    rw [one_div, ← hg.tsum_eq]
    exact hg.summable.sum_le_tsum _ (fun k _ ↦ pow_nonneg hq₀ k)
  rw [intervalIntegral.integral_finsetSum, rule_polynomial, ← Finset.sum_sub_distrib]
  · simp_rw [intervalIntegral.integral_const_mul, integral_shiftedMonomial, rule_monomial]
    simp_rw [← mul_sub]
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ k ∈ Finset.range n, h * M * δ * q ^ k := by
        apply Finset.sum_le_sum
        intro k hk
        have hcast : (panelMoment k : ℂ) - (∑ i, (weights i : ℂ) * (nodes i : ℂ) ^ k) =
            (((panelMoment k : ℝ) - ∑ i, (weights i : ℝ) * (nodes i : ℝ) ^ k : ℝ) : ℂ) := by
          push_cast
          rfl
        rw [hcast, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hh]
        calc
          _ ≤ (M * R⁻¹ ^ k) * (h * h ^ k * δ) := by
            gcongr
            · exact ha k (Finset.mem_range.mp hk)
            · exact hmoments k (Finset.mem_range.mp hk)
          _ = h * M * δ * q ^ k := by change _ = h * M * δ * (h / R) ^ k; rw [div_eq_mul_inv, mul_pow]; ring
      _ ≤ _ := by
        rw [← Finset.mul_sum, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hsum) (by positivity)
  · intro k _
    exact (show Continuous (fun x : ℝ ↦ a k * ((x - c : ℝ) : ℂ) ^ k) from by
      fun_prop).intervalIntegrable _ _

private theorem contour_coeff_same_radius {F : ℂ → ℂ} {c : ℂ} {R r : ℝ≥0}
    (hR : 0 < R) (hr : 0 < r) (hF : DifferentiableOn ℂ F (closedBall c R))
    (hFr : DifferentiableOn ℂ F (closedBall c r)) (k : ℕ) :
    contourTaylorCoeff F c R k = contourTaylorCoeff F c r k := by
  apply mul_left_cancel₀ (show (k.factorial : ℂ) ≠ 0 by exact_mod_cast Nat.factorial_ne_zero k)
  have hOuter := (hF.hasFPowerSeriesOnBall hR).factorial_smul (1 : ℂ) k
  have hInner := (hFr.hasFPowerSeriesOnBall hr).factorial_smul (1 : ℂ) k
  simpa only [contourTaylorCoeff, nsmul_eq_mul] using hOuter.trans hInner.symm

/-- Use the outer circle for the Taylor tail and the inner circle for the coefficients
that multiply moment errors. Both circles give the same Taylor polynomial. -/
theorem rationalPanelRule_twoRadius_error_le {m : ℕ} (nodes weights : Fin m → ℚ)
    {F : ℂ → ℂ} {c h M mInner δ W : ℝ} {R r : ℝ≥0} (n : ℕ)
    (hh : 0 ≤ h) (hr : h < (r : ℝ)) (hrR : r ≤ R) (hδ : 0 ≤ δ)
    (hnodes : ∀ i, |(nodes i : ℝ)| ≤ 1) (hweights : ∑ i, |(weights i : ℝ)| ≤ W)
    (hmoments : ∀ k < n,
      |(panelMoment k : ℝ) - ∑ i, (weights i : ℝ) * (nodes i : ℝ) ^ k| ≤ δ)
    (hF : DifferentiableOn ℂ F (closedBall (c : ℂ) R))
    (hbound : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ M)
    (hSmall : ∀ z ∈ sphere (c : ℂ) r, ‖F z‖ ≤ mInner) :
    ‖(∫ x in c - h..c + h, F (x : ℂ)) - rationalPanelRule nodes weights (fun x ↦ F x) c h‖ ≤
      h * (2 + W) * (M * (h / (R : ℝ)) ^ n / (1 - h / (R : ℝ))) +
        h * mInner * δ / (1 - h / (r : ℝ)) := by
  have hrr : (r : ℝ) ≤ (R : ℝ) := by exact_mod_cast hrR
  have hOuter : h < (R : ℝ) := hr.trans_le hrr
  have hR : 0 < (R : ℝ) := hh.trans_lt hOuter
  have hr₀ : 0 < (r : ℝ) := hh.trans_lt hr
  have hM : 0 ≤ M := (norm_nonneg _).trans (hbound _ (circleMap_mem_sphere _ hR.le 0))
  have hMi : 0 ≤ mInner := (norm_nonneg _).trans (hSmall _ (circleMap_mem_sphere _ hr₀.le 0))
  have hFr : DifferentiableOn ℂ F (closedBall (c : ℂ) r) :=
    hF.mono (closedBall_subset_closedBall hrr)
  let q := h / (R : ℝ)
  let E := M * q ^ n / (1 - q)
  let a := contourTaylorCoeff F c R
  let p : ℝ → ℂ := fun x ↦ ∑ k ∈ Finset.range n, a k * ((x - c : ℝ) : ℂ) ^ k
  have hq₀ : 0 ≤ q := div_nonneg hh hR.le
  have hq₁ : q < 1 := (div_lt_one hR).mpr hOuter
  have hE : 0 ≤ E := div_nonneg (mul_nonneg hM (pow_nonneg hq₀ _)) (sub_nonneg.mpr hq₁.le)
  have hpoint (x : ℝ) (hx : x ∈ Icc (c - h) (c + h)) : ‖((x - c : ℝ) : ℂ)‖ ≤ h := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith only [hx.1], by linarith only [hx.2]⟩
  have hp (x : ℝ) (hx : x ∈ Icc (c - h) (c + h)) : ‖F (x : ℂ) - p x‖ ≤ E := by
    have h := contourTaylor_tail_le hF hbound hOuter (hpoint x hx) n
    rwa [← Complex.ofReal_add, show c + (x - c) = x by ring] at h
  have hcont : ContinuousOn (fun x : ℝ ↦ F (x : ℂ)) (Icc (c - h) (c + h)) := by
    refine hF.continuousOn.comp Complex.continuous_ofReal.continuousOn ?_
    intro x hx
    rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub]
    exact (hpoint x hx).trans hOuter.le
  have hab : c - h ≤ c + h := by linarith only [hh]
  have hfi := hcont.intervalIntegrable_of_Icc (μ := volume) hab
  have hpi : IntervalIntegrable p volume (c - h) (c + h) :=
    (show Continuous p from by dsimp only [p]; fun_prop).intervalIntegrable _ _
  have hi : ‖(∫ x in c - h..c + h, F (x : ℂ)) - ∫ x in c - h..c + h, p x‖ ≤ E * (2 * h) := by
    rw [← intervalIntegral.integral_sub hfi hpi]
    have hx := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c - h) (b := c + h) (f := fun x ↦ F (x : ℂ) - p x)
      (fun x hx ↦ hp x (Ioc_subset_Icc_self (by rwa [uIoc_of_le hab] at hx)))
    rwa [abs_of_nonneg (sub_nonneg.mpr hab), show c + h - (c - h) = 2 * h by ring] at hx
  have hCoeff (k : ℕ) : ‖a k‖ ≤ mInner * ((r : ℝ)⁻¹) ^ k := by
    dsimp only [a]
    rw [contour_coeff_same_radius (by exact_mod_cast hR) (by exact_mod_cast hr₀) hF hFr k]
    exact norm_contourTaylorCoeff_le hr₀ hFr.continuousOn hSmall k
  have hpoly := polynomial_moment_error nodes weights a c n hh hr₀ hMi hδ hr
    (fun k _ ↦ hCoeff k) hmoments
  have hquad := rule_sub_norm_le nodes weights hh hE hnodes hweights hp
  have hquadRev : ‖rationalPanelRule nodes weights p c h -
      rationalPanelRule nodes weights (fun x ↦ F x) c h‖ ≤ h * W * E := by
    rw [norm_sub_rev]
    exact hquad
  refine (norm_sub_le_norm_sub_add_norm_sub _ (∫ x in c - h..c + h, p x) _).trans ?_
  refine (add_le_add hi ((norm_sub_le_norm_sub_add_norm_sub _ (rationalPanelRule nodes weights p c h) _).trans
    (add_le_add hpoly hquadRev))).trans_eq ?_
  dsimp only [E, q]
  ring

theorem rationalPanelRule_error_le {m : ℕ} (nodes weights : Fin m → ℚ)
    {F : ℂ → ℂ} {c h M δ W : ℝ} {R : ℝ≥0} (n : ℕ)
    (hh : 0 ≤ h) (hr : h < (R : ℝ)) (hδ : 0 ≤ δ)
    (hnodes : ∀ i, |(nodes i : ℝ)| ≤ 1) (hweights : ∑ i, |(weights i : ℝ)| ≤ W)
    (hmoments : ∀ k < n,
      |(panelMoment k : ℝ) - ∑ i, (weights i : ℝ) * (nodes i : ℝ) ^ k| ≤ δ)
    (hF : DifferentiableOn ℂ F (closedBall (c : ℂ) R))
    (hbound : ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ M) :
    ‖(∫ x in c - h..c + h, F (x : ℂ)) - rationalPanelRule nodes weights (fun x ↦ F x) c h‖ ≤
      h * M / (1 - h / (R : ℝ)) * ((2 + W) * (h / (R : ℝ)) ^ n + δ) := by
  refine (rationalPanelRule_twoRadius_error_le nodes weights n hh hr le_rfl hδ
    hnodes hweights hmoments hF hbound hbound).trans_eq ?_
  ring

theorem rationalCompositeRule_twoRadius_error_le {m : ℕ} (nodes weights : Fin m → ℚ)
    {F : ℂ → ℂ} {a h M mInner δ W : ℝ} {R r : ℝ≥0} (n p : ℕ)
    (hh : 0 ≤ h) (hr : h < (r : ℝ)) (hrR : r ≤ R) (hδ : 0 ≤ δ)
    (hnodes : ∀ i, |(nodes i : ℝ)| ≤ 1) (hweights : ∑ i, |(weights i : ℝ)| ≤ W)
    (hmoments : ∀ k < n,
      |(panelMoment k : ℝ) - ∑ i, (weights i : ℝ) * (nodes i : ℝ) ^ k| ≤ δ)
    (hF : Differentiable ℂ F)
    (hbound : ∀ c ∈ Icc a (a + 2 * (p : ℝ) * h), ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ M)
    (hSmall : ∀ c ∈ Icc a (a + 2 * (p : ℝ) * h), ∀ z ∈ sphere (c : ℂ) r, ‖F z‖ ≤ mInner) :
    ‖(∫ x in a..a + 2 * (p : ℝ) * h, F (x : ℂ)) -
        rationalCompositeRule nodes weights (fun x ↦ F x) a h p‖ ≤
      (p : ℝ) * (h * (2 + W) * (M * (h / (R : ℝ)) ^ n / (1 - h / (R : ℝ))) +
        h * mInner * δ / (1 - h / (r : ℝ))) := by
  let b (k : ℕ) := a + 2 * (k : ℝ) * h
  let c (k : ℕ) := a + (2 * (k : ℝ) + 1) * h
  have hleft (k : ℕ) : b k = c k - h := by dsimp [b, c]; ring
  have hright (k : ℕ) : b (k + 1) = c k + h := by dsimp [b, c]; push_cast; ring
  have hstart : b 0 = a := by simp [b]
  have hsplit := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (a := b) (n := p)
    (f := fun x : ℝ ↦ F (x : ℂ))
    (fun k _ ↦ (hF.continuous.comp Complex.continuous_ofReal).intervalIntegrable (b k) (b (k + 1)))
  rw [hstart] at hsplit
  change (∑ k ∈ Finset.range p, ∫ x in b k..b (k + 1), F (x : ℂ)) =
    (∫ x in a..a + 2 * (p : ℝ) * h, F (x : ℂ)) at hsplit
  rw [← hsplit, rationalCompositeRule, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _k ∈ Finset.range p,
        (h * (2 + W) * (M * (h / (R : ℝ)) ^ n / (1 - h / (R : ℝ))) +
          h * mInner * δ / (1 - h / (r : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hlast : (k : ℝ) + 1 ≤ p := by
        exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      have hc : c k ∈ Icc a (a + 2 * (p : ℝ) * h) := by
        refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
        dsimp only [c]
        have hmid : 2 * (k : ℝ) + 1 ≤ 2 * (p : ℝ) := by linarith only [hlast]
        have h := mul_le_mul_of_nonneg_right hmid hh
        linarith only [h]
      change ‖(∫ x in b k..b (k + 1), F (x : ℂ)) -
        rationalPanelRule nodes weights (fun x ↦ F x) (c k) h‖ ≤ _
      rw [hleft, hright]
      exact rationalPanelRule_twoRadius_error_le nodes weights n hh hr hrR hδ hnodes hweights hmoments
        hF.differentiableOn (hbound _ hc) (hSmall _ hc)
    _ = _ := by simp [mul_add]

theorem rationalCompositeRule_error_le {m : ℕ} (nodes weights : Fin m → ℚ)
    {F : ℂ → ℂ} {a h M δ W : ℝ} {R : ℝ≥0} (n p : ℕ)
    (hh : 0 ≤ h) (hr : h < (R : ℝ)) (hδ : 0 ≤ δ)
    (hnodes : ∀ i, |(nodes i : ℝ)| ≤ 1) (hweights : ∑ i, |(weights i : ℝ)| ≤ W)
    (hmoments : ∀ k < n,
      |(panelMoment k : ℝ) - ∑ i, (weights i : ℝ) * (nodes i : ℝ) ^ k| ≤ δ)
    (hF : Differentiable ℂ F)
    (hbound : ∀ c ∈ Icc a (a + 2 * (p : ℝ) * h), ∀ z ∈ sphere (c : ℂ) R, ‖F z‖ ≤ M) :
    ‖(∫ x in a..a + 2 * (p : ℝ) * h, F (x : ℂ)) -
        rationalCompositeRule nodes weights (fun x ↦ F x) a h p‖ ≤
      (p : ℝ) * (h * M / (1 - h / (R : ℝ)) * ((2 + W) * (h / (R : ℝ)) ^ n + δ)) := by
  refine (rationalCompositeRule_twoRadius_error_le nodes weights n p hh hr le_rfl hδ
    hnodes hweights hmoments hF hbound hbound).trans_eq ?_
  ring

#print axioms rationalPanelRule_twoRadius_error_le
#print axioms rationalCompositeRule_twoRadius_error_le
#print axioms rationalPanelRule_error_le
#print axioms rationalCompositeRule_error_le

end

end FieldTarget
