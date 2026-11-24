import ArchivedDottieContourSum
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Shift the archived vertical line across its pole at zero. The proof
uses Cauchy–Goursat on the divided difference, then evaluates the pole
term on the real parameter of the two vertical sides. -/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace QuarticModel

private noncomputable def verticalPoint (c t : ℝ) : ℂ := (c : ℂ)+(t : ℂ)*I
private noncomputable def horizontalPoint (t x : ℝ) : ℂ := (x : ℂ)+(t : ℂ)*I

private theorem verticalPoint_ne_zero {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    verticalPoint c t ≠ 0 := by
  intro h
  exact hc (by simpa [verticalPoint, Complex.mul_re] using congrArg Complex.re h)

private theorem verticalPole_difference (u : ℝ) :
    (verticalPoint 1 u)⁻¹ - (verticalPoint (-1) u)⁻¹ =
      ((2 * (1+u^2)⁻¹ : ℝ) : ℂ) := by
  have hRight := verticalPoint_ne_zero (by norm_num : (1 : ℝ) ≠ 0) u
  have hLeft := verticalPoint_ne_zero (by norm_num : (-1 : ℝ) ≠ 0) u
  rw [← one_div, ← one_div, div_sub_div _ _ hRight hLeft]
  simp only [verticalPoint, ofReal_one, ofReal_neg, one_mul, mul_one, ofReal_mul, ofReal_inv,
    ofReal_ofNat, ofReal_add, ofReal_pow]
  rw [show (-1 : ℂ)+(u : ℂ)*I-(1+(u : ℂ)*I) = -2 by ring,
    show ((1 : ℂ)+(u : ℂ)*I)*(-1+(u : ℂ)*I) = -(1+(u : ℂ)^2) by
      linear_combination (u : ℂ)^2 * Complex.I_sq]
  rw [neg_div_neg_eq, div_eq_mul_inv]

private theorem dslope_vertical_difference (H : ℂ → ℂ) (u : ℝ) :
    dslope H 0 (verticalPoint 1 u) - dslope H 0 (verticalPoint (-1) u) =
      (H (verticalPoint 1 u) / verticalPoint 1 u - H (verticalPoint (-1) u) / verticalPoint (-1) u) -
        H 0 * ((2 * (1+u^2)⁻¹ : ℝ) : ℂ) := by
  rw [dslope_of_ne _ (verticalPoint_ne_zero (by norm_num) _),
    dslope_of_ne _ (verticalPoint_ne_zero (by norm_num) _),
    slope_def_field, slope_def_field, sub_zero, sub_zero, ← verticalPole_difference]
  simp only [div_eq_mul_inv]
  ring

private theorem dslope_boundary (H : ℂ → ℂ) (hH : Differentiable ℂ H) (T : ℝ) :
    (∫ y in -T..T, (dslope H 0 (verticalPoint 1 y) - dslope H 0 (verticalPoint (-1) y))) =
      I*((∫ x in (-1 : ℝ)..1, dslope H 0 (horizontalPoint (-T) x)) -
        (∫ x in (-1 : ℝ)..1, dslope H 0 (horizontalPoint T x))) := by
  have hd : Differentiable ℂ (dslope H 0) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (univ_mem : univ ∈ 𝓝 (0 : ℂ))).mpr hH.differentiableOn
  have hD (c : ℝ) : IntervalIntegrable (fun y => dslope H 0 (verticalPoint c y)) volume (-T) T :=
    (hd.continuous.comp (by unfold verticalPoint; fun_prop)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (hD 1) (hD (-1))]
  have hr := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (dslope H 0)
    ⟨-1,-T⟩ ⟨1,T⟩ hd.differentiableOn
  simp only [horizontalPoint, verticalPoint, smul_eq_mul] at hr ⊢
  linear_combination (-I)*hr +
    ((∫ y in -T..T, dslope H 0 ((1 : ℝ) + (y : ℂ)*I)) -
      (∫ y in -T..T, dslope H 0 ((-1 : ℝ) + (y : ℂ)*I))) * Complex.I_sq

private theorem pole_integral (T : ℝ) :
    (∫ u in -T..T, ((2 * (1+u^2)⁻¹ : ℝ) : ℂ)) =
      ((2 * (Real.arctan T - Real.arctan (-T)) : ℝ) : ℂ) := by
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul,
    integral_inv_one_add_sq]

/-- The difference of the two upward vertical integrals across the simple
pole is its residue times \(2π\). Horizontal decay is expressed in terms
of the analytic divided difference. -/
theorem shift_vertical_one_of_decay (H : ℂ → ℂ) (hH : Differentiable ℂ H)
    (hvRight : Integrable (fun t => H (verticalPoint 1 t) / verticalPoint 1 t))
    (hvLeft : Integrable (fun t => H (verticalPoint (-1) t) / verticalPoint (-1) t))
    (hbottom : Tendsto (fun T => ∫ x in (-1 : ℝ)..1, dslope H 0 (horizontalPoint (-T) x))
      atTop (𝓝 0))
    (htop : Tendsto (fun T => ∫ x in (-1 : ℝ)..1, dslope H 0 (horizontalPoint T x))
      atTop (𝓝 0)) :
    (∫ t : ℝ, H (verticalPoint 1 t) / verticalPoint 1 t) -
      (∫ t : ℝ, H (verticalPoint (-1) t) / verticalPoint (-1) t) =
      2*(Real.pi : ℂ)*H 0 := by
  let f := fun u => H (verticalPoint 1 u) / verticalPoint 1 u -
    H (verticalPoint (-1) u) / verticalPoint (-1) u
  let g := fun u : ℝ => ((2 * (1+u^2)⁻¹ : ℝ) : ℂ)
  let bottom := fun T : ℝ => ∫ x in (-1 : ℝ)..1, dslope H 0 (horizontalPoint (-T) x)
  let top := fun T : ℝ => ∫ x in (-1 : ℝ)..1, dslope H 0 (horizontalPoint T x)
  have hf : Integrable f := hvRight.sub hvLeft
  have h₁ : Tendsto (fun T : ℝ => (∫ u in -T..T, f u)) atTop (𝓝 (∫ u, f u)) :=
    intervalIntegral_tendsto_integral hf tendsto_neg_atTop_atBot tendsto_id
  have he (T : ℝ) :
      (∫ u in -T..T, f u) = I*(bottom T-top T) +
        H 0 * ((2 * (Real.arctan T - Real.arctan (-T)) : ℝ) : ℂ) := by
    have hg : Continuous g := by
      apply Complex.continuous_ofReal.comp
      exact continuous_const.mul ((continuous_const.add (continuous_id.pow 2)).inv₀
        (fun u => ne_of_gt (by positivity : 0 < 1+(u : ℝ)^2)))
    have hc := dslope_boundary H hH T
    simp_rw [dslope_vertical_difference] at hc
    change (∫ u in -T..T, f u-H 0*g u) = I*(bottom T-top T) at hc
    rw [intervalIntegral.integral_sub hf.intervalIntegrable
      ((hg.const_mul _).intervalIntegrable _ _), intervalIntegral.integral_const_mul] at hc
    unfold g at hc
    rw [pole_integral T] at hc
    linear_combination hc
  have hp : Tendsto (fun T : ℝ => 2 * (Real.arctan T - Real.arctan (-T))) atTop
      (𝓝 (2*Real.pi)) := by
    have h := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).sub
      ((Real.tendsto_arctan_atBot.comp tendsto_neg_atTop_atBot).mono_right nhdsWithin_le_nhds)).const_mul (2 : ℝ)
    rw [show 2*(Real.pi/2-(-(Real.pi/2))) = 2*Real.pi by ring] at h
    simpa only [Function.comp_apply] using h
  have hp' := (Complex.continuous_ofReal.tendsto (2*Real.pi)).comp hp
  have h₂ := ((hbottom.sub htop).const_mul I).add (hp'.const_mul (H 0))
  have h₂' : Tendsto (fun T : ℝ => (∫ u in -T..T, f u)) atTop (𝓝 (2*(Real.pi : ℂ)*H 0)) := by
    simp only [sub_self, mul_zero, zero_add, ofReal_mul, ofReal_ofNat] at h₂
    rw [show H 0 * (2*(Real.pi : ℂ)) = 2*(Real.pi : ℂ)*H 0 by ring] at h₂
    exact h₂.congr' (Eventually.of_forall fun T => (he T).symm)
  have hresult := tendsto_nhds_unique h₁ h₂'
  simpa only [f, integral_sub hvRight hvLeft] using hresult

#print axioms shift_vertical_one_of_decay

end QuarticModel
