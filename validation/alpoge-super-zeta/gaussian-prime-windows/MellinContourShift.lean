import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! Square-integrable height decay on a closed strip permits a shift of the
Mellin inversion line. The rectangle identity and its limit use the same
vertical integrals as Mathlib's Mellin inverse. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory Set
open scoped Topology Interval

noncomputable section

private theorem integrable_inverse_add_abs_sq :
    Integrable (fun y : ℝ => ((1 + |y|) ^ (2 : ℕ))⁻¹) := by
  have hi := integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := 2) (by norm_num)
  convert hi using 1
  ext y
  rw [Real.norm_eq_abs, Real.rpow_neg (by positivity), Real.rpow_two]

/-- A continuous vertical reading dominated by the square of the reciprocal
linear envelope is integrable on that line. -/
theorem verticalIntegrable_of_square_decay {f : ℂ → ℂ} {σ a b C : ℝ}
    (hσa : a ≤ σ) (hσb : σ ≤ b)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C / (1 + |z.im|) ^ 2) :
    VerticalIntegrable f σ := by
  let line (y : ℝ) : ℂ := (σ : ℂ) + (y : ℂ) * I
  let reading := f ∘ line
  have hre (y : ℝ) : (line y).re = σ := by simp [line, mul_re]
  have him (y : ℝ) : (line y).im = y := by simp [line, mul_im]
  have hcont : Continuous reading := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hl : ContinuousAt line y := by fun_prop
    have hf := (hd (line y) (by rw [hre]; exact hσa) (by rw [hre]; exact hσb)).continuousAt
    exact hf.comp hl
  change Integrable reading
  refine (integrable_inverse_add_abs_sq.const_mul C).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  simpa only [reading, Function.comp_apply, him, div_eq_mul_inv] using
    hbound (line y) (by rw [hre]; exact hσa) (by rw [hre]; exact hσb)

/-- If a strip is free of singularities and the horizontal edges vanish,
the two full vertical integrals agree. -/
theorem verticalIntegral_eq_of_square_decay {f : ℂ → ℂ} {a b C : ℝ}
    (hab : a ≤ b)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ C / (1 + |z.im|) ^ 2) :
    (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * I) := by
  let H (t : ℝ) := ∫ x in a..b, f ((x : ℂ) + (t : ℂ) * I)
  let V (σ T : ℝ) := ∫ y in -T..T, f ((σ : ℂ) + (y : ℂ) * I)
  have hH (t : ℝ) : ‖H t‖ ≤ (C / (1 + |t|) ^ 2) * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le hab] at hx
    simpa [mul_re, mul_im] using
      hbound ((x : ℂ) + (t : ℂ) * I) (by simpa [mul_re] using hx.1.le)
        (by simpa [mul_re] using hx.2)
  have hq : Tendsto (fun T : ℝ => 1 + |T|) atTop atTop :=
    tendsto_atTop_mono (fun T => (le_abs_self T).trans (by linarith)) tendsto_id
  have hs : Tendsto (fun T : ℝ => (1 + |T|) ^ (2 : ℕ)) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hq
  have hi : Tendsto (fun T : ℝ => ((1 + |T|) ^ (2 : ℕ))⁻¹) atTop (𝓝 0) :=
    hs.inv_tendsto_atTop
  have hE : Tendsto (fun T : ℝ => (C / (1 + |T|) ^ (2 : ℕ)) * |b - a|) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using (hi.const_mul C).mul_const |b - a|
  have hpos : Tendsto H atTop (𝓝 0) := squeeze_zero_norm hH hE
  have hneg : Tendsto (fun T : ℝ => H (-T)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun T => by simpa only [abs_neg] using hH (-T)) hE
  have ha := verticalIntegrable_of_square_decay le_rfl hab hd hbound
  have hb := verticalIntegrable_of_square_decay hab le_rfl hd hbound
  have htneg : Tendsto (fun T : ℝ => -T) atTop atBot := tendsto_neg_atTop_atBot
  have hta : Tendsto (V a) atTop (𝓝 (∫ y : ℝ, f ((a : ℂ) + (y : ℂ) * I))) :=
    intervalIntegral_tendsto_integral ha htneg tendsto_id
  have htb : Tendsto (V b) atTop (𝓝 (∫ y : ℝ, f ((b : ℂ) + (y : ℂ) * I))) :=
    intervalIntegral_tendsto_integral hb htneg tendsto_id
  have hRect (T : ℝ) : H (-T) - H T + I • V b T - I • V a T = 0 := by
    have hD : DifferentiableOn ℂ f (Complex.reProdIm (uIcc a b) (uIcc (-T) T)) := by
      intro z hz
      rw [mem_reProdIm, uIcc_of_le hab] at hz
      exact (hd z hz.1.1 hz.1.2).differentiableWithinAt
    exact integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, -T⟩ ⟨b, T⟩ hD
  have hZero : Tendsto (fun T : ℝ => H (-T) - H T + I • V b T - I • V a T) atTop (𝓝 0) :=
    tendsto_const_nhds.congr (fun T => (hRect T).symm)
  have hLim := ((hneg.sub hpos).add (htb.const_smul I)).sub (hta.const_smul I)
  have he := tendsto_nhds_unique hLim hZero
  simp only [sub_self, zero_add, smul_eq_mul, ← mul_sub] at he
  exact (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left Complex.I_ne_zero)).symm

/-- The Mellin inverse of a pole-free, square-decaying continuation is the
same on either edge of the strip. -/
theorem mellinInv_eq_of_square_decay {g : ℂ → ℂ} {a b C v : ℝ} (hv : 0 < v)
    (hab : a ≤ b)
    (hd : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ g z)
    (hbound : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖g z‖ ≤ C / (1 + |z.im|) ^ 2) :
    mellinInv a g v = mellinInv b g v := by
  let f (z : ℂ) := (v : ℂ) ^ (-z) * g z
  let P := max (v ^ (-a)) (v ^ (-b))
  have hP : 0 ≤ P := (Real.rpow_nonneg hv.le _).trans (le_max_left _ _)
  have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have hD (z : ℂ) (ha : a ≤ z.re) (hb : z.re ≤ b) : DifferentiableAt ℂ f z :=
    (differentiableAt_id.neg.const_cpow (Or.inl hvC)).mul (hd z ha hb)
  have hB (z : ℂ) (ha : a ≤ z.re) (hb : z.re ≤ b) :
      ‖f z‖ ≤ (P * C) / (1 + |z.im|) ^ 2 := by
    have hPower : ‖(v : ℂ) ^ (-z)‖ ≤ P := by
      rw [norm_cpow_eq_rpow_re_of_pos hv, neg_re]
      by_cases h : 1 ≤ v
      · exact (Real.rpow_le_rpow_of_exponent_le h (neg_le_neg ha)).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hv (le_of_not_ge h)
          (neg_le_neg hb)).trans (le_max_right _ _)
    unfold f
    rw [norm_mul, mul_div_assoc]
    exact mul_le_mul hPower (hbound z ha hb) (norm_nonneg _) hP
  rw [mellinInv, mellinInv]
  simp only [smul_eq_mul]
  exact congrArg (fun w : ℂ => (1 / (2 * Real.pi)) • w)
    (verticalIntegral_eq_of_square_decay hab hD hB)

/-- The norm of the inverse on an integrable line keeps the real exponent
of that line. -/
theorem norm_mellinInv_le {g : ℂ → ℂ} {a v : ℝ}
    (hv : 0 < v) (hg : VerticalIntegrable g a) :
    ‖mellinInv a g v‖ ≤
      ((1 / (2 * Real.pi)) * ∫ y : ℝ, ‖g ((a : ℂ) + (y : ℂ) * I)‖) * v ^ (-a) := by
  rw [mellinInv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hI : Integrable (fun y : ℝ => v ^ (-a) * ‖g ((a : ℂ) + (y : ℂ) * I)‖) :=
    hg.norm.const_mul _
  have hB : ‖∫ y : ℝ, (v : ℂ) ^ (-((a : ℂ) + (y : ℂ) * I)) •
      g ((a : ℂ) + (y : ℂ) * I)‖ ≤
      ∫ y : ℝ, v ^ (-a) * ‖g ((a : ℂ) + (y : ℂ) * I)‖ := by
    refine norm_integral_le_of_norm_le hI (Eventually.of_forall fun y => ?_)
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hv, neg_re]
    simp [mul_re]
  apply (mul_le_mul_of_nonneg_left hB (by positivity)).trans_eq
  rw [integral_const_mul]
  ring

#print axioms verticalIntegrable_of_square_decay
#print axioms verticalIntegral_eq_of_square_decay
#print axioms mellinInv_eq_of_square_decay
#print axioms norm_mellinInv_le

end
end AlpogeSuperZeta
