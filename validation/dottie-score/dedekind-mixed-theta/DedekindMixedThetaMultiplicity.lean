import DedekindMixedThetaDerivative
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace FieldTarget

open Complex Filter MeasureTheory Set
open scoped Topology
open DedekindZetaZeroFree.AbelianQuotient

noncomputable section

private theorem tendsto_twice_integral_tail (f : ℝ → ℝ) :
    Tendsto (fun R : ℝ ↦ 2 * ∫ x in Ioi R, f x) atTop (𝓝 0) := by
  simpa only [id, mul_zero] using
    (tendsto_integral_Ioi_zero (f := f) (b := id) tendsto_id).const_mul (2 : ℝ)

theorem mixedThetaWeightedTail_tendsto_zero (K : Type) [Field K] [NumberField K] (ρ : ℝ) :
    Tendsto (fun R : ℝ ↦ mixedThetaWeightedTail K R ρ) atTop (𝓝 0) :=
  tendsto_twice_integral_tail _

/-- For each field and derivative order, a single sufficiently large cutoff
works at every height on the closed critical strip. -/
theorem mixedTheta_uniform_derivative_cutoff (K : Type) [Field K] [NumberField K]
    (n : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, 1 ≤ R ∧ ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖iteratedDeriv n (Theta.mixedThetaPair K).Λ₀ w -
        iteratedDeriv n (mixedThetaTruncation K R) w‖ < ε := by
  let B : ℝ := (n.factorial : ℝ) / ρ ^ n
  have hLim : Tendsto (fun R : ℝ ↦ B * mixedThetaWeightedTail K R ρ) atTop (𝓝 0) := by
    simpa only [mul_zero] using (mixedThetaWeightedTail_tendsto_zero K ρ).const_mul B
  filter_upwards [eventually_ge_atTop (1 : ℝ), hLim.eventually (Iio_mem_nhds hε)] with R hR hBound
  refine ⟨hR, fun w hlo hhi ↦ (mixedTheta_mellin_iteratedDeriv_error_le K n hR hρ hlo hhi).trans_lt ?_⟩
  have hEq : (n.factorial : ℝ) * mixedThetaWeightedTail K R ρ / ρ ^ n =
      B * mixedThetaWeightedTail K R ρ := by
    unfold B
    ring
  rwa [hEq]

private theorem poleFactor_hasDerivAt (w : ℂ) :
    HasDerivAt (fun z : ℂ ↦ z * (1 - z)) (1 - 2 * w) w := by
  have hSub : HasDerivAt (fun z : ℂ ↦ 1 - z) (-1) w :=
    (hasDerivAt_id w).const_sub (1 : ℂ)
  have h := (hasDerivAt_id w).mul hSub
  change HasDerivAt (fun z : ℂ ↦ z * (1 - z)) (1 * (1 - w) + w * (-1)) w at h
  convert h using 1
  ring

private theorem mixedThetaEntireReading_deriv (K : Type) [Field K] [NumberField K] (w : ℂ) :
    deriv (mixedThetaEntireReading K) w =
      (1 - 2 * w) * (Theta.mixedThetaPair K).Λ₀ w +
        w * (1 - w) * deriv (Theta.mixedThetaPair K).Λ₀ w := by
  exact (((poleFactor_hasDerivAt w).mul
    ((Theta.mixedThetaPair K).differentiable_Λ₀ w).hasDerivAt).sub_const _).deriv

/-- At a zero, substitute the exact pole identity into the slope before
applying the tail budget. This certifies multiplicity one for the actual
Dedekind continuation from the truncated slope at the same input. -/
theorem mixedTheta_order_one_of_truncation_slope (K : Type) [Field K] [NumberField K]
    {R ρ : ℝ} (hR : 1 ≤ R) (hρ : 0 < ρ) {w : ℂ}
    (hlo : 0 < w.re) (hhi : w.re < 1) (hz : mixedThetaContinuation K w = 0)
    (hMargin : mixedThetaWeightedTail K R ρ / ρ <
      ‖deriv (mixedThetaTruncation K R) w +
        (Theta.mixedThetaPair K).f₀ * (1 - 2 * w) / (w * (1 - w)) ^ 2‖) :
    analyticOrderNatAt (mixedThetaContinuation K) w = 1 := by
  let p : ℂ := w * (1 - w)
  have hp : p ≠ 0 := by
    apply mul_ne_zero
    · intro he
      rw [he, Complex.zero_re, lt_self_iff_false] at hlo
      exact hlo
    · intro he
      have he' := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at he'
      linarith only [he', hhi]
  let shift := (Theta.mixedThetaPair K).f₀ * (1 - 2 * w) / p ^ 2
  have hZero := (mixedThetaEntireReading_zero_iff K w hlo hhi).mpr hz
  have hExact : (Theta.mixedThetaPair K).Λ₀ w = (Theta.mixedThetaPair K).f₀ / p := by
    apply (eq_div_iff hp).mpr
    rw [mul_comm]
    exact sub_eq_zero.mp hZero
  have hErr : ‖deriv (Theta.mixedThetaPair K).Λ₀ w -
      deriv (mixedThetaTruncation K R) w‖ ≤ mixedThetaWeightedTail K R ρ / ρ := by
    simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using
      mixedTheta_mellin_iteratedDeriv_error_le K 1 hR hρ hlo.le hhi.le
  have hLarge : deriv (Theta.mixedThetaPair K).Λ₀ w + shift ≠ 0 := by
    intro he
    have hEq : deriv (Theta.mixedThetaPair K).Λ₀ w - deriv (mixedThetaTruncation K R) w =
        -(deriv (mixedThetaTruncation K R) w + shift) := by
      linear_combination he
    rw [hEq, norm_neg] at hErr
    exact (not_lt_of_ge hErr) hMargin
  have hDerivEq : deriv (mixedThetaEntireReading K) w =
      p * (deriv (Theta.mixedThetaPair K).Λ₀ w + shift) := by
    rw [mixedThetaEntireReading_deriv, hExact]
    change (1 - 2 * w) * ((Theta.mixedThetaPair K).f₀ / p) + p * _ = p * _
    unfold shift
    field_simp
    ring
  have hDeriv : deriv (mixedThetaEntireReading K) w ≠ 0 := by
    rw [hDerivEq]
    exact mul_ne_zero hp hLarge
  have hOrder := ((mixedThetaEntireReading_differentiable K).analyticAt w).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    hZero hDeriv
  rw [← mixedThetaEntireReading_orderNat_eq_continuation K hlo hhi, analyticOrderNatAt, hOrder]
  rfl

#check @mixedTheta_uniform_derivative_cutoff
#check @mixedTheta_order_one_of_truncation_slope
#print axioms mixedTheta_uniform_derivative_cutoff
#print axioms mixedTheta_order_one_of_truncation_slope

end
end FieldTarget
