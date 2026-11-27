import DedekindDiskTaylorError
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecificLimits.Basic

/-! On disks with fixed strip clearance the analytic allowance can be made
arbitrarily small with one cutoff and degree for every center height. -/

namespace FieldTarget

open Complex Filter MeasureTheory Set
open DedekindZetaZeroFree.AbelianQuotient
open scoped Topology

noncomputable section

theorem mixedThetaWeightedTail_zero_tendsto (K : Type) [Field K] [NumberField K] :
    Tendsto (fun cut : ℝ ↦ mixedThetaWeightedTail K cut 0) atTop (𝓝 0) := by
  have weighted (f : ℝ → ℝ) :
      Tendsto (fun cut : ℝ ↦ 2 * ∫ t : ℝ in Ioi cut, f t) atTop (𝓝 0) := by
    have h := tendsto_integral_Ioi_zero (μ := volume) (f := f) (b := id) tendsto_id
    simpa only [id_eq, mul_zero] using h.const_mul (2 : ℝ)
  simp only [mixedThetaWeightedTail, Real.rpow_zero, one_mul]
  exact weighted _

private theorem circleAllowance_le_of_clearance (K : Type) [Field K] [NumberField K]
    {cut ρ δ : ℝ} {c : ℂ} (hδ : 0 < δ)
    (hLeft : ρ + δ ≤ c.re) (hRight : c.re ≤ 1 - ρ - δ) :
    mixedThetaCompletedCircleAllowance K cut c ρ ≤
      mixedThetaWeightedTail K 1 0 + mixedThetaWeightedTail K cut 0 +
        ‖(Theta.mixedThetaPair K).f₀‖ / (δ * δ) := by
  have hNorm₀ : c.re ≤ ‖c‖ := (le_abs_self _).trans (Complex.abs_re_le_norm c)
  have hNorm₁ : 1 - c.re ≤ ‖1 - c‖ := by
    simpa only [Complex.sub_re, Complex.one_re] using
      (le_abs_self (1 - c).re).trans (Complex.abs_re_le_norm (1 - c))
  have h₀ : δ ≤ ‖c‖ - ρ := by linarith only [hLeft, hNorm₀]
  have h₁ : δ ≤ ‖1 - c‖ - ρ := by linarith only [hRight, hNorm₁]
  unfold mixedThetaCompletedCircleAllowance
  exact add_le_add le_rfl (div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hδ hδ)
    (mul_le_mul h₀ h₁ hδ.le (hδ.le.trans h₀)))

theorem exists_mixedThetaCompletedTaylorAllowance_le_uniform_height
    (K : Type) [Field K] [NumberField K] {ρ r δ ε : ℝ}
    (hr₀ : 0 ≤ r) (hr : r < ρ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ cut : ℝ, 1 ≤ cut ∧ ∃ n : ℕ, 1 ≤ n ∧
      ∀ c : ℂ, ρ + δ ≤ c.re → c.re ≤ 1 - ρ - δ →
        mixedThetaCompletedTaylorAllowance K cut c ρ r n ≤ ε := by
  have hHalf : (0 : ℝ) < ε / 2 := by linarith only [hε]
  obtain ⟨cut₀, hCut₀⟩ := eventually_atTop.mp
    ((mixedThetaWeightedTail_zero_tendsto K).eventually (gt_mem_nhds hHalf))
  let cut : ℝ := max 1 cut₀
  have hCut := hCut₀ cut (le_max_right _ _)
  let M := mixedThetaWeightedTail K 1 0 + mixedThetaWeightedTail K cut 0 +
    ‖(Theta.mixedThetaPair K).f₀‖ / (δ * δ)
  have hρ : 0 < ρ := hr₀.trans_lt hr
  have hq₀ : 0 ≤ r / ρ := div_nonneg hr₀ hρ.le
  have hq₁ : r / ρ < 1 := (div_lt_one hρ).mpr hr
  have hGeom : Tendsto (fun n : ℕ ↦ M * (r / ρ) ^ n / (1 - r / ρ)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).const_mul M).div_const (1 - r / ρ)
  obtain ⟨n₀, hN₀⟩ := eventually_atTop.mp (hGeom.eventually (gt_mem_nhds hHalf))
  let n := max 1 n₀
  have hNum := hN₀ n (le_max_right _ _)
  refine ⟨cut, le_max_left _ _, n, le_max_left _ _, ?_⟩
  intro c hLeft hRight
  have hBound : mixedThetaCompletedCircleAllowance K cut c ρ ≤ M :=
    circleAllowance_le_of_clearance K hδ hLeft hRight
  have hA := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hBound (pow_nonneg hq₀ n))
    (by linarith only [hq₁] : 0 ≤ 1 - r / ρ)
  have hFinal : mixedThetaWeightedTail K cut 0 + M * (r / ρ) ^ n / (1 - r / ρ) ≤ ε := by
    linarith only [hCut, hNum]
  unfold mixedThetaCompletedTaylorAllowance
  exact (add_le_add le_rfl hA).trans hFinal

#check @exists_mixedThetaCompletedTaylorAllowance_le_uniform_height
#print axioms mixedThetaWeightedTail_zero_tendsto
#print axioms exists_mixedThetaCompletedTaylorAllowance_le_uniform_height

end

end FieldTarget
