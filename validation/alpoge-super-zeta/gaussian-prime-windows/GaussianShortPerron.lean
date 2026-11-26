import MellinContourShift
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! A linear cutoff whose transition can be placed strictly between two
integers. Its Mellin transform has two height bounds with different
dependence on the transition width. -/

namespace AlpogeSuperZeta

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

def perronTent (b v : ℝ) : ℂ := (max (b - v) 0 : ℝ)

def shortPerronKernel (d v : ℝ) : ℂ :=
  (perronTent (1 + d) v - perronTent 1 v) / (d : ℂ)

def shortPerronMultiplier (d : ℝ) (z : ℂ) : ℂ :=
  (((1 + d : ℝ) : ℂ) ^ (z + 1) - 1) / ((d : ℂ) * z * (z + 1))

theorem shortPerronKernel_eq_one {d v : ℝ} (hd : 0 < d) (hv : v ≤ 1) :
    shortPerronKernel d v = 1 := by
  rw [shortPerronKernel, perronTent, perronTent,
    max_eq_left (by linarith : 0 ≤ 1 + d - v), max_eq_left (by linarith : 0 ≤ 1 - v),
    ← ofReal_sub, show 1 + d - v - (1 - v) = d by ring,
    div_self (ofReal_ne_zero.mpr hd.ne')]

theorem shortPerronKernel_eq_zero {d v : ℝ} (hd : 0 < d) (hv : 1 + d ≤ v) :
    shortPerronKernel d v = 0 := by
  simp [shortPerronKernel, perronTent, max_eq_right (by linarith : 1 + d - v ≤ 0),
    max_eq_right (by linarith : 1 - v ≤ 0)]

theorem shortPerronKernel_continuous (d : ℝ) : Continuous (shortPerronKernel d) := by
  unfold shortPerronKernel perronTent
  fun_prop

theorem shortPerronKernel_norm_le_power {d : ℝ} (hd : 0 < d) (hd₁ : d ≤ 1) (v : ℝ)
    (hv : 0 < v) : ‖shortPerronKernel d v‖ ≤ 4 * v ^ (-(2 : ℝ)) := by
  by_cases hz : 1 + d ≤ v
  · rw [shortPerronKernel_eq_zero hd hz, norm_zero]
    positivity
  have h₀ : 0 ≤ max (1 + d - v) 0 - max (1 - v) 0 := by
    exact sub_nonneg.mpr (max_le_max_right _ (by linarith))
  have h₁ : max (1 + d - v) 0 - max (1 - v) 0 ≤ d := by
    rw [sub_le_iff_le_add]
    apply max_le
    · linarith [le_max_left (1 - v) 0]
    · linarith [le_max_right (1 - v) 0]
  have hV : v ≤ 2 := by linarith
  rw [shortPerronKernel, perronTent, perronTent, ← ofReal_sub, norm_div, norm_real, norm_real,
    Real.norm_of_nonneg h₀, Real.norm_of_nonneg hd.le, Real.rpow_neg hv.le, Real.rpow_two]
  calc
    _ ≤ 1 := (div_le_one hd).mpr h₁
    _ ≤ _ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hv 2), one_mul]
      nlinarith [sq_nonneg (v - 2)]

theorem perronTent_hasMellin {b : ℝ} (hb : 0 < b) {z : ℂ} (hz : 0 < z.re) :
    HasMellin (perronTent b) z (((b : ℂ) ^ (z + 1)) / (z * (z + 1))) := by
  have hz₀ : z ≠ 0 := fun h => by simp [h] at hz
  have hz₁ : z + 1 ≠ 0 := fun h => by
    have h' := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at h'
    linarith
  have hRe : -1 < (z - 1).re := by rw [sub_re, one_re]; linarith
  have he (v : ℝ) (hv : v ∈ Ioi (0 : ℝ)) :
      (v : ℂ) ^ (z - 1) • perronTent b v =
        (Iic b).indicator (fun t : ℝ => (b : ℂ) * (t : ℂ) ^ (z - 1) - (t : ℂ) ^ z) v := by
    by_cases ht : v ≤ b
    · rw [indicator_of_mem (mem_Iic.mpr ht), perronTent, max_eq_left (sub_nonneg.mpr ht),
        ofReal_sub, smul_eq_mul, mul_sub, mul_comm ((v : ℂ) ^ (z - 1)) (b : ℂ)]
      rw [show (v : ℂ) ^ (z - 1) * (v : ℂ) = (v : ℂ) ^ z by
        calc
          _ = (v : ℂ) ^ (z - 1) * (v : ℂ) ^ (1 : ℂ) := by rw [cpow_one]
          _ = _ := by rw [← cpow_add _ _ (ofReal_ne_zero.mpr (ne_of_gt hv)), sub_add_cancel] ]
    · simp [indicator_of_notMem (show v ∉ Iic b from ht), perronTent,
        max_eq_right (sub_nonpos.mpr (le_of_not_ge ht))]
  have hM : mellin (perronTent b) z = ((b : ℂ) ^ (z + 1)) / (z * (z + 1)) := by
    rw [mellin, setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
      show Ioi (0 : ℝ) ∩ Iic b = Ioc 0 b from rfl, ← intervalIntegral.integral_of_le hb.le]
    have hI₀ : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (z - 1)) volume 0 b :=
      intervalIntegral.intervalIntegrable_cpow' hRe
    have hI₁ : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ z) volume 0 b :=
      intervalIntegral.intervalIntegrable_cpow' (by linarith)
    rw [intervalIntegral.integral_sub (hI₀.const_mul _) hI₁, intervalIntegral.integral_const_mul,
      integral_cpow (Or.inl hRe), integral_cpow (Or.inl (by linarith : -1 < z.re)),
      sub_add_cancel, ofReal_zero, zero_cpow hz₀, zero_cpow hz₁, sub_zero, sub_zero]
    have hB : (b : ℂ) * (b : ℂ) ^ z = (b : ℂ) ^ (z + 1) := by
      rw [mul_comm, cpow_add _ _ (ofReal_ne_zero.mpr hb.ne'), cpow_one]
    rw [← mul_div_assoc, hB]
    field_simp
    ring
  refine ⟨Integrable.of_integral_ne_zero ?_, hM⟩
  exact hM.trans_ne (div_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hb.ne')))
    (mul_ne_zero hz₀ hz₁))

theorem shortPerronKernel_hasMellin {d : ℝ} (hd : 0 < d) {z : ℂ} (hz : 0 < z.re) :
    HasMellin (shortPerronKernel d) z (shortPerronMultiplier d z) := by
  have h₁ := perronTent_hasMellin (show 0 < 1 + d by linarith) hz
  have h₂ := perronTent_hasMellin one_pos hz
  have hSub := hasMellin_sub h₁.1 h₂.1
  refine ⟨hSub.1.div_const _, ?_⟩
  rw [show shortPerronKernel d = fun v => (perronTent (1 + d) v - perronTent 1 v) / (d : ℂ)
      from rfl, mellin_div_const, hSub.2, h₁.2, h₂.2]
  simp only [ofReal_one, one_cpow, shortPerronMultiplier, ← sub_div, div_div]
  ring

theorem shortPerronMultiplier_one {d : ℝ} (hd : 0 < d) :
    shortPerronMultiplier d 1 = ((1 + d / 2 : ℝ) : ℂ) := by
  unfold shortPerronMultiplier
  rw [show (1 : ℂ) + 1 = ((2 : ℕ) : ℂ) by norm_num, cpow_natCast]
  push_cast
  field_simp [ofReal_ne_zero.mpr hd.ne']
  ring

theorem shortPerronMultiplier_analytic (d : ℝ) (hd : 0 < d) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (shortPerronMultiplier d) z := by
  have hz₀ : z ≠ 0 := fun h => by simp [h] at hz
  have hz₁ : z + 1 ≠ 0 := fun h => by
    have h' := congrArg Complex.re h
    simp only [add_re, one_re, zero_re] at h'
    linarith
  have hB : (((1 + d : ℝ) : ℂ)) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hC : Differentiable ℂ (fun w : ℂ => (((1 + d : ℝ) : ℂ)) ^ (w + 1)) :=
    (differentiable_id.add_const _).const_cpow (Or.inl hB)
  exact ((hC.analyticAt z).sub analyticAt_const).div
    ((analyticAt_const.mul analyticAt_id).mul (analyticAt_id.add analyticAt_const))
    (mul_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hd.ne') hz₀) hz₁)

#print axioms shortPerronKernel_eq_one
#print axioms shortPerronKernel_eq_zero
#print axioms shortPerronKernel_continuous
#print axioms shortPerronKernel_norm_le_power
#print axioms perronTent_hasMellin
#print axioms shortPerronKernel_hasMellin
#print axioms shortPerronMultiplier_one
#print axioms shortPerronMultiplier_analytic

end
end AlpogeSuperZeta
