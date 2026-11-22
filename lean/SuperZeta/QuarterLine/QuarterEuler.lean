import SuperZeta.UnitSpectrum
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
open scoped Topology
open Complex MeasureTheory Asymptotics Set Filter
namespace SuperZeta.QuarterEuler

def floorKernel : ℝ → ℂ := (Ioi (1:ℝ)).indicator (fun x => ((Int.fract x : ℝ) : ℂ))

lemma kernel_meas : Measurable floorKernel :=
  (Complex.measurable_ofReal.comp measurable_fract).indicator measurableSet_Ioi

lemma kernel_bound (x : ℝ) : ‖floorKernel x‖ ≤ 1 := by
  by_cases h : 1 < x
  · simpa [floorKernel, h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
      using (Int.fract_lt_one x).le
  · simp [floorKernel, h]

lemma kernel_diff {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (fun z : ℂ => mellin floorKernel (-z)) w := by
  change DifferentiableAt ℂ ((mellin floorKernel) ∘ fun z : ℂ => -z) w
  apply DifferentiableAt.comp w _ (show DifferentiableAt ℂ (fun z : ℂ => -z) w by fun_prop)
  apply mellin_differentiableAt_of_isBigO_rpow (a:=0) (b:=-w.re-1)
  · apply (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2
    intro k _ hk
    exact (volume.integrableOn_of_bounded hk.measure_lt_top.ne
      kernel_meas.aestronglyMeasurable (Filter.Eventually.of_forall (fun x => kernel_bound x)))
  · apply isBigO_of_le
    intro x
    simpa using kernel_bound x
  · simpa using hw
  · refine isBigO_iff.mpr ⟨1, ?_⟩
    filter_upwards [(nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ)<1 by norm_num)) : Iio 1 ∈ 𝓝[Ioi 0] (0:ℝ))] with x hx
    simp [floorKernel,not_lt.mpr (le_of_lt (show x < 1 from hx))]
  · simp

lemma kernel_integral (w : ℂ) : mellin floorKernel (-w) =
    ∫ x : ℝ in Ioi 1, (x:ℂ)^(-(w+1)) * ((Int.fract x : ℝ) : ℂ) := by
  unfold mellin floorKernel
  simp_rw [smul_eq_mul, show -w-1= -(w+1) by ring]
  have h (x : ℝ) : (x:ℂ)^(-(w+1)) * (Ioi (1:ℝ)).indicator
      (fun y : ℝ => ((Int.fract y : ℝ) : ℂ)) x =
      (Ioi (1:ℝ)).indicator (fun y : ℝ => (y:ℂ)^(-(w+1)) * ((Int.fract y : ℝ) : ℂ)) x := by
    by_cases hx : 1 < x <;> simp [hx]
  simp_rw [h]
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))]

lemma kernel_norm_le (w : ℂ) (hw : 0 < w.re) :
    ‖mellin floorKernel (-w)‖ ≤ 1/w.re := by
  rw [kernel_integral]
  have he : -(w.re+1) < -1 := by linarith
  have hi := integrableOn_Ioi_rpow_of_lt he (show (0:ℝ)<1 by norm_num)
  calc
    _ ≤ ∫ x : ℝ in Ioi 1, x^(-(w.re+1)) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with x hx
      have hx' : 0 < x := lt_trans zero_lt_one hx
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx']
      simp only [neg_re, add_re, one_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hx'.le _) (Int.fract_lt_one x).le
    _ = _ := by rw [integral_Ioi_rpow_of_lt he one_pos]; simp


lemma frac_integrable {w : ℂ} (hw : 0 < w.re) :
    IntegrableOn (fun x : ℝ => (x:ℂ)^(-(w+1)) * ((Int.fract x : ℝ):ℂ)) (Ioi 1) := by
  refine (integrableOn_Ioi_rpow_of_lt (show -(w.re+1) < -1 by linarith) (show (0:ℝ)<1 by norm_num)).mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with x hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans zero_lt_one hx)]
    simp only [neg_re, add_re, one_re, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg (le_trans zero_le_one hx.le) _) (Int.fract_lt_one x).le

lemma zeta_integral_right {w : ℂ} (hw : 1 < w.re) :
    riemannZeta w = w/(w-1) - w*mellin floorKernel (-w) := by
  have hO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ‖(1 : ℕ → ℂ) k‖)
      =O[atTop] fun n : ℕ => (n:ℝ)^(1:ℝ) := by
    apply isBigO_of_le
    intro n
    simp
  have H := LSeries_eq_mul_integral' (1 : ℕ → ℂ) (r:=1) zero_le_one hw hO
  rw [LSeries_one_eq_riemannZeta hw] at H
  simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc,
    Nat.add_sub_cancel] at H
  rw [H, kernel_integral]
  have hm : ∀ x ∈ Ioi (1:ℝ), ((⌊x⌋₊:ℕ):ℂ) * (x:ℂ)^(-(w+1)) =
      (x:ℂ)^(-w) - (x:ℂ)^(-(w+1)) * ((Int.fract x:ℝ):ℂ) := by
    intro x hx
    have hp : 0 < x := lt_trans zero_lt_one hx
    have hn : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
    have hf : ((⌊x⌋₊:ℕ):ℂ) = (x:ℂ) - ((Int.fract x:ℝ):ℂ) := by
      exact_mod_cast (show (⌊x⌋₊ : ℝ)=x-Int.fract x by rw [natCast_floor_eq_intCast_floor hp.le]; unfold Int.fract; ring)
    rw [hf, show -w=1+(-(w+1)) by ring, Complex.cpow_add _ _ hn, Complex.cpow_one]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hm,
    integral_sub (integrableOn_Ioi_cpow_of_lt (show (-w).re < -1 by simpa using hw) one_pos)
      (frac_integrable (zero_lt_one.trans hw)),
    integral_Ioi_cpow_of_lt (show (-w).re < -1 by simpa using hw) one_pos, ofReal_one, one_cpow]
  rw [show -w+1 = -(w-1) by ring]
  simp only [div_eq_mul_inv, inv_neg, neg_mul, mul_neg, neg_neg, mul_sub]
  ring

lemma zeta_integral {w : ℂ} (hw : 0 < w.re) (hi : w.im ≠ 0) :
    riemannZeta w = w/(w-1) - w*mellin floorKernel (-w) := by
  let U : Set ℂ := {v | 0 < v.re} ∩ (if 0 < w.im then {v | 0 < v.im} else {v | v.im < 0})
  have hopen : IsOpen U := by
    dsimp [U]; split <;> apply IsOpen.inter <;> first | exact isOpen_Ioi.preimage continuous_re | exact isOpen_Ioi.preimage continuous_im | exact isOpen_Iio.preimage continuous_im
  have hconv : Convex ℝ U := by
    dsimp [U]; split <;> apply Convex.inter <;> first | exact convex_halfSpace_re_gt 0 | exact convex_halfSpace_im_gt 0 | exact convex_halfSpace_im_lt 0
  have memU (x : ℝ) (hx : 0<x) : (⟨x,w.im⟩:ℂ) ∈ U := by
    constructor
    · exact hx
    · by_cases h : 0 < w.im
      · simp [h]
      · simpa [h] using lt_of_le_of_ne (le_of_not_gt h) hi
  have hne (z : ℂ) (hz : z∈U) : z ≠ 1 := by
    rintro rfl
    simp [U] at hz; split at hz <;> simp at hz
  apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜:=ℂ) (U:=U) (f:=riemannZeta) (g:=fun z : ℂ => z/(z-1) - z*mellin floorKernel (-z)) (z₀:=⟨2,w.im⟩) _ _
      hconv.isPreconnected (memU _ (by norm_num)) _ (show w∈U from memU _ hw)
  · exact DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_riemannZeta (hne z hz)).differentiableWithinAt) hopen
  · apply DifferentiableOn.analyticOnNhd _ hopen
    intro z hz
    have h : z-1 ≠ 0 := sub_ne_zero.mpr (hne z hz)
    have hd : DifferentiableAt ℂ (fun u : ℂ => u) z := differentiableAt_id
    exact ((hd.div (hd.sub_const 1) h).sub
      (hd.mul (kernel_diff (w:=z) hz.1))).differentiableWithinAt
  · filter_upwards [(isOpen_Ioi.preimage continuous_re).mem_nhds (show 1 < (⟨2,w.im⟩:ℂ).re by norm_num)]
    exact fun z hz => zeta_integral_right hz

theorem zeta_half_bound {w : ℂ} (hw : w.re=1/2) (hi : w.im ≠ 0) :
    ‖riemannZeta w‖ ≤ 1+2*‖w‖ := by
  have hp : 0<w.re := by linarith
  have hnorm : ‖w-1‖ = ‖w‖ := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp only [Complex.normSq_apply, sub_re, sub_im, one_re, one_im, sub_zero, hw]
    ring
  have hn : w≠0 := by intro e; simp [e] at hp
  rw [zeta_integral hp hi]
  calc
    _ ≤ ‖w/(w-1)‖+‖w*mellin floorKernel (-w)‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_div, hnorm, div_self (norm_ne_zero_iff.mpr hn), norm_mul]
      have hb := kernel_norm_le w hp
      rw [hw] at hb
      norm_num at hb
      nlinarith [mul_le_mul_of_nonneg_left hb (norm_nonneg w)]

end SuperZeta.QuarterEuler
