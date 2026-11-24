import NativeDottieRay
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Mellin continuation of the actual relative logarithms at the two
native Dottie angles. The scale change supplies the existing exponential
tail convention of `EvenMellin.Data`. -/
noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

def relativeOffset (positiveAngle : Bool) (x : ℝ) : ℝ :=
  rayOffset positiveAngle x / referenceRay x

theorem realKernel_eq (b : Bool) (x : ℝ) :
    realKernel b x = Real.log (1 + relativeOffset b x) := by
  unfold realKernel determinantRay relativeOffset
  rw [add_div, div_self (reference_ray_pos x).ne']

theorem kernel_continuous (b : Bool) : Continuous (kernel b) := by
  apply Complex.continuous_ofReal.comp
  unfold realKernel
  apply Continuous.log
  · apply Continuous.div _ _ (fun x => (reference_ray_pos x).ne')
    · unfold determinantRay rayOffset referenceRay
      fun_prop
    · unfold referenceRay
      fun_prop
  · intro x
    exact (div_pos (determinant_ray_pos b x) (reference_ray_pos x)).ne'

private theorem ray_ratio_lower (b : Bool) (x : ℝ) :
    (3/4 : ℝ) ≤ determinantRay b x / referenceRay x := by
  rw [le_div_iff₀ (reference_ray_pos x)]
  have hs := sineSign_sq b
  have he : determinantRay b x - (3/4)*referenceRay x =
      1/4 + (4/3)*(x-sineSign b*Real.sinh x/2)^2 := by
    unfold determinantRay rayOffset referenceRay
    linear_combination -(Real.sinh x ^ 2/3)*hs
  nlinarith only [he, sq_nonneg (x-sineSign b*Real.sinh x/2)]

private theorem log_bound {v : ℝ} (hv : (3/4 : ℝ) ≤ v) :
    |Real.log v| ≤ (4/3)*|v-1| := by
  have hpos : 0 < v := by linarith
  rcases le_or_gt v 1 with h | h
  · have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at hinv
    rw [abs_of_nonpos (Real.log_nonpos hpos.le h), abs_of_nonpos (sub_nonpos.mpr h)]
    refine hinv.trans ?_
    rw [show v⁻¹-1 = (1-v)/v by field_simp [hpos.ne'],
      div_le_iff₀ hpos]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hv) (sub_nonneg.mpr h)]
  · rw [abs_of_nonneg (Real.log_nonneg h.le), abs_of_nonneg (sub_nonneg.mpr h.le)]
    exact (Real.log_le_sub_one_of_pos hpos).trans (by linarith)

private theorem sinh_cosh_bounds {x : ℝ} (hx : 0 ≤ x) :
    x ≤ Real.sinh x ∧ 0 ≤ Real.sinh x ∧ Real.sinh x ≤ Real.cosh x := by
  refine ⟨Real.self_le_sinh_iff.mpr hx, Real.sinh_nonneg_iff.mpr hx, ?_⟩
  rw [Real.sinh_eq, Real.cosh_eq]
  linarith [Real.exp_pos (-x)]

theorem kernel_tail_bound (b : Bool) {x : ℝ} (hx : 0 ≤ x) :
    ‖kernel b x‖ ≤ (128/9) * Real.exp (-x/2) := by
  have hcos : 0 < Real.cosh x := Real.cosh_pos x
  obtain ⟨hxs, hs, hsc⟩ := sinh_cosh_bounds hx
  have hdiv : x / Real.cosh x ≤ 1 := (div_le_one hcos).mpr (hxs.trans hsc)
  have href : Real.cosh x ^ 2 ≤ referenceRay x := by
    unfold referenceRay
    nlinarith only [Real.cosh_sq_sub_sinh_sq x, sq_nonneg (Real.sinh x)]
  have hsg : |sineSign b| = 1 := by cases b <;> norm_num [sineSign]
  have hn : |x^2-sineSign b*(x*Real.sinh x)| ≤ x * (2*Real.cosh x) := by
    calc
      _ ≤ |x^2| + |sineSign b * (x*Real.sinh x)| := abs_sub _ _
      _ = x*(x+Real.sinh x) := by
        rw [abs_of_nonneg (sq_nonneg x), abs_mul, hsg, one_mul,
          abs_of_nonneg (mul_nonneg hx hs)]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hxs.trans hsc]) hx
  have hoff : |relativeOffset b x| ≤ (8/3)*(x/Real.cosh x) := by
    unfold relativeOffset rayOffset
    rw [abs_div, abs_mul, abs_of_pos (reference_ray_pos x),
      abs_of_pos (by norm_num : (0 : ℝ)<4/3), div_le_iff₀ (reference_ray_pos x)]
    calc
      _ ≤ (4/3)*(x*(2*Real.cosh x)) := by gcongr
      _ = (8/3)*(x/Real.cosh x)*(Real.cosh x)^2 := by field_simp; ring
      _ ≤ _ := by gcongr
  have hce : Real.exp x ≤ 2*Real.cosh x := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-x)]
  have hxexp : x ≤ 2*Real.exp (x/2) := by linarith [Real.add_one_le_exp (x/2)]
  have he : x/Real.cosh x ≤ 4*Real.exp (-x/2) := by
    rw [div_le_iff₀ hcos]
    calc
      x ≤ 2*Real.exp (x/2) := hxexp
      _ = 4*Real.exp (-x/2)*(Real.exp x/2) := by
        have h := Real.exp_add (-x/2) x
        rw [show -x/2+x=x/2 by ring] at h
        rw [h]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith : Real.exp x/2 ≤ Real.cosh x)
        (by positivity)
  have hid : determinantRay b x / referenceRay x - 1 = relativeOffset b x := by
    unfold determinantRay relativeOffset
    rw [add_div, div_self (reference_ray_pos x).ne', add_sub_cancel_left]
  rw [kernel, Complex.norm_real, Real.norm_eq_abs, realKernel]
  calc
    _ ≤ (4/3)*|determinantRay b x / referenceRay x - 1| :=
      log_bound (ray_ratio_lower b x)
    _ = (4/3)*|relativeOffset b x| := by rw [hid]
    _ ≤ (4/3)*((8/3)*(x/Real.cosh x)) := by gcongr
    _ ≤ (4/3)*((8/3)*(4*Real.exp (-x/2))) := by gcongr
    _ = _ := by ring

private theorem analyticAt_dslope {f : ℝ → ℝ} {x : ℝ} (h : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (dslope f x) x := by
  obtain ⟨_, hp⟩ := h
  exact ⟨_, hp.has_fpower_series_dslope_fslope⟩

private theorem sinh_analytic : AnalyticAt ℝ Real.sinh 0 := by
  have h₁ : AnalyticAt ℝ Real.exp 0 := analyticAt_rexp
  have h₂ : AnalyticAt ℝ (fun x : ℝ => Real.exp (-x)) 0 :=
    (by simpa using h₁ : AnalyticAt ℝ Real.exp (-(0:ℝ))).comp analyticAt_id.neg
  rw [funext Real.sinh_eq]
  simp only [div_eq_mul_inv]
  exact (h₁.sub h₂).mul analyticAt_const

private def offsetFactor (b : Bool) (x : ℝ) : ℝ :=
  (4/3)*(1 - sineSign b * dslope Real.sinh 0 x) / referenceRay x

private theorem offset_factor_eq (b : Bool) (x : ℝ) :
    relativeOffset b x = x^2 * offsetFactor b x := by
  by_cases h : x = 0
  · simp [h, relativeOffset, rayOffset]
  · unfold relativeOffset rayOffset offsetFactor
    rw [dslope_of_ne _ h, slope_def_field, Real.sinh_zero, sub_zero, sub_zero]
    field_simp [h, (reference_ray_pos x).ne']
    ring

private def logFactor (b : Bool) (x : ℝ) : ℝ :=
  offsetFactor b x * dslope Real.log 1 (1 + relativeOffset b x)

private theorem kernel_factor_eq (b : Bool) (x : ℝ) :
    realKernel b x = x^2 * logFactor b x := by
  rw [realKernel_eq, logFactor, ← mul_assoc, ← offset_factor_eq]
  by_cases h : relativeOffset b x = 0
  · simp [h]
  · have hn : 1 + relativeOffset b x ≠ 1 := by
      intro e
      exact h (by linarith only [e])
    rw [dslope_of_ne _ hn,
      slope_def_field, Real.log_one, sub_zero, add_sub_cancel_left]
    field_simp [h]

private theorem offsetFactor_analytic (b : Bool) : AnalyticAt ℝ (offsetFactor b) 0 := by
  have h := analyticAt_dslope sinh_analytic
  have hd : AnalyticAt ℝ referenceRay 0 := by
    unfold referenceRay
    exact analyticAt_const.add (analyticAt_const.mul (sinh_analytic.pow 2))
  unfold offsetFactor
  exact (analyticAt_const.mul (analyticAt_const.sub (analyticAt_const.mul h))).div hd
    (reference_ray_pos 0).ne'

private theorem logFactor_analytic (b : Bool) : AnalyticAt ℝ (logFactor b) 0 := by
  have hL := analyticAt_dslope (analyticAt_log (by norm_num : (0:ℝ)<1))
  have harg : AnalyticAt ℝ (fun x : ℝ => 1+relativeOffset b x) 0 := by
    simp_rw [offset_factor_eq]
    exact analyticAt_const.add ((analyticAt_id.pow 2).mul (offsetFactor_analytic b))
  have harg₀ : 1 + relativeOffset b 0 = 1 := by simp [offset_factor_eq]
  have hh : AnalyticAt ℝ (dslope Real.log 1) (1 + relativeOffset b 0) := by
    rw [harg₀]
    exact hL
  unfold logFactor
  exact (offsetFactor_analytic b).mul
    (AnalyticAt.comp' (g := dslope Real.log 1) (f := fun x : ℝ => 1 + relativeOffset b x)
      (x := 0) hh harg)

private theorem logFactor_even (b : Bool) (x : ℝ) : logFactor b (-x) = logFactor b x := by
  by_cases hx : x = 0
  · simp [hx]
  have hk : realKernel b (-x) = realKernel b x := by
    simp [realKernel, determinantRay, referenceRay, rayOffset, Real.sinh_neg, neg_sq]
  rw [kernel_factor_eq, kernel_factor_eq, neg_sq] at hk
  exact mul_left_cancel₀ (pow_ne_zero _ hx) hk

private theorem logFactor_at_zero (b : Bool) :
    logFactor b 0 = (4/3)*(1 - sineSign b) := by
  unfold logFactor offsetFactor
  rw [offset_factor_eq]
  simp [dslope_same, Real.deriv_sinh, Real.deriv_log, referenceRay]

private def scaledFactor (b : Bool) (x : ℝ) : ℝ := 4 * logFactor b (2*x)

def scaledKernel (b : Bool) (x : ℝ) : ℂ := kernel b (2*x)

private theorem scaled_factor_eq (b : Bool) (x : ℝ) :
    scaledKernel b x = ((x^2*scaledFactor b x : ℝ) : ℂ) := by
  rw [scaledKernel, kernel, kernel_factor_eq, scaledFactor, mul_pow]
  push_cast
  ring

private theorem scaledFactor_analytic (b : Bool) : AnalyticAt ℝ (scaledFactor b) 0 := by
  have h : AnalyticAt ℝ (fun x : ℝ => 2*x) 0 := analyticAt_const.mul analyticAt_id
  have h' : AnalyticAt ℝ (logFactor b) ((fun x : ℝ => 2*x) 0) := by
    simpa using logFactor_analytic b
  exact analyticAt_const.mul (h'.comp h)

private def raw (b : Bool) (n : ℕ) : ℝ := iteratedDeriv n (scaledFactor b) 0 / n.factorial

def coeff (b : Bool) (n : ℕ) : ℂ := (raw b (2*n) : ℝ)

private theorem raw_odd (b : Bool) (n : ℕ) : raw b (2*n+1) = 0 := by
  have he : (fun x : ℝ => scaledFactor b (-x)) = scaledFactor b := by
    funext x
    rw [scaledFactor, scaledFactor, mul_neg, logFactor_even]
  have h := iteratedDeriv_comp_neg (2*n+1) (scaledFactor b) 0
  rw [he, neg_zero, pow_succ, pow_mul, neg_one_sq, one_pow] at h
  simp only [one_mul, neg_one_smul] at h
  unfold raw
  rw [show iteratedDeriv (2*n+1) (scaledFactor b) 0 = 0 by linarith]
  simp

private theorem even_partial (b : Bool) (x : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range (2*N), raw b j*x^j =
      ∑ k ∈ Finset.range N, raw b (2*k)*x^(2*k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2*(N+1)=2*N+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ (n:=2*N), ih, raw_odd, zero_mul, add_zero,
      Finset.sum_range_succ]

private theorem scaled_taylor (b : Bool) (N : ℕ) :
    (fun x : ℝ => scaledKernel b x - ∑ k ∈ Finset.range N,
      coeff b k * (x:ℂ)^(2*(k+1))) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-(-((2*(N+1):ℕ):ℝ)))) := by
  have h := (scaledFactor_analytic b).hasFPowerSeriesAt.isBigO_sub_partialSum_pow (2*N)
  simp only [zero_add, FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul] at h
  change (fun x : ℝ => scaledFactor b x - ∑ j ∈ Finset.range (2*N), raw b j*x^j)
    =O[_] _ at h
  simp_rw [even_partial] at h
  obtain ⟨C, hC⟩ := isBigO_iff.mp h
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [hC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hC hx
  change 0 < x at hx
  have hmul := mul_le_mul_of_nonneg_left hC (sq_nonneg x)
  have he : scaledKernel b x - ∑ k ∈ Finset.range N,
      coeff b k*(x:ℂ)^(2*(k+1)) =
      ((x^2 * (scaledFactor b x - ∑ k ∈ Finset.range N,
        raw b (2*k)*x^(2*k)) : ℝ) : ℂ) := by
    simp only [scaled_factor_eq, coeff, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_sum, mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [show 2*(k+1)=2*k+2 by omega, pow_add]
    ring
  have hnN : 0 ≤ x^(2*N) := pow_nonneg hx.le _
  have hnM : 0 ≤ x^(2*(N+1)) := pow_nonneg hx.le _
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg x),
    neg_neg, Real.rpow_natCast, Real.norm_eq_abs, abs_of_nonneg hnM]
  have hpoly : x^2*(C*x^(2*N)) = C*x^(2*(N+1)) := by
    rw [show 2*(N+1)=2*N+2 by omega, pow_add]
    ring
  simpa only [Real.norm_eq_abs, abs_of_pos hx, abs_of_nonneg hnN, hpoly] using hmul

theorem data (b : Bool) : SuperZeta.EvenMellin.Data (scaledKernel b) (coeff b) := by
  refine ⟨?_, ?_, scaled_taylor b⟩
  · have hc : Continuous (scaledKernel b) :=
      (kernel_continuous b).comp (continuous_const.mul continuous_id)
    exact hc.continuousOn.locallyIntegrableOn measurableSet_Ioi
  · refine isBigO_iff.mpr ⟨128/9, ?_⟩
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa [scaledKernel, show -(2*x)/2 = -1*x by ring] using
      kernel_tail_bound b (show 0 ≤ 2*x by positivity)

def correction (b : Bool) (s : ℂ) : ℂ :=
  (2 : ℂ)^(-(2*s)) * SuperZeta.EvenMellin.continuation (scaledKernel b) (coeff b) s

theorem correction_entire (b : Bool) : Differentiable ℂ (correction b) := by
  unfold correction
  have h₁ : Differentiable ℂ (fun s : ℂ => (2:ℂ)^(-(2*s))) := by
    simp only [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0)]
    fun_prop
  exact h₁.mul (SuperZeta.EvenMellin.continuation_entire (data b))

theorem correction_integral (b : Bool) {s : ℂ} (hs : s.re < 1) :
    correction b s = 2*s*Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ) *
      mellin (kernel b) (-(2*s)) := by
  have h := SuperZeta.EvenMellin.continuation_eq (data b) 0
    (by simpa using hs)
  have he : SuperZeta.EvenMellin.remainder (scaledKernel b) (coeff b) 0 = scaledKernel b := by
    funext x
    simp [SuperZeta.EvenMellin.remainder]
  simp only [correction, h, SuperZeta.EvenMellin.patch, he, Finset.range_zero,
    Finset.sum_empty, sub_zero]
  change (2:ℂ)^(-(2*s)) *
    (2*s*Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ) * mellin (scaledKernel b) (-(2*s))) = _
  rw [show scaledKernel b = fun x => kernel b (2*x) from rfl,
    mellin_comp_mul_left _ _ (by norm_num : (0:ℝ)<2), smul_eq_mul, neg_neg]
  simp only [Complex.ofReal_ofNat, Complex.cpow_neg]
  have hn : (2 : ℂ)^(2*s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  calc
    _ = ((2:ℂ)^(2*s))⁻¹ * (2:ℂ)^(2*s) *
        (2*s*Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ) * mellin (kernel b) (-(2*s))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn, one_mul]

theorem correction_one (b : Bool) : correction b 1 = ((4/3)*(1-sineSign b) : ℝ) := by
  have h := SuperZeta.EvenMellin.continuation_succ (data b) 0
  simp only [Nat.cast_zero, zero_add] at h
  rw [correction, h]
  norm_num [coeff, raw, scaledFactor, logFactor_at_zero, Complex.cpow_neg, Complex.cpow_two]
  ring

theorem archived_first_corrections : correction false 1 = 0 ∧ correction true 1 = 8/3 := by
  constructor <;> rw [correction_one] <;> norm_num [sineSign]

#print axioms kernel_tail_bound
#print axioms data
#print axioms correction_entire
#print axioms correction_integral
#print axioms archived_first_corrections

end DottieOriented.NativeSpectrum
end
