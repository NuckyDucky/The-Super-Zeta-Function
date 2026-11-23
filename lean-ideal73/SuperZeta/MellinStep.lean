import SuperZeta.Kernel
import Mathlib.Analysis.Complex.RemovableSingularity

/-! First continuation of the cosine determinant correction. Removing the
quadratic Taylor term near zero extends the integral to Re(s) < 2. The
sine prefactor removes its apparent pole at s = 1 and gives J(1) = q. -/
noncomputable section
namespace SuperZeta.Reference
open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology

private def cutoff : ℝ → ℂ := (Ioc (0:ℝ) 1).indicator fun x => (x:ℂ)^2

/-- Kernel after subtracting the first term on the unit interval. -/
def subtractedKernel (q x : ℝ) : ℂ := logKernel q x - (q:ℂ)*cutoff x

private theorem cutoff_hasMellin {v : ℂ} (hv : -2 < v.re) :
    HasMellin cutoff v (1/(v+2)) := by
  have h := hasMellin_cpow_Ioc (2:ℂ) (s:=v) (by norm_num; linarith)
  simpa only [cutoff, Complex.cpow_two] using h

private theorem subtracted_local {q : ℝ} (hq : 0 ≤ q) :
    LocallyIntegrableOn (subtractedKernel q) (Ioi 0) := by
  have hpow : Continuous (fun x : ℝ => (x:ℂ)^2) := by fun_prop
  have hcut : LocallyIntegrable cutoff := hpow.locallyIntegrable.indicator measurableSet_Ioc
  exact (kernel_locally_integrable hq).sub (fun x hx =>
    (hcut.locallyIntegrableOn _ x hx).smul (q:ℂ))

private theorem subtracted_top {q : ℝ} (hq : 0 ≤ q) :
    subtractedKernel q =O[atTop] (fun x : ℝ => Real.exp (-1*x)) := by
  apply (kernel_at_top hq).congr' _ (Filter.EventuallyEq.rfl)
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  simp [subtractedKernel,cutoff, not_le.mpr hx]

private theorem subtracted_zero {q : ℝ} (hq : 0 ≤ q) :
    subtractedKernel q =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-4 : ℝ))) := by
  apply (kernel_remainder_at_zero hq).congr' _ (Filter.EventuallyEq.rfl)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
      (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))] with x hx hlt
  have hm : x ∈ Ioc (0:ℝ) 1 := ⟨hx, hlt.le⟩
  simp [subtractedKernel,cutoff,hm]

theorem subtracted_converges {q : ℝ} (hq : 0 ≤ q) {s : ℂ} (hs : s.re < 2) :
    MellinConvergent (subtractedKernel q) (-(2*s)) := by
  apply mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
    (subtracted_local hq) (subtracted_top hq) (subtracted_zero hq)
  simp [two_mul]
  linarith

private def sinePhase (s : ℂ) : ℂ := Complex.sin ((Real.pi:ℂ)*s)

private theorem sinePhase_entire : Differentiable ℂ sinePhase := by
  unfold sinePhase
  fun_prop

private theorem sinePhase_one : sinePhase 1 = 0 := by simp [sinePhase]

private theorem sinePhase_deriv : deriv sinePhase 1 = -(Real.pi:ℂ) := by
  have h := (Complex.hasDerivAt_sin ((Real.pi:ℂ)*1)).comp (1:ℂ)
    ((hasDerivAt_id (1:ℂ)).const_mul (Real.pi:ℂ))
  change deriv (fun x : ℂ => Complex.sin ((Real.pi:ℂ)*x)) 1 = _
  simpa [Function.comp_def] using h.deriv

/-- The divided difference supplies the removable value at the first pole. -/
def correctionToTwo (q : ℝ) (s : ℂ) : ℂ :=
  2*s*sinePhase s/(Real.pi:ℂ) * mellin (subtractedKernel q) (-(2*s))
    - (q:ℂ)*s/(Real.pi:ℂ)*dslope sinePhase 1 s

/-- The first continued formula agrees with the original convergent integral. -/
theorem correctionToTwo_eq {q : ℝ} (hq : 0 ≤ q) {s : ℂ} (hs : s.re < 1) :
    correctionToTwo q s = correction q s := by
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  have hv : -2 < (-(2*s)).re := by simp [two_mul]; linarith
  have ho : MellinConvergent (logKernel q) (-(2*s)) :=
    mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
      (kernel_locally_integrable hq) (kernel_at_top hq) (kernel_at_zero hq) hv
  have hc := cutoff_hasMellin hv
  have hm := (hasMellin_sub ho (hc.1.const_smul (q:ℂ))).2
  have he : mellin (subtractedKernel q) (-(2*s)) =
      mellin (logKernel q) (-(2*s)) - (q:ℂ)*(1/(-(2*s)+2)) := by
    rw [mellin_const_smul, hc.2] at hm
    exact hm
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn : -(2*s)+2 ≠ 0 := by intro h; apply hs1; linear_combination -h/2
  rw [correctionToTwo, correction, sqrt_transform, he, dslope_of_ne _ hs1,
    slope_def_field, sinePhase_one, sub_zero]
  unfold sinePhase
  field_simp [hp, hn, sub_ne_zero.mpr hs1, sub_ne_zero.mpr hs1.symm]
  have hinv := inv_mul_cancel₀ (sub_ne_zero.mpr hs1.symm)
  linear_combination (s * Complex.sin (s*(Real.pi:ℂ)) * (q:ℂ)) * hinv

theorem correctionToTwo_differentiable {q : ℝ} (hq : 0 ≤ q) {s : ℂ} (hs : s.re < 2) :
    DifferentiableAt ℂ (correctionToTwo q) s := by
  have hm : DifferentiableAt ℂ (mellin (subtractedKernel q)) (-(2*s)) := by
    apply mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
      (subtracted_local hq) (subtracted_top hq) (subtracted_zero hq)
    simp [two_mul]
    linarith
  have hd : Differentiable ℂ (dslope sinePhase 1) := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (univ_mem : Set.univ ∈ 𝓝 (1:ℂ))).mpr
      sinePhase_entire.differentiableOn
  unfold correctionToTwo
  have harg : DifferentiableAt ℂ (fun z : ℂ => -(2*z)) s := by fun_prop
  have hcomp := hm.comp s harg
  apply DifferentiableAt.sub
  · apply DifferentiableAt.mul
    · exact ((((differentiableAt_const (2:ℂ)).mul differentiableAt_id).mul
        (sinePhase_entire s)).div_const (Real.pi:ℂ))
    · exact hcomp
  · exact (((differentiableAt_const (q:ℂ)).mul differentiableAt_id).div_const
      (Real.pi:ℂ)).mul (hd s)

/-- For q = ε⁻² the continued correction takes precisely that value at one. -/
theorem correctionToTwo_one (q : ℝ) : correctionToTwo q 1 = (q:ℂ) := by
  rw [correctionToTwo, sinePhase_one, dslope_same, sinePhase_deriv]
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

end SuperZeta.Reference
