import SuperZeta.Reference
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Taylor subtraction of arbitrary order for the actual relative log determinant. -/
noncomputable section
namespace SuperZeta.Reference
open Asymptotics Filter
open scoped Topology

private def realKernel (q x : ℝ) : ℝ := Real.log (1+q*(x/Real.cosh x)^2)

private theorem realKernel_analytic (q : ℝ) : AnalyticAt ℝ (realKernel q) 0 := by
  have hcosh : AnalyticAt ℝ Real.cosh 0 := by
    have he : AnalyticAt ℝ Real.exp 0 := analyticAt_rexp
    have hn : AnalyticAt ℝ (fun x : ℝ => Real.exp (-x)) 0 :=
      (by simpa using he : AnalyticAt ℝ Real.exp (-(0:ℝ))).comp analyticAt_id.neg
    have hfun : Real.cosh = fun x : ℝ => (Real.exp x + Real.exp (-x)) * (2:ℝ)⁻¹ := by
      funext x
      rw [Real.cosh_eq, div_eq_mul_inv]
    rw [hfun]
    exact (he.add hn).mul (analyticAt_const (v:=(2:ℝ)⁻¹))
  have hy : AnalyticAt ℝ (fun x : ℝ => 1+q*(x/Real.cosh x)^2) 0 :=
    analyticAt_const.add (analyticAt_const.mul ((analyticAt_id.div hcosh (by simp)).pow 2))
  exact hy.log (by norm_num)

private def raw (q : ℝ) (n : ℕ) : ℝ := iteratedDeriv n (realKernel q) 0 / n.factorial
def taylorKernelCoeff (q : ℝ) (k : ℕ) : ℂ := ↑(raw q (2*(k+1)))

private theorem raw_odd (q : ℝ) (k : ℕ) : raw q (2*k+1) = 0 := by
  have he : (fun x : ℝ => realKernel q (-x)) = realKernel q := by
    funext x
    simp [realKernel, neg_div, neg_sq]
  have h := iteratedDeriv_comp_neg (2*k+1) (realKernel q) 0
  rw [he, neg_zero, pow_succ, pow_mul, neg_one_sq, one_pow] at h
  simp only [one_mul, neg_one_smul] at h
  unfold raw
  rw [show iteratedDeriv (2*k+1) (realKernel q) 0 = 0 by linarith]
  simp

private theorem even_partial (q x : ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range (2*(N+1)), raw q j*x^j =
      ∑ k ∈ Finset.range N, raw q (2*(k+1))*x^(2*(k+1)) := by
  induction N with
  | zero =>
    have hz : raw q 0 = 0 := by simp [raw, realKernel]
    have ho : raw q 1 = 0 := raw_odd q 0
    norm_num [Finset.sum_range_succ, hz, ho]
  | succ N ih =>
    rw [show 2*(N+1+1)=2*(N+1)+1+1 by omega, Finset.sum_range_succ,
      Finset.sum_range_succ (n:=2*(N+1)), ih, raw_odd, zero_mul, add_zero,
      Finset.sum_range_succ]

/-- The remainder after N even terms is O(x^(2N+2)). Its coefficients are
the even derivatives of the original reciprocal determinant's logarithm. -/
theorem logKernel_taylor_remainder (q : ℝ) (N : ℕ) :
    (fun x : ℝ => logKernel q x - ∑ k ∈ Finset.range N,
      taylorKernelCoeff q k * (x:ℂ)^(2*(k+1))) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-(-((2*(N+1):ℕ):ℝ)))) := by
  have h := (realKernel_analytic q).hasFPowerSeriesAt.isBigO_sub_partialSum_pow (2*(N+1))
  simp only [zero_add, FormalMultilinearSeries.partialSum, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul] at h
  change (fun x : ℝ => realKernel q x - ∑ j ∈ Finset.range (2*(N+1)), raw q j*x^j) =O[_] _ at h
  simp_rw [even_partial] at h
  obtain ⟨C, hC⟩ := isBigO_iff.mp h
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [hC.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with x hx xpos
  change 0 < x at xpos
  have hre : x ^ (-(-((2*(N+1):ℕ):ℝ))) = x ^ (2*(N+1)) := by
    rw [neg_neg, Real.rpow_natCast]
  change ‖((realKernel q x:ℝ):ℂ) - _‖ ≤ _
  simp only [taylorKernelCoeff, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_sum, ← Complex.ofReal_sub, Complex.norm_real, hre]
  simpa [Real.norm_eq_abs, abs_of_pos xpos] using hx

end SuperZeta.Reference
