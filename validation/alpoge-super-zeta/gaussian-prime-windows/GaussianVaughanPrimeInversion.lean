import GaussianVaughanContourDecay
import MellinContourShift
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! Invert the continued transform at the actual completed-prime kernel.
The original Dirichlet sum is continuous on positive scales, so Mathlib's
inversion applies pointwise on the right before the shift to 3/8. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory QuarticModel Set
open scoped Topology

noncomputable section

theorem dirichletKernelSum_continuousAt_of_power
    {a : ArithmeticFunction ℂ} {H : ℝ → ℂ} {s D x : ℝ}
    (hs : 0 ≤ s) (hD : 0 ≤ D) (hx : 0 < x)
    (hH₀ : ContinuousOn H (Ioi 0))
    (hH : ∀ v > 0, ‖H v‖ ≤ D * v ^ (-s))
    (ha : LSeriesSummable a (s : ℂ)) :
    ContinuousAt (dirichletKernelSum a H) x := by
  let b := x / 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hbx : x ∈ Ioi b := by dsimp [b]; exact half_lt_self hx
  have hterm (n : ℕ) : ContinuousOn (fun v : ℝ => a n * H ((n : ℝ) * v)) (Ioi b) := by
    by_cases hn : n = 0
    · subst n
      simpa only [ArithmeticFunction.map_zero, zero_mul] using continuousOn_const
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    exact continuousOn_const.mul
      (hH₀.comp ((continuous_const.mul continuous_id).continuousOn)
        (fun v hv => mul_pos hn₀ (hb.trans hv)))
  have hbound (n : ℕ) (v : ℝ) (hv : v ∈ Ioi b) :
      ‖a n * H ((n : ℝ) * v)‖ ≤ (D * b ^ (-s)) * ‖LSeries.term a (s : ℂ) n‖ := by
    by_cases hn : n = 0
    · subst n
      simp
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hv₀ : 0 < v := hb.trans hv
    have hpow := Real.rpow_le_rpow_of_nonpos hb (le_of_lt hv) (neg_nonpos.mpr hs)
    have hL : ‖LSeries.term a (s : ℂ) n‖ = ‖a n‖ * (n : ℝ) ^ (-s) := by
      rw [LSeries.term_of_ne_zero hn, norm_div, ← Complex.ofReal_natCast,
        norm_cpow_eq_rpow_re_of_pos hn₀, ofReal_re, Real.rpow_neg hn₀.le, div_eq_mul_inv]
    calc
      _ ≤ ‖a n‖ * (D * ((n : ℝ) * v) ^ (-s)) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hH _ (mul_pos hn₀ hv₀)) (norm_nonneg _)
      _ = (D * v ^ (-s)) * ‖LSeries.term a (s : ℂ) n‖ := by
        rw [Real.mul_rpow hn₀.le hv₀.le, hL]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hD) (norm_nonneg _)
  exact (continuousOn_tsum hterm (ha.norm.mul_left _) hbound).continuousAt
    (isOpen_Ioi.mem_nhds hbx)

theorem archivedGaussianVaughanCompletedPrimeKernel_continuousAt {v : ℝ} (hv : 0 < v) :
    ContinuousAt archivedGaussianVaughanCompletedPrimeKernel v := by
  obtain ⟨D, hD, hK⟩ := archivedGaussianVaughanKernel_powerBound (a := 2) (by norm_num)
  have hL := ArithmeticFunction.LSeriesSummable_mul
    (archivedGaussianVaughanPrime_summable (z := ((2 : ℝ) : ℂ)) (by norm_num))
    (archivedGaussianFactor_hasSum (w := ((2 : ℝ) : ℂ)) (by norm_num)).LSeriesSummable
  change ContinuousAt (dirichletKernelSum
    (archivedGaussianVaughanPrimeCoefficients * signedIdealCoefficients)
    (fun x => (archivedGaussianVaughanKernel x : ℂ))) v
  apply dirichletKernelSum_continuousAt_of_power (s := 2) (by norm_num) hD hv
    (Complex.continuous_ofReal.comp_continuousOn archivedGaussianVaughanKernel_continuousOn) _ hL
  intro x hx
  simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hK x hx

private abbrev completedPrimeTransform :=
  archivedGaussianVaughanPrimeContinuation archivedGaussianVaughanHigherMellin

private theorem completedPrimeTransform_strip (hDir : DirichletLZerosOnLine) :
    (∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 3 / 2 →
      DifferentiableAt ℂ completedPrimeTransform z) ∧
    ∃ C ≥ 0, ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 3 / 2 →
      ‖completedPrimeTransform z‖ ≤ C / (1 + |z.im|) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := archivedGaussianVaughanCompletedPrime_rapid_decay hDir 2
  refine ⟨fun z h₁ _ => ((archivedGaussianVaughanCompletedPrime_continues hDir).1 z
    (by linarith)).differentiableAt, C, hC, fun z h₁ h₂ => ?_⟩
  apply (le_div_iff₀ (show 0 < (1 + |z.im|) ^ (2 : ℕ) by positivity)).mpr
  simpa only [mul_comm] using hb z h₁ (by linarith)

/-- Recover the archived completed-prime kernel from the inverse on the
left contour, at every positive input scale. -/
theorem archivedGaussianVaughanCompletedPrimeKernel_eq_leftMellinInv
    (hDir : DirichletLZerosOnLine) {v : ℝ} (hv : 0 < v) :
    archivedGaussianVaughanCompletedPrimeKernel v =
      mellinInv (3 / 8) completedPrimeTransform v := by
  let f := archivedGaussianVaughanCompletedPrimeKernel
  let b : ℝ := 3 / 2
  obtain ⟨hd, C, _, hbound⟩ := completedPrimeTransform_strip hDir
  have hRight : VerticalIntegrable completedPrimeTransform b :=
    verticalIntegrable_of_square_decay (a := 3 / 8) (b := 3 / 2)
      (by norm_num [b]) (by norm_num [b]) hd hbound
  have hB : MellinConvergent f (b : ℂ) :=
    ((archivedGaussianVaughanCompletedPrime_continues hDir).2 (b : ℂ) (by norm_num [b])).1
  have hRead (t : ℝ) : mellin f ((b : ℂ) + (t : ℂ) * I) =
      completedPrimeTransform ((b : ℂ) + (t : ℂ) * I) :=
    ((archivedGaussianVaughanCompletedPrime_continues hDir).2 _
      (by simp [b, mul_re]; norm_num)).2
  have hInvInt : VerticalIntegrable (mellin f) b :=
    hRight.congr (Eventually.of_forall fun t => (hRead t).symm)
  calc
    f v = mellinInv b (mellin f) v :=
      (mellinInv_mellin_eq b f hv hB hInvInt
        (archivedGaussianVaughanCompletedPrimeKernel_continuousAt hv)).symm
    _ = mellinInv b completedPrimeTransform v := by simp only [mellinInv, hRead]
    _ = _ := (mellinInv_eq_of_square_decay hv (by norm_num [b]) hd hbound).symm

theorem archivedGaussianVaughanCompletedPrimeKernel_left_powerBound
    (hDir : DirichletLZerosOnLine) :
    ∃ C ≥ 0, ∀ v > (0 : ℝ),
      ‖archivedGaussianVaughanCompletedPrimeKernel v‖ ≤ C * v ^ (-(3 / 8 : ℝ)) := by
  obtain ⟨hd, D, hD, hbound⟩ := completedPrimeTransform_strip hDir
  have hL : VerticalIntegrable completedPrimeTransform (3 / 8) :=
    verticalIntegrable_of_square_decay (a := 3 / 8) (b := 3 / 2)
      le_rfl (by norm_num) hd hbound
  let C := (1 / (2 * Real.pi)) *
    ∫ y : ℝ, ‖completedPrimeTransform (((3 / 8 : ℝ) : ℂ) + (y : ℂ) * I)‖
  have hC : 0 ≤ C := mul_nonneg (by positivity [Real.pi_pos]) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨C, hC, fun v hv => ?_⟩
  rw [archivedGaussianVaughanCompletedPrimeKernel_eq_leftMellinInv hDir hv]
  exact norm_mellinInv_le hv hL

#check archivedGaussianVaughanCompletedPrimeKernel_left_powerBound
#print axioms dirichletKernelSum_continuousAt_of_power
#print axioms archivedGaussianVaughanCompletedPrimeKernel_continuousAt
#print axioms archivedGaussianVaughanCompletedPrimeKernel_eq_leftMellinInv
#print axioms archivedGaussianVaughanCompletedPrimeKernel_left_powerBound

end
end AlpogeSuperZeta
