import SuperZeta.Reference
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Values of the expression obtained from the reference sum and Mellin correction. -/
noncomputable section
namespace SuperZeta.Reference
open Complex MeasureTheory

theorem correction_neg_nat (q : ℝ) (n : ℕ) : correction q (-(n:ℂ)) = 0 := by
  simp [correction, mul_neg, mul_comm (Real.pi : ℂ) (n : ℂ), Complex.sin_nat_mul_pi]

/-- Zeros at the nonpositive integers for the reference-plus-correction expression. -/
theorem continued_neg_nat (q : ℝ) (n : ℕ) : continuedExpression q (-(n:ℂ)) = 0 := by
  rw [continuedExpression, correction_neg_nat, add_zero]
  cases n with
  | zero => simp [Spectrum.riemannFactor]
  | succ m =>
    rw [show (2:ℂ)*(-(↑(m+1):ℂ)) = -2*((m:ℂ)+1) by push_cast; ring,
      riemannZeta_neg_two_mul_nat_add_one, mul_zero]

/-- The relative correction has vanishing first derivative at zero. -/
theorem correction_derivative_zero {q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt (correction q) 0 0 := by
  have hm : DifferentiableAt ℂ (mellin (logKernel q)) (0:ℂ) := by
    apply mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
      (kernel_locally_integrable hq) (kernel_at_top hq) (kernel_at_zero hq)
    norm_num
  let g := fun s : ℂ => Complex.sin (↑Real.pi*s) / ↑Real.pi *
    (2*mellin (logKernel q) (-(2*s)))
  have hh : DifferentiableAt ℂ (fun s : ℂ => mellin (logKernel q) (-(2*s))) 0 := by
    apply DifferentiableAt.comp 0 (g := mellin (logKernel q)) (f := fun s : ℂ => -(2*s))
    · simpa using hm
    · fun_prop
  have hg : DifferentiableAt ℂ g 0 := by
    dsimp [g]
    fun_prop (disch := first | exact hh | exact_mod_cast Real.pi_ne_zero)
  have h := (hasDerivAt_id (0:ℂ)).mul hg.hasDerivAt
  have heq : correction q = fun s : ℂ => s*g s := by
    funext s
    rw [correction, sqrt_transform]
    dsimp [g]
    ring
  rw [heq]
  simpa [g] using h

/-- The derivative at zero, and hence the regularized determinant, are
independent of every real q≥0 in this expression. -/
theorem continued_derivative_zero {q : ℝ} (hq : 0 ≤ q) :
    HasDerivAt (continuedExpression q) (-(Real.log 4 : ℝ) : ℂ) 0 := by
  have hd : HasDerivAt (fun s : ℂ => 2*s) 2 0 := by simpa using (hasDerivAt_id (0:ℂ)).const_mul 2
  have htwo := (hd.const_cpow (c:=(2:ℂ)) (Or.inl (by norm_num))).sub_const 1
  have hpi := (hd.neg.const_cpow (c:=(Real.pi:ℂ)) (Or.inl (by exact_mod_cast Real.pi_ne_zero))).const_mul 2
  have hz := (differentiableAt_riemannZeta (s:=2*(0:ℂ)) (by norm_num)).hasDerivAt.comp_of_eq 0 hd (by rfl)
  have h := (((hpi.mul htwo).mul hz).add (correction_derivative_zero hq))
  have hl : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, Real.log_pow]; norm_num
  convert h using 1
  simp [hl, riemannZeta_zero, Function.comp_apply]
  rw [show (Complex.log 2) = ↑(Real.log 2) by norm_cast]
  ring

theorem regularized_determinant {q : ℝ} (hq : 0 ≤ q) :
    Complex.exp (-deriv (continuedExpression q) 0) = 4 := by
  rw [(continued_derivative_zero hq).deriv]
  rw [neg_neg, ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0:ℝ)<4)]
  norm_num

end SuperZeta.Reference
