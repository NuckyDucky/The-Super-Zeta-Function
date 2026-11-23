import DottieOmittedSharpVariation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Derivatives of the finite sharp block and of its one-sided completion. -/

namespace QuarticModel

open Complex Finset
open private signedTerm from DottieSignedMoments
open private dottie_block_log_width_succ_monotone dottie_block_log_width_one_nonneg
  dottie_signed_term_anchor from DottieOmittedSharpVariation

/-- The signed Dirichlet block weighted by the displacement from `log h`. -/
noncomputable def dottieCenteredLogBlock (h len : ℕ) (w : ℂ) : ℂ :=
  ∑ n ∈ Ioc h (h + len),
    ((Real.log (n : ℝ) : ℂ) - (Real.log (h : ℝ) : ℂ)) *
      ((archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w))

theorem dottie_norm_block_hasDerivAt (h len : ℕ) (w : ℂ) :
    HasDerivAt (dottieNormBlock h len)
      (-(∑ n ∈ Ioc h (h + len),
        (Real.log (n : ℝ) : ℂ) * ((archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w)))) w := by
  have block_eq : dottieNormBlock h len = fun z =>
      ∑ n ∈ Ioc h (h + len), (archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-z) :=
    funext (dottie_norm_block_eq_Ioc h len)
  rw [block_eq, ← Finset.sum_neg_distrib]
  refine HasDerivAt.fun_sum fun n hn => ?_
  have hnpos : 0 < n := (Nat.zero_le h).trans_lt (Finset.mem_Ioc.mp hn).1
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have term := (((hasDerivAt_id' w).neg.const_cpow (c := (n : ℂ))
    (Or.inl hnne)).const_mul (archivedLatticeCoeff n : ℂ))
  have term_deriv_eq :
      (archivedLatticeCoeff n : ℂ) * ((n : ℂ)^(-w) * Complex.log (n : ℂ) * (-1)) =
        -((Real.log (n : ℝ) : ℂ) * ((archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w))) := by
    rw [Complex.natCast_log]
    ring
  rw [← term_deriv_eq]
  exact term

private theorem dottie_sharp_factor_hasDerivAt {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt dottieSharpFactor
      (dottieSharpFactor w * ((Real.log archivedThetaScale : ℂ) + digamma w)) w := by
  have gamma_deriv_eq : Gamma w * digamma w = deriv Gamma w := by
    rw [digamma_def, logDeriv_apply, mul_comm, div_mul_cancel₀ _ (Gamma_ne_zero_of_re_pos hw)]
  have gamma_deriv : HasDerivAt Gamma (Gamma w * digamma w) w := by
    rw [gamma_deriv_eq]
    apply (differentiableAt_Gamma w ?_).hasDerivAt
    intro n hn
    have hnre := congrArg Complex.re hn
    rw [Complex.neg_re, Complex.natCast_re] at hnre
    have hn₀ : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hscale : (archivedThetaScale : ℂ) ≠ 0 := ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have power_deriv := (hasDerivAt_id' w).const_cpow (c := (archivedThetaScale : ℂ)) (Or.inl hscale)
  have factor_deriv_eq :
      (((archivedThetaScale : ℂ)^w * Complex.log (archivedThetaScale : ℂ) * 1) * Gamma w +
        (archivedThetaScale : ℂ)^w * (Gamma w * digamma w)) / (archivedDottieCompletionScale : ℂ) =
        dottieSharpFactor w * ((Real.log archivedThetaScale : ℂ) + digamma w) := by
    rw [dottieSharpFactor, Complex.ofReal_log archivedThetaScale_pos.le]
    ring
  rw [← factor_deriv_eq]
  exact (power_deriv.mul gamma_deriv).div_const (archivedDottieCompletionScale : ℂ)

/-- The derivative of one completed side, with the logarithmic weight centered at `h`. -/
theorem dottie_completed_norm_block_hasDerivAt (h len : ℕ) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt (fun z => dottieSharpFactor z * dottieNormBlock h len z)
      (dottieSharpFactor w *
        (((Real.log archivedThetaScale : ℂ) + digamma w - (Real.log (h : ℝ) : ℂ)) *
          dottieNormBlock h len w - dottieCenteredLogBlock h len w)) w := by
  let logSum : ℂ := ∑ n ∈ Ioc h (h + len),
    (Real.log (n : ℝ) : ℂ) * ((archivedLatticeCoeff n : ℂ) * (n : ℂ)^(-w))
  have centered_eq : dottieCenteredLogBlock h len w =
      logSum - (Real.log (h : ℝ) : ℂ) * dottieNormBlock h len w := by
    rw [dottieCenteredLogBlock, dottie_norm_block_eq_Ioc, Finset.mul_sum]
    unfold logSum
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => sub_mul _ _ _
  have product_eq :
      dottieSharpFactor w * ((Real.log archivedThetaScale : ℂ) + digamma w) * dottieNormBlock h len w +
        dottieSharpFactor w * (-logSum) =
        dottieSharpFactor w *
          (((Real.log archivedThetaScale : ℂ) + digamma w - (Real.log (h : ℝ) : ℂ)) *
            dottieNormBlock h len w - dottieCenteredLogBlock h len w) := by
    rw [centered_eq]
    ring
  rw [← product_eq]
  have block_deriv : HasDerivAt (dottieNormBlock h len) (-logSum) w :=
    dottie_norm_block_hasDerivAt h len w
  exact (dottie_sharp_factor_hasDerivAt hw).mul block_deriv

private theorem centered_log_eq_range (h len : ℕ) (w : ℂ) :
    dottieCenteredLogBlock h len w =
      ∑ i ∈ range len, (dottieBlockLogWidth h (i+1) : ℂ) *
        signedTerm archivedLatticeCoeff w (h+i) := by
  have hset : Ioc h (h+len) = Ico (h+1) (h+len+1) := by
    ext n
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [dottieCenteredLogBlock, hset, Finset.sum_Ico_eq_sum_range,
    show h+len+1-(h+1) = len by omega]
  apply sum_congr rfl
  intro i _
  rw [show h+1+i = h+i+1 by omega, signedTerm, dottieBlockLogWidth,
    show h+(i+1) = h+i+1 by omega, Complex.ofReal_sub]

theorem dottie_centered_log_block_bound {h : ℕ} (hh : 0 < h) (last : ℕ) (s z : ℂ) (A : ℝ)
    (hprefix : ∀ k ≤ last+1, ‖dottieNormBlock h k s‖ ≤ A) :
    let L := dottieBlockLogWidth h (last+1)
    ‖dottieCenteredLogBlock h (last+1) (s+z)‖ ≤
      ‖(h : ℂ)^(-z)‖ * (A*L*(2+‖z‖*L)*Real.exp (‖z‖*L)) := by
  let c := fun i => signedTerm archivedLatticeCoeff s (h+i)
  let u := fun i => dottieBlockLogWidth h (i+1)
  let L := dottieBlockLogWidth h (last+1)
  have heq : dottieCenteredLogBlock h (last+1) (s+z) =
      (h : ℂ)^(-z) * ∑ i ∈ range (last+1), ((u i : ℂ) * Complex.exp ((-z)*(u i : ℂ))) * c i := by
    rw [centered_log_eq_range, Finset.mul_sum]
    apply sum_congr rfl
    intro i _
    rw [dottie_signed_term_anchor hh s z i]
    change (u i : ℂ) * ((h : ℂ)^(-z) * (Complex.exp ((-z)*(u i : ℂ))*c i)) = _
    ring
  dsimp only
  rw [heq, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [norm_neg] using dottie_signed_block_log_weight c u last A L (-z)
    (dottie_block_log_width_succ_monotone h) (dottie_block_log_width_one_nonneg hh) le_rfl hprefix

/-- The anchored derivative retains the complex direction of the block sum
at the center. The remaining error is bounded by its signed partial sums. -/
theorem dottie_completed_derivative_anchor_error {h : ℕ} (hh : 0 < h)
    (last : ℕ) (s z : ℂ) (hw : 0 < (s+z).re) (A : ℝ)
    (hprefix : ∀ k ≤ last+1, ‖dottieNormBlock h k s‖ ≤ A) :
    let w := s+z
    let L := dottieBlockLogWidth h (last+1)
    let κ := (Real.log archivedThetaScale : ℂ) + digamma w - (Real.log (h : ℝ) : ℂ)
    ‖deriv (fun v => dottieSharpFactor v * dottieNormBlock h (last+1) v) w -
        dottieSharpFactor w * (κ * ((h : ℂ)^(-z) * dottieNormBlock h (last+1) s))‖ ≤
      ‖dottieSharpFactor w‖ * ‖(h : ℂ)^(-z)‖ *
        (‖κ‖*(2*A*‖z‖*L*Real.exp (‖z‖*L)) + A*L*(2+‖z‖*L)*Real.exp (‖z‖*L)) := by
  intro w L κ
  have hd := (dottie_completed_norm_block_hasDerivAt h (last+1) hw).deriv
  change deriv (fun v => dottieSharpFactor v * dottieNormBlock h (last+1) v) w = _ at hd
  rw [hd]
  change ‖dottieSharpFactor w * (κ * dottieNormBlock h (last+1) w -
      dottieCenteredLogBlock h (last+1) w) -
      dottieSharpFactor w * (κ * ((h : ℂ)^(-z) * dottieNormBlock h (last+1) s))‖ ≤ _
  rw [← mul_sub, show κ * dottieNormBlock h (last+1) w - dottieCenteredLogBlock h (last+1) w -
      κ * ((h : ℂ)^(-z) * dottieNormBlock h (last+1) s) =
      κ * (dottieNormBlock h (last+1) w - (h : ℂ)^(-z) * dottieNormBlock h (last+1) s) -
      dottieCenteredLogBlock h (last+1) w by ring, norm_mul]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, mul_add]
  exact add_le_add
    ((mul_le_mul_of_nonneg_left (dottie_norm_block_shift_error hh last s z A hprefix)
        (norm_nonneg κ)).trans_eq (by ring))
    (dottie_centered_log_block_bound hh last s z A hprefix)

#print axioms dottieCenteredLogBlock
#print axioms dottie_norm_block_hasDerivAt
#print axioms dottie_completed_norm_block_hasDerivAt
#print axioms dottie_centered_log_block_bound
#print axioms dottie_completed_derivative_anchor_error

end QuarticModel
