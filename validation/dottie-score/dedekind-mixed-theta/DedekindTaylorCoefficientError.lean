import DedekindMixedThetaDerivative
import ContourTaylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! The Mellin derivative allowance gives coefficient enclosures in the
same Taylor normalization used by the disk certificates. -/

namespace FieldTarget

open Complex Metric
open DedekindZetaZeroFree.AbelianQuotient
open scoped NNReal

noncomputable section

theorem contourTaylorCoeff_eq_iteratedDeriv_div_factorial {F : ℂ → ℂ} {c : ℂ}
    {ρ : ℝ≥0} (hρ : 0 < ρ) (hF : DifferentiableOn ℂ F (closedBall c (ρ : ℝ)))
    (n : ℕ) :
    contourTaylorCoeff F c ρ n = iteratedDeriv n F c / (n.factorial : ℂ) := by
  have h := (hF.hasFPowerSeriesOnBall hρ).factorial_smul (1 : ℂ) n
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero n)).mpr
  simpa only [contourTaylorCoeff, nsmul_eq_mul, ← iteratedDeriv_eq_iteratedFDeriv, mul_comm] using h

/-- After dividing by the factorial, the radial tail contributes only the
inverse power of the outer radius to each Taylor coefficient. -/
theorem mixedTheta_folded_taylorCoeff_error_le (K : Type) [Field K] [NumberField K]
    {cut : ℝ} {ρ : ℝ≥0} {c : ℂ} (hcut : 1 ≤ cut) (hρ : 0 < ρ)
    (hlo : 0 ≤ c.re) (hhi : c.re ≤ 1) (n : ℕ) :
    ‖contourTaylorCoeff (Theta.mixedThetaPair K).Λ₀ c ρ n -
      contourTaylorCoeff (mixedThetaTruncation K cut) c ρ n‖ ≤
      mixedThetaWeightedTail K cut ρ / (ρ : ℝ) ^ n := by
  rw [contourTaylorCoeff_eq_iteratedDeriv_div_factorial hρ
    (Theta.mixedThetaPair K).differentiable_Λ₀.differentiableOn n,
    contourTaylorCoeff_eq_iteratedDeriv_div_factorial hρ
      (mixedThetaTruncation_differentiable K hcut).differentiableOn n,
    ← sub_div, norm_div, Complex.norm_natCast]
  have hR : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hFact : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  refine (div_le_div_of_nonneg_right
    (mixedTheta_mellin_iteratedDeriv_error_le K n hcut hR hlo hhi) hFact.le).trans_eq ?_
  field_simp [hFact.ne', hR.ne']

#print axioms contourTaylorCoeff_eq_iteratedDeriv_div_factorial
#print axioms mixedTheta_folded_taylorCoeff_error_le

end

end FieldTarget
