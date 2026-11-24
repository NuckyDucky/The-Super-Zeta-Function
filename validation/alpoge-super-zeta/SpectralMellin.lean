import OrdinaryInteractions
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiModOne
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiOfNeOne

namespace AlpogeSuperZeta

open Complex MeasureTheory Set SuperZeta

noncomputable section

/-- Alpöge's modulus-one smoothed prime sum, expressed entirely through
the corrected spectrum and its known local factor in the spectral variable. -/
theorem spectral_mellin_mod_one {s : ℂ} (hs : 1 < (2 * s).re) :
    (∫ y in Ioi (1 : ℝ), Deduction.Gchi (1 : DirichletCharacter ℂ 1) y *
      (y : ℂ) ^ (-(2 * s) - 1)) =
    -((logDeriv corrected s - logDeriv Spectrum.riemannFactor s) / 2 +
      1 / (2 * s - 1) + 1 - (1 + Real.eulerMascheroniConstant) * (2 * s)) /
      ((2 * s) * (2 * s - 1)) := by
  have hs₀ : 0 < s.re := by simp [two_mul] at hs; linarith
  have hp : 2 * s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact (lt_irrefl _ hs)
  have hh := corrected_logDeriv hs₀ hp (riemannZeta_ne_zero_of_one_le_re hs.le)
  have hn : (logDeriv corrected s - logDeriv Spectrum.riemannFactor s) / 2 =
      deriv riemannZeta (2 * s) / riemannZeta (2 * s) := by
    rw [← logDeriv_apply]
    linear_combination hh / 2
  rw [hn]
  exact Deduction.mellin_Gchi_modOne 1 (2 * s) hs

/-- At the same input, each nontrivial Dirichlet character contributes its
own regularized logarithmic derivative. The two Mellin readings can be
compared at the spectral address before making a window assumption. -/
theorem spectral_mellin_difference {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < (2 * s).re) :
    (∫ y in Ioi (1 : ℝ), Deduction.Gchi (1 : DirichletCharacter ℂ 1) y *
      (y : ℂ) ^ (-(2 * s) - 1)) -
    (∫ y in Ioi (1 : ℝ), Deduction.Gchi χ y * (y : ℂ) ^ (-(2 * s) - 1)) =
    -((logDeriv corrected s - logDeriv Spectrum.riemannFactor s) / 2 -
      logDeriv χ.LFunction (2 * s) + 1 / (2 * s - 1) + 1 -
      (1 + Real.eulerMascheroniConstant - logDeriv χ.LFunction 1) * (2 * s)) /
      ((2 * s) * (2 * s - 1)) := by
  rw [spectral_mellin_mod_one hs, Deduction.mellin_Gchi_of_ne_one χ hχ (2 * s) hs]
  simp only [logDeriv_apply (f := χ.LFunction), ← sub_div]
  ring

#print axioms Deduction.mellin_Gchi_modOne
#print axioms Deduction.mellin_Gchi_of_ne_one
#print axioms spectral_mellin_mod_one
#print axioms spectral_mellin_difference

end
end AlpogeSuperZeta
