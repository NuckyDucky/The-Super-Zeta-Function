import SpectralMellin
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LogDerivLocal

namespace AlpogeSuperZeta

open Complex SuperZeta Filter
open scoped Topology

noncomputable section

/-- Compare the normalized ordinary slope with the slope of a character
read at the same doubled input. The factor 1/2 converts the derivatives
from spectral scale back to Riemann scale. -/
def signedSlope {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  (logDeriv corrected s - logDeriv Spectrum.riemannFactor s -
    logDeriv (fun z : ℂ => χ.LFunction (2 * z)) s) / 2

/-- The principal part of the difference keeps only the difference of
vanishing orders. Both orders are recorded at the original Riemann input. -/
theorem signed_slope_local {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs₀ : 0 < s.re) (hs₁ : s.re < 1 / 2)
    (hζ : analyticOrderAt riemannZeta (2 * s) ≠ ⊤)
    (hχ : analyticOrderAt χ.LFunction (2 * s) ≠ ⊤) :
    ∃ m n : ℕ, (m : ℕ∞) = analyticOrderAt riemannZeta (2 * s) ∧
      (n : ℕ∞) = analyticOrderAt χ.LFunction (2 * s) ∧
      ∃ H : ℂ → ℂ, AnalyticAt ℂ H s ∧
        ∀ᶠ z in 𝓝[≠] s,
          signedSlope χ z = ((m : ℂ) - (n : ℂ)) / (2 * (z - s)) + H z := by
  have hp := Multiplicity.doubled_ne_pole hs₁
  have hJ := (Reference.entireCorrection_differentiable
    (q := 1) (by norm_num)).analyticAt s
  have hD : AnalyticAt ℂ corrected s := (UnitSpectrum.continuation_analytic hp).sub hJ
  have hDo : analyticOrderAt corrected s = analyticOrderAt riemannZeta (2 * s) :=
    UnitSpectrum.difference_order hs₀ hs₁
  have hψd : DifferentiableOn ℂ χ.LFunction ({1}ᶜ : Set ℂ) := fun z hz =>
    (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have hψ : AnalyticAt ℂ χ.LFunction (2 * s) :=
    hψd.analyticAt (isOpen_compl_singleton.mem_nhds hp)
  have hψs := hψ.comp (Multiplicity.scale_analytic 2 s)
  have hψo := Multiplicity.scale_order (by norm_num : (2 : ℂ) ≠ 0) hψ
  obtain ⟨m, _, hm, A, hA, heA⟩ := Deduction.logDeriv_local hD
    (fun h => hζ (hDo.symm.trans (analyticOrderAt_eq_top.mpr h)))
  obtain ⟨n, _, hn, B, hB, heB⟩ := Deduction.logDeriv_local hψs
    (fun h => hχ (hψo.symm.trans (analyticOrderAt_eq_top.mpr h)))
  have hF := Multiplicity.analytic_factor s
  have hL : AnalyticAt ℂ (logDeriv Spectrum.riemannFactor) s :=
    hF.deriv.div hF (Spectrum.riemannFactor_ne_zero hs₀)
  refine ⟨m, n, hm.trans hDo, hn.trans hψo,
    fun z => (A z - logDeriv Spectrum.riemannFactor z - B z) / 2,
    ((hA.sub hL).sub hB).div analyticAt_const (by norm_num), ?_⟩
  filter_upwards [heA, heB] with z hz hq
  change deriv (fun t : ℂ => χ.LFunction (2 * t)) z / χ.LFunction (2 * z) = _ at hq
  dsimp only [signedSlope]
  rw [logDeriv_apply corrected, hz, logDeriv_apply (fun z : ℂ => χ.LFunction (2 * z)), hq]
  rw [div_mul_eq_div_div]
  ring

#print axioms Deduction.logDeriv_local
#print axioms signed_slope_local

end
end AlpogeSuperZeta
