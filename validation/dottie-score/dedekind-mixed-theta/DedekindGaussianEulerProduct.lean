import DedekindEulerByRationalPrime
import DedekindGaussianLocalEuler
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace FieldTarget

set_option autoImplicit false

open Complex Ideal NumberField

/-- The Dedekind zeta of the actual Gaussian quadratic field is ordinary
zeta times Dirichlet beta on the convergence half-plane. -/
theorem gaussianQuadratic_dedekindZeta_eq_zeta_beta (w : ℂ) (hw : 1 < w.re) :
    NumberField.dedekindZeta GaussianQuadraticField w =
      riemannZeta w * gaussianQuadraticChar.LFunction w := by
  rw [dedekindZeta_eq_eulerProduct_rationalPrimes GaussianQuadraticField w hw]
  have hζ := riemannZeta_eulerProduct_hasProd hw
  have hβ := gaussianQuadraticChar.LSeries_eulerProduct_hasProd hw
  rw [← gaussianQuadraticChar.LFunction_eq_LSeries hw] at hβ
  refine (tprod_congr ?_).trans (hζ.mul hβ).tprod_eq
  intro p
  let _ : Fact p.val.Prime := ⟨p.property⟩
  rw [Finset.prod_inv_distrib, gaussianQuadratic_localEuler_denominator]
  simp only [mul_inv_rev, mul_comm]

/-- The Gaussian field's band certificate now takes the single bound on its
completion-weighted beta factor at one. -/
theorem gaussianQuadratic_dottie_band_of_weighted_beta_bound
    {L : ℝ} (hL : 0 ≤ L)
    (hslope : 2 * (gaussianQuadraticWeightedBeta 1 * completedRiemannZeta₀ 1 +
      deriv gaussianQuadraticWeightedBeta 1).re <
        ‖gaussianQuadraticWeightedBeta 1‖ / (1 + (L + 31/128)^2)) :
    HasFiniteDottieBoundaryCertificate (mixedThetaContinuation GaussianQuadraticField)
      (mixedThetaCompletedReading GaussianQuadraticField) (-L) L :=
  gaussianQuadratic_dottie_band_of_beta_slope gaussianQuadratic_dedekindZeta_eq_zeta_beta hL hslope

#check @gaussianQuadratic_dedekindZeta_eq_zeta_beta
#check @gaussianQuadratic_dottie_band_of_weighted_beta_bound
#print axioms gaussianQuadratic_dedekindZeta_eq_zeta_beta
#print axioms gaussianQuadratic_dottie_band_of_weighted_beta_bound

end FieldTarget
