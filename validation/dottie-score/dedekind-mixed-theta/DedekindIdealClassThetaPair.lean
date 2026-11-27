import DedekindZetaZeroFree.LFunctions.Dedekind.IdealClassThetaMellin
import DedekindZetaZeroFree.Theta.Profiles.MixedThetaFunctionalEquationPair

namespace FieldTarget

open scoped NumberField nonZeroDivisors
open NumberField Complex MeasureTheory
open DedekindZetaZeroFree.AbelianQuotient
open DedekindZetaZeroFree.AbelianQuotient.Theta

noncomputable section

/-- The class theta function paired with the theta function of its trace
dual. The same basis-independent Poisson identity applies class by class. -/
def idealClassThetaPair (K : Type) [Field K] [NumberField K]
    (C : ClassGroup (𝓞 K)) : WeakFEPair ℂ where
  f := (alpha K : ℂ) • mixedAngularAverage K
    (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))
  g := (alpha K : ℂ) • mixedNegAngularAverage K
    (traceDualIdealUnit K (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)))
  k := 1
  ε := 1
  f₀ := (alpha K : ℂ)
  g₀ := (alpha K : ℂ)
  hk := by norm_num
  hε := by norm_num
  hf_int := (locallyIntegrableOn_mixedAngularAverage K _).smul _
  hg_int := (locallyIntegrableOn_mixedNegAngularAverage K _).smul _
  h_feq := by
    intro t ht
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mixedAngularAverage_poisson K _ t ht, Real.rpow_one]
    simp only [one_mul]
    ring
  hf_top := by
    intro r
    simpa only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_one] using
      (mixedAngularAverage_isBigO_rpow K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) r).const_mul_left
          (alpha K : ℂ)
  hg_top := by
    intro r
    simpa only [Pi.smul_apply, smul_eq_mul, mul_sub, mul_one] using
      (mixedNegAngularAverage_isBigO_rpow K (traceDualIdealUnit K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C))) r).const_mul_left
          (alpha K : ℂ)

/-- In the domain of convergence, the continued class Mellin reading is
the completed partial Dedekind zeta value at the same input. -/
theorem idealClassThetaPair_eq_completedPartial
    (K : Type) [Field K] [NumberField K] (C : ClassGroup (𝓞 K))
    {w : ℂ} (hw : 1 < w.re) :
    (idealClassThetaPair K C).Λ w = zetaGammaFactor K w * partialDedekindZeta K C w := by
  have h := (idealClassThetaPair K C).hasMellin (show (idealClassThetaPair K C).k < w.re from hw)
  have heq : ((idealClassThetaPair K C).f · - (idealClassThetaPair K C).f₀) =
      (fun t ↦ (alpha K : ℂ) * (mixedAngularAverage K
        (FractionalIdeal.mk0 K (inverseClassIdealRepresentative K C)) t - 1)) := by
    funext t
    simp [idealClassThetaPair, Pi.smul_apply, mul_sub]
  rw [heq] at h
  exact h.2.symm.trans (hasMellin_classTheta K C hw).2

#check @idealClassThetaPair_eq_completedPartial
#print axioms idealClassThetaPair
#print axioms idealClassThetaPair_eq_completedPartial

end
end FieldTarget
