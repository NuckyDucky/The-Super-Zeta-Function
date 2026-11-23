import ArchivedDottieFiniteSums

/-! Keep the signed coefficients together inside the exact contour integral.
This exposes the cancellation required in each omitted range. -/

open Complex Finset MeasureTheory
open scoped BigOperators ComplexConjugate

namespace QuarticModel

open private dottieContour from ArchivedDottieTailPartition

/-- Finite Dirichlet polynomial in the exact conductor and norm units. -/
noncomputable def dottieRangePolynomial (S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ S, (archivedLatticeCoeff n : ℂ) * ((archivedThetaScale / (n : ℝ) : ℝ) : ℂ)^s

noncomputable def dottieRangeIntegrand (S : Finset ℕ) (w : ℂ) (u : ℝ) : ℂ :=
  let z := dottieContour u
  dottieRangePolynomial S (w+z) * Gamma (w+z) *
    Complex.exp (z^2-I*(Real.pi : ℂ)*z/2) / z

/-- Divide an entire signed range by the same completion scale as the
individual norm terms. -/
noncomputable def dottieRangeSide (S : Finset ℕ) (w : ℂ) : ℂ :=
  (∫ u : ℝ, dottieRangeIntegrand S w u) /
    (2 * (Real.pi : ℂ) * (archivedDottieCompletionScale : ℂ))

private theorem dottie_range_integrand_eq (S : Finset ℕ) (w : ℂ) (u : ℝ) :
    dottieRangeIntegrand S w u = ∑ n ∈ S, (archivedLatticeCoeff n : ℂ) * dottieContourIntegrand w n u := by
  simp only [dottieRangeIntegrand, dottieRangePolynomial, Finset.sum_mul, Finset.sum_div]
  exact sum_congr rfl (fun n _ => by unfold dottieContourIntegrand; ring)

theorem dottie_range_integrand_integrable (S : Finset ℕ) (hw : 0 < w.re+1)
    (hS : ∀ n ∈ S, n ≠ 0) : Integrable (dottieRangeIntegrand S w) := by
  have h := integrable_finsetSum S (fun n hn =>
    (dottieContourIntegrand_integrable hw (hS n hn)).const_mul (archivedLatticeCoeff n : ℂ))
  exact h.congr (Filter.Eventually.of_forall fun u => (dottie_range_integrand_eq S w u).symm)

theorem dottie_range_side_eq_sum (S : Finset ℕ) (hw : 0 < w.re+1)
    (hS : ∀ n ∈ S, n ≠ 0) : dottieRangeSide S w = ∑ n ∈ S, dottieSmoothSide w n := by
  simp_rw [dottieRangeSide, dottie_range_integrand_eq,
    integral_finsetSum S (fun n hn => (dottieContourIntegrand_integrable hw (hS n hn)).const_mul _),
    integral_const_mul, Finset.sum_div]
  apply sum_congr rfl
  intro n hn
  rw [dottieSmoothSide, if_neg (hS n hn), div_mul_eq_mul_div]

theorem dottie_omitted_eq_range_integrals {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    dottieOmitted w = dottieRangeSide dottieOmittedNorms w +
      conj (dottieRangeSide dottieOmittedNorms (1-conj w)) := by
  have hS : ∀ n ∈ dottieOmittedNorms, n ≠ 0 := by
    intro n hn he
    subst n
    simp [dottieOmittedNorms] at hn
  have hwr : 0 < (1-conj w).re+1 := by
    simp only [sub_re, one_re, conj_re]
    linarith
  rw [dottie_range_side_eq_sum dottieOmittedNorms (by linarith : 0 < w.re+1) hS,
    dottie_range_side_eq_sum dottieOmittedNorms hwr hS, map_sum,
    ← Finset.sum_add_distrib, dottie_omitted_eq_finite_sum]
  rfl

#print axioms dottie_range_integrand_integrable
#print axioms dottie_range_side_eq_sum
#print axioms dottie_omitted_eq_range_integrals

end QuarticModel
