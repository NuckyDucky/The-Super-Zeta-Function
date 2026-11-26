import ArchivedGaussianTriangleWindow

namespace GaussianTriangleScopeAudit

open AlpogeSuperZeta ArtinPrimitiveRootsConjecture FieldTarget

theorem sameLateWindowCondition :
    GaussianCutoffWindowBound archivedGaussianTriangleWindow ↔
      GaussianCutoffWindowBound archivedGaussianSquaredWindow :=
  archivedGaussianTriangleWindowBound_iff_prime_squared.trans
    archivedGaussianSquaredWindowBound_iff_prime_squared.symm

theorem actualQuarticContract
    (hD : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (w : ℂ),
      0 < w.re → w.re < 1 → DirichletCharacter.LFunction χ w = 0 → w.re = 1 / 2)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
        ∀ x ∈ Set.Icc Y (Y ^ (1 + δ)), archivedGaussianTriangleWindow x ≤ C * x ^ θ) :
    ∀ Z : ℂ → ℂ, IsDedekindZeta QuarticModel.K Z → ∀ w : ℂ,
      0 < w.re → w.re < 1 → Z w = 0 → w.re = 1 / 2 :=
  quartic_rh_of_archived_gaussian_triangle_windows hD hpos hcut

#check archivedMellin_eq_quartic_real_formula
#check cofactors_on_line
#check archivedGaussianSquaredWindow_mellin
#check quartic_rh_of_gaussian_cutoff_windows
#check archivedGaussianRawWindow_eq_prefix_sub
#check archivedGaussianPrimeHalfWindow_eq_prefix_sub
#check archivedGaussianTriangleWindow_error
#check frobeniusTriangleDivisibility_error
#check actualQuarticContract
#print axioms cofactors_on_line
#print axioms archivedMellin_eq_quartic_real_formula
#print axioms quartic_rh_of_gaussian_cutoff_windows
#print axioms quartic_rh_of_archived_gaussian_squared_windows
#print axioms quartic_rh_of_archived_gaussian_triangle_windows
#print axioms sameLateWindowCondition
#print axioms actualQuarticContract

end GaussianTriangleScopeAudit
