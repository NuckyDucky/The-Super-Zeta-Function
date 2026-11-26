import GaussianVaughanMellinSeries

/-! Real-axis positivity lets the original Gaussian Mellin window detect
the same poles after reversing the sign of the sum. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory QuarticModel Set ArtinPrimitiveRootsConjecture

noncomputable section

theorem quartic_rh_of_archived_vaughan_negative_sum_windows
    (hDir : DirichletLZerosOnLine)
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound (fun X => -archivedGaussianVaughanSum X)) :
    DedekindZetaRH QuarticModel.K := by
  have hReal := gaussian_poles_nonreal_of_mellin_pos (fun σ _ =>
    archivedMellin_eq_quartic_real_formula ▸ hpos σ)
  refine quartic_rh_of_gaussian_mellin_windows hDir
    (A := fun X => -archivedGaussianVaughanSum X) archivedGaussianVaughanSum_measurable.neg
    ?_ (Φ := fun z => archivedGaussianVaughanEndpoint z - archivedGaussianVaughanMellin z)
    (fun z _ hz => (archivedGaussianVaughanEndpoint_entire.analyticAt z).sub
      (archivedGaussianVaughanMellin_analytic hz)) ?_ ?_ hcut
  · simpa only [abs_neg] using archivedGaussianVaughanSum_growth
  · intro ρ hρ hhalf
    obtain ⟨n, _, _, hc, b, hb, hnear⟩ := archivedGaussianVaughanMellin_pole hFree hhalf hρ.2
    refine ⟨_, neg_ne_zero.mpr hc, fun him => (hReal ρ hρ him).elim,
      fun z => archivedGaussianVaughanEndpoint z - b z,
      (archivedGaussianVaughanEndpoint_entire.analyticAt ρ).sub hb, ?_⟩
    filter_upwards [hnear] with z hz
    rw [hz, neg_div]
    ring
  · intro z hz
    simp only [ofReal_neg, neg_mul, integral_neg]
    rw [archivedGaussianVaughanSum_mellin_above_one (one_lt_two.trans hz)]
    ring

#check quartic_rh_of_archived_vaughan_negative_sum_windows
#print axioms quartic_rh_of_archived_vaughan_negative_sum_windows

end
end AlpogeSuperZeta
