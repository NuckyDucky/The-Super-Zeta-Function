import DedekindCyclicZetaDescent
import DedekindMixedThetaRightEdge
import DedekindMixedThetaSampleCover

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Set SuperZeta.StirlingCorrection

/-- At each nonnegative height a band can use the field's own completed
Mellin samples to certify all points beyond its near-line clearance. -/
def HasDottieCompletedSampleHeightCover (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∃ l u : ℝ, t ∈ Icc l u ∧
    ∀ ε : ℝ, 0 < ε → ∀ w : ℂ, w.im ∈ Icc l u →
      1/2 + ε ≤ w.re → w.re ≤ 31/32 →
      ∃ a : DottieBandRing l u,
        w ∈ Metric.ball (dottieScaledRightCenter a.val.1 a.val.2) (dottieScaledRadius a.val.2) ∧
        HasDottieCompletedSamples L a.val.1 a.val.2

theorem dedekindZetaRH_of_completed_sample_height_cover (L : Type) [Field L] [NumberField L]
    (hs : HasDottieCompletedSampleHeightCover L) : DedekindZetaRH L := by
  apply dedekindZetaRH_of_completed_mixedTheta_signed_height_cover L
  intro t ht
  obtain ⟨l, u, hu, hlocal⟩ := hs t ht
  exact ⟨l, u, hu, hasFiniteDottieBoundaryCertificate_of_completed_samples L hlocal⟩

/-- Given the rational Dirichlet strip-zero result, only nonabelian rational
Galois fields need to supply the Dottie sample coverage. -/
theorem dedekindZetaRH_of_dirichlet_and_nonabelian_galois_sample_cover
    (hD : ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), StripZerosOnLine χ.LFunction)
    (hs : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
      ¬ IsAbelianGalois ℚ L → HasDottieCompletedSampleHeightCover L)
    (K : Type*) [Field K] [NumberField K] : DedekindZetaRH K := by
  refine dedekindZetaRH_of_all_galois_over_rat (fun L _ _ _ ↦ ?_) K
  by_cases hA : IsAbelianGalois ℚ L
  · let : IsAbelianGalois ℚ L := hA
    exact dedekindZetaRH_of_dirichlet_of_abelian hD L
  · exact dedekindZetaRH_of_completed_sample_height_cover L (hs L hA)

#print HasDottieCompletedSampleHeightCover
#print HasDottieCompletedSamples
#check @dedekindZetaRH_of_dirichlet_and_nonabelian_galois_sample_cover
#print axioms dedekindZetaRH_of_completed_sample_height_cover
#print axioms dedekindZetaRH_of_dirichlet_and_nonabelian_galois_sample_cover

end FieldTarget
