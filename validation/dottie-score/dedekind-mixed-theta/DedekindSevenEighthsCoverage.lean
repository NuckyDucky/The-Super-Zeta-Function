import HeckeSevenEighthsTransfer
import DedekindGaloisDottieTarget

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set SuperZeta.StirlingCorrection
open scoped ComplexConjugate

theorem dedekindZetaRH_iff_seven_eighths_nonnegative_band
    (K : Type) [Field K] [NumberField K] :
    DedekindZetaRH K ↔ ∀ w : ℂ,
      1 / 2 < w.re → w.re ≤ 7 / 8 → 0 ≤ w.im → mixedThetaContinuation K w ≠ 0 := by
  rw [dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind K)]
  constructor
  · intro h w hlo hhi _ hz
    exact (ne_of_gt hlo) (h w (by linarith only [hlo]) (by linarith only [hhi]) hz)
  · intro h
    have hRight (z : ℂ) (hlo : 1 / 2 < z.re) (hhi : z.re < 1) :
        mixedThetaContinuation K z ≠ 0 := by
      by_cases hEdge : (7 / 8 : ℝ) < z.re
      · exact mixedThetaContinuation_ne_zero_above_seven_eighths K hEdge hhi
      · have hBand := le_of_not_gt hEdge
        by_cases hIm : 0 ≤ z.im
        · exact h z hlo hBand hIm
        · intro hz
          have hOne : z ≠ 1 := by
            rintro rfl
            exact lt_irrefl 1 hhi
          have hConj : mixedThetaContinuation K (conj z) = 0 := by
            rw [continuation_conj_argument (mixedThetaContinuation_isDedekind K) hOne,
              hz, map_zero]
          exact h (conj z) (by simpa only [conj_re] using hlo)
            (by simpa only [conj_re] using hBand)
            (by simpa only [conj_im, neg_nonneg] using le_of_not_ge hIm) hConj
    intro w hlo hhi hz
    rcases lt_trichotomy w.re (1 / 2 : ℝ) with hLeft | hLine | hRightOfLine
    · have hRe : (1 - conj w).re = 1 - w.re := by
        simp only [sub_re, one_re, conj_re]
      have h := hRight (1 - conj w) (by rw [hRe]; linarith only [hLeft])
        (by rw [hRe]; linarith only [hlo])
      exact (h (mixedThetaContinuation_reflects K w hlo hhi hz)).elim
    · exact hLine
    · exact (hRight w hRightOfLine hhi hz).elim

/-- The existing rational samples and error allowances on the part of each
bounded height band between the near-line clearance and `7/8`. -/
def HasDottieCompletedSamplesToSevenEighths (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∃ l u : ℝ, t ∈ Icc l u ∧
    ∀ ε : ℝ, 0 < ε → ∀ w : ℂ, w.im ∈ Icc l u →
      1 / 2 + ε ≤ w.re → w.re ≤ 7 / 8 →
      ∃ a : DottieBandRing l u,
        w ∈ Metric.ball (dottieScaledRightCenter a.val.1 a.val.2) (dottieScaledRadius a.val.2) ∧
        HasDottieCompletedSamples K a.val.1 a.val.2

theorem dedekindZetaRH_of_completed_samples_to_seven_eighths
    (K : Type) [Field K] [NumberField K] (hCover : HasDottieCompletedSamplesToSevenEighths K) :
    DedekindZetaRH K := by
  apply (dedekindZetaRH_iff_seven_eighths_nonnegative_band K).mpr
  intro w hlo hhi hIm
  obtain ⟨l, u, hHeight, hLocal⟩ := hCover w.im hIm
  obtain ⟨ε, hε, hClear⟩ := exists_dedekind_band_clearance
    (mixedThetaContinuation_isDedekind K) l u
  by_cases hNear : w.re - 1 / 2 < ε
  · exact hClear w hHeight hlo (by linarith only [hhi]) hNear
  · obtain ⟨a, hw, R, hR, m, hm, axis, hAxis, margin, hMargin, tail, hTail, hSamples⟩ :=
      hLocal ε hε w hHeight (by linarith only [le_of_not_gt hNear]) hhi
    have hBoundary := dottie_completed_boundary_of_rational_samples K R hR hm axis hAxis
      hTail hSamples
    have hNoZero := dottie_disk_nonzero_of_signed_boundary
      (mixedThetaCompletedReading_differentiableOn K) hMargin hBoundary
      (Metric.ball_subset_closedBall hw)
    exact fun hz ↦ hNoZero ((mixedThetaCompletedReading_zero_iff K w
      (by linarith only [hlo]) (by linarith only [hhi])).mpr hz)

theorem dedekindZetaRH_of_dirichlet_and_nonabelian_galois_samples_to_seven_eighths
    (hD : ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), StripZerosOnLine χ.LFunction)
    (hCover : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
      ¬ IsAbelianGalois ℚ L → HasDottieCompletedSamplesToSevenEighths L)
    (K : Type*) [Field K] [NumberField K] : DedekindZetaRH K := by
  refine dedekindZetaRH_of_all_galois_over_rat (fun L _ _ _ ↦ ?_) K
  by_cases hA : IsAbelianGalois ℚ L
  · let : IsAbelianGalois ℚ L := hA
    exact dedekindZetaRH_of_dirichlet_of_abelian hD L
  · exact dedekindZetaRH_of_completed_samples_to_seven_eighths L (hCover L hA)

#print HasDottieCompletedSamplesToSevenEighths
#check @dedekindZetaRH_iff_seven_eighths_nonnegative_band
#check @dedekindZetaRH_of_dirichlet_and_nonabelian_galois_samples_to_seven_eighths
#print axioms dedekindZetaRH_iff_seven_eighths_nonnegative_band
#print axioms dedekindZetaRH_of_completed_samples_to_seven_eighths
#print axioms dedekindZetaRH_of_dirichlet_and_nonabelian_galois_samples_to_seven_eighths

end FieldTarget
