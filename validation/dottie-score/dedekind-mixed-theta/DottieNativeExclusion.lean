import DottieNativeCandidate

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection

/-- If every covering scale comes with a strictly signed corrected word,
the original input is nonzero. The hypothetical zero is discharged here. -/
theorem dottie_native_words_ne_zero_of_signed_boundary {ρ : ℂ}
    (Z J : Bool → ℂ → ℂ)
    (hCorrected : ∀ (b : Bool) (w : ℂ), 0 < w.re → w.re < 1 →
      Z b (w / 2) - J b (w / 2) = dottieNativeThirds w)
    (hlo : 1 / 2 < ρ.re) (hhi : ρ.re ≤ 127 / 128)
    (hSigned : ∀ n : ℕ,
      ρ ∈ closedBall (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n) →
        ∃ (W : ℂ → ℂ) (b : Bool), DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1) ∧
          ∀ z ∈ sphere (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n),
            (W z * (Z b (z / 2) - J b (z / 2))).im < 0) :
    riemannZeta ρ ≠ 0 := by
  intro hzero
  obtain ⟨n, hρ, hboundary⟩ := dottie_native_words_candidate_boundary Z J hCorrected hlo hhi hzero
  obtain ⟨W, b, hW, hnegative⟩ := hSigned n hρ
  obtain ⟨z, hz, hnonnegative⟩ := hboundary W hW
  exact (not_lt_of_ge (hnonnegative b)) (hnegative z hz)

#check @dottie_native_words_ne_zero_of_signed_boundary
#print axioms dottie_native_words_ne_zero_of_signed_boundary

end FieldTarget
