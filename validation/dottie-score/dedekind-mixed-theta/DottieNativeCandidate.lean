import DottieCandidateCircles
import DottieAlpogeDisk

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection

/-- The common corrected reading from the two marked thirds spectra,
evaluated at the ordinary input `w = 2*s`. -/
noncomputable def dottieNativeThirds (w : ℂ) : ℂ :=
  ((Real.pi : ℂ) ^ (-w) * ((3 : ℂ) ^ w - 1)) * riemannZeta w

private theorem dottieNativeThirds_differentiableOn :
    DifferentiableOn ℂ dottieNativeThirds (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
  have hπ : Differentiable ℂ (fun w : ℂ => (Real.pi : ℂ) ^ (-w)) :=
    differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h3 : Differentiable ℂ (fun w : ℂ => (3 : ℂ) ^ w - 1) :=
    (differentiable_id.const_cpow (Or.inl (by norm_num : (3 : ℂ) ≠ 0))).sub_const 1
  have hζ : DifferentiableOn ℂ riemannZeta (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
    intro z hz
    have htop : z.re < 1 := hz.2
    have hne : z ≠ 1 := by rintro rfl; norm_num at htop
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  exact (hπ.mul h3).differentiableOn.mul hζ

/-- `hCorrected` is the pointwise identity of the two original native words
from `NativeDottieContact`, at the doubled ordinary input. -/
theorem dottie_native_words_le_on_alpoge_disk {σ t : ℝ} {n : ℕ} {w : ℂ}
    (Z J : Bool → ℂ → ℂ)
    (hCorrected : ∀ b : Bool, Z b (w / 2) - J b (w / 2) = dottieNativeThirds w)
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (ht : 3 ≤ |t|)
    (hfit : σ - 1 ≤ dottieRingScale n / 2048)
    (hw : w ∈ closedBall (dottieScaledRightCenter (t + 1 / 512) n) (dottieScaledRadius n)) :
    ∀ b : Bool, ‖Z b (w / 2) - J b (w / 2)‖ ≤ 24 * (|t| + 2) := by
  intro b
  rw [hCorrected b]
  exact native_thirds_reading_le_on_dottie_disk_of_alpoge hσ hσ₂ ht hfit hw

/-- A candidate zero forces a nonnegative boundary reading at the same
point for both corrected words, for every holomorphic weight. -/
theorem dottie_native_words_candidate_boundary {ρ : ℂ}
    (Z J : Bool → ℂ → ℂ)
    (hCorrected : ∀ (b : Bool) (w : ℂ), 0 < w.re → w.re < 1 →
      Z b (w / 2) - J b (w / 2) = dottieNativeThirds w)
    (hlo : 1 / 2 < ρ.re) (hhi : ρ.re ≤ 127 / 128) (hzero : riemannZeta ρ = 0) :
    ∃ n : ℕ, ρ ∈ closedBall (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n) ∧
      ∀ W : ℂ → ℂ, DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1) →
        ∃ z ∈ sphere (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n),
          ∀ b : Bool, 0 ≤ (W z * (Z b (z / 2) - J b (z / 2))).im := by
  have hRzero : dottieNativeThirds ρ = 0 := by simp [dottieNativeThirds, hzero]
  obtain ⟨n, hn, hboundary⟩ :=
    dottie_candidate_zero_boundary dottieNativeThirds_differentiableOn hlo hhi hRzero
  refine ⟨n, hn, fun W hW => ?_⟩
  obtain ⟨z, hz, hpos⟩ := hboundary W hW
  have hzStrip := dottieScaledRightDisk_strip (sphere_subset_closedBall hz)
  refine ⟨z, hz, fun b => ?_⟩
  rwa [hCorrected b z ((by norm_num : (0 : ℝ) < 1 / 2).trans hzStrip.1) hzStrip.2]

#print axioms dottie_native_words_le_on_alpoge_disk
#check @dottie_native_words_candidate_boundary
#print axioms dottie_native_words_candidate_boundary

end FieldTarget
