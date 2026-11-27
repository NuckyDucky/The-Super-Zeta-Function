import DottieContourPhase
import DedekindMixedThetaCompletedRings

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection

private theorem dottie_boundary_nonneg_of_zero {F W : ℂ → ℂ} {ρ : ℂ} {T : ℝ} {n : ℕ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hW : DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hzero : F ρ = 0) (hρ : ρ ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    ∃ z ∈ sphere (dottieScaledRightCenter T n) (dottieScaledRadius n), 0 ≤ (W z * F z).im := by
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
  have hstrip : sphere c r ⊆ Complex.re ⁻¹' Ioo (0 : ℝ) 1 := by
    intro z hz
    have h := dottieScaledRightDisk_strip (sphere_subset_closedBall hz)
    exact ⟨(by norm_num : (0 : ℝ) < 1 / 2).trans h.1, h.2⟩
  have hcont : ContinuousOn (fun z => (W z * F z).im) (sphere c r) :=
    Complex.continuous_im.comp_continuousOn ((hW.mul hF).continuousOn.mono hstrip)
  obtain ⟨z, hz, hmax⟩ := (isCompact_sphere c r).exists_isMaxOn
    (NormedSpace.sphere_nonempty.mpr hr.le) hcont
  refine ⟨z, hz, ?_⟩
  by_contra! hneg
  have hboundary : ∀ u ∈ sphere c r, (W u * F u).im ≤ -(-(W z * F z).im) := by
    intro u hu
    rw [neg_neg]
    exact hmax hu
  exact dottie_disk_nonzero_of_holomorphic_weight hF hW (neg_pos.mpr hneg) hboundary hρ hzero

/-- A candidate zero determines a reference height and a covering scale.
Every holomorphic weight then has a nonnegative imaginary reading somewhere
on that disk's circumference. -/
theorem dottie_candidate_zero_boundary {F : ℂ → ℂ} {ρ : ℂ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hlo : 1 / 2 < ρ.re) (hhi : ρ.re ≤ 127 / 128) (hzero : F ρ = 0) :
    ∃ n : ℕ, ρ ∈ closedBall (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n) ∧
      ∀ W : ℂ → ℂ, DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1) →
        ∃ z ∈ sphere (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n),
          0 ≤ (W z * F z).im := by
  obtain ⟨n, hn⟩ := dottieScaledRightDisk_covers hlo hhi
  exact ⟨n, hn, fun _ hW => dottie_boundary_nonneg_of_zero hF hW hzero hn⟩

theorem riemannZeta_candidate_dottie_boundary {ρ : ℂ}
    (hlo : 1 / 2 < ρ.re) (hhi : ρ.re ≤ 127 / 128) (hzero : riemannZeta ρ = 0) :
    ∃ n : ℕ, ρ ∈ closedBall (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n) ∧
      ∀ W : ℂ → ℂ, DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1) →
        ∃ z ∈ sphere (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n),
          0 ≤ (W z * riemannZeta z).im := by
  apply dottie_candidate_zero_boundary _ hlo hhi hzero
  intro z hz
  have htop : z.re < 1 := hz.2
  have hne : z ≠ 1 := by rintro rfl; norm_num at htop
  exact (differentiableAt_riemannZeta hne).differentiableWithinAt

theorem dedekind_candidate_dottie_boundary (K : Type*) [Field K] [NumberField K] {ρ : ℂ}
    (hlo : 1 / 2 < ρ.re) (hhi : ρ.re ≤ 127 / 128) (hzero : mixedThetaContinuation K ρ = 0) :
    ∃ n : ℕ, ρ ∈ closedBall (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n) ∧
      ∀ W : ℂ → ℂ, DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1) →
        ∃ z ∈ sphere (dottieScaledRightCenter (ρ.im + 1 / 512) n) (dottieScaledRadius n),
          0 ≤ (W z * mixedThetaCompletedReading K z).im := by
  have hR : 0 < ρ.re := (by norm_num : (0 : ℝ) < 1 / 2).trans hlo
  have hT : ρ.re < 1 := hhi.trans_lt (by norm_num)
  have hFzero := (mixedThetaCompletedReading_zero_iff K ρ hR hT).mpr hzero
  exact dottie_candidate_zero_boundary (mixedThetaCompletedReading_differentiableOn K) hlo hhi hFzero

#print axioms dottie_candidate_zero_boundary
#check @riemannZeta_candidate_dottie_boundary
#print axioms riemannZeta_candidate_dottie_boundary
#check @dedekind_candidate_dottie_boundary
#print axioms dedekind_candidate_dottie_boundary

end FieldTarget
