import DedekindTwelfthRootTarget
import DedekindMixedThetaFiniteSamples

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Filter MeasureTheory Metric Set
open DedekindZetaZeroFree.AbelianQuotient SuperZeta.StirlingCorrection

/-- A strict signed boundary bound needs holomorphy only on the closed
measuring disk. -/
theorem dottie_disk_nonzero_of_local_signed_boundary {H : ℂ → ℂ} {T margin : ℝ} {n : ℕ}
    (hH : DifferentiableOn ℂ H (closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)))
    (hmargin : 0 < margin)
    (hboundary : ∀ z ∈ sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (H z).im ≤ -margin)
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    H w ≠ 0 := by
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
  let f := fun z : ℂ ↦ Complex.exp (-I * H z)
  have hreg : DifferentiableOn ℂ f (closure (ball c r)) := by
    rw [closure_ball c hr.ne']
    exact Complex.differentiable_exp.comp_differentiableOn ((differentiableOn_const (-I)).mul hH)
  have hnorm (z : ℂ) : ‖f z‖ = Real.exp (H z).im := by
    change ‖Complex.exp (-I * H z)‖ = _
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hedge : ∀ z ∈ frontier (ball c r), ‖f z‖ ≤ Real.exp (-margin) := by
    intro z hz
    rw [frontier_ball c hr.ne'] at hz
    rw [hnorm, Real.exp_le_exp]
    exact hboundary z hz
  have hclosed : w ∈ closure (ball c r) := by rwa [closure_ball c hr.ne']
  have hb := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
    hreg.diffContOnCl hedge hclosed
  rw [hnorm, Real.exp_le_exp] at hb
  intro hz
  rw [hz, zero_im] at hb
  linarith only [hb, hmargin]

/-- The mesh bound is for the entire weighted reading. The Mellin
tail at a sample is multiplied by the norm of the weight there. -/
theorem mixedTheta_weighted_boundary_of_rational_samples
    (K : Type) [Field K] [NumberField K] {W : ℂ → ℂ} {T R M margin tail : ℝ} {n m : ℕ}
    (hR : 1 ≤ R) (hm : 0 < m) (hM : 0 ≤ M)
    (hH : ∀ z ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n),
      DifferentiableAt ℂ (W * mixedThetaCompletedReading K) z)
    (hderiv : ∀ z ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n),
      ‖deriv (W * mixedThetaCompletedReading K) z‖ ≤ M)
    (hTail : 2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖
      ≤ tail)
    (hSamples : ∀ a ∈ contourQuarterTurns, ∀ j ≤ m,
      let v := rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) a m j
      (W v * mixedThetaCompletedTruncation K R v).im +
        M * (2 * dottieScaledRadius n / (m : ℝ)) + ‖W v‖ * tail ≤ -margin) :
    ∀ z ∈ sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (W z * mixedThetaCompletedReading K z).im ≤ -margin := by
  have hs : ∀ a ∈ contourQuarterTurns, ∀ j ≤ m,
      (1 * (W * mixedThetaCompletedReading K)
        (rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) a m j)).im +
        ‖(1 : ℂ)‖ * (M * (2 * dottieScaledRadius n / (m : ℝ))) ≤ -margin := by
    intro a ha j hj
    let v := rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) a m j
    have hr : 0 < dottieScaledRadius n := mul_pos (by norm_num) (dottieRingScale_pos n)
    have hv := dottieScaledRightDisk_strip (sphere_subset_closedBall
      (rationalContourSample_mem_sphere (c := dottieScaledRightCenter T n)
        (m := m) (j := j) hr ha))
    have hv₀ : 0 < v.re := (by norm_num : (0 : ℝ) < 1 / 2).trans hv.1
    have herr := (mixedThetaCompletedTruncation_error_le K R hR v hv₀ hv.2).trans hTail
    have hweighted : (W v * mixedThetaCompletedReading K v).im -
        (W v * mixedThetaCompletedTruncation K R v).im ≤ ‖W v‖ * tail := by
      rw [← sub_im, ← mul_sub]
      refine (le_abs_self _).trans ((abs_im_le_norm _).trans ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left herr (norm_nonneg _)
    have hsample := hSamples a ha j hj
    change (W v * mixedThetaCompletedTruncation K R v).im +
      M * (2 * dottieScaledRadius n / (m : ℝ)) + ‖W v‖ * tail ≤ -margin at hsample
    change (1 * (W v * mixedThetaCompletedReading K v)).im +
      ‖(1 : ℂ)‖ * (M * (2 * dottieScaledRadius n / (m : ℝ))) ≤ -margin
    simp only [one_mul, norm_one]
    linarith only [hweighted, hsample]
  intro z hz
  simpa only [Pi.mul_apply, one_mul] using
    dottie_signed_boundary_of_rational_samples hm hM hH hderiv hs z hz

/-- A weighted contour certificate records a finite sample bound, the
original Mellin tail, and a derivative allowance on the closed disk. -/
def IsDottieCompletedWeightedSampleCertificate (K : Type) [Field K] [NumberField K]
    (T : ℝ) (n : ℕ) (W : ℂ → ℂ) : Prop :=
  ∃ (R M margin tail : ℝ) (m : ℕ),
    1 ≤ R ∧ 0 < m ∧ 0 ≤ M ∧ 0 < margin ∧
    (∀ z ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n),
      DifferentiableAt ℂ (W * mixedThetaCompletedReading K) z) ∧
    (∀ z ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n),
      ‖deriv (W * mixedThetaCompletedReading K) z‖ ≤ M) ∧
    (2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ ≤ tail) ∧
    ∀ a ∈ contourQuarterTurns, ∀ j ≤ m,
      let v := rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) a m j
      (W v * mixedThetaCompletedTruncation K R v).im +
        M * (2 * dottieScaledRadius n / (m : ℝ)) + ‖W v‖ * tail ≤ -margin

def HasDottieCompletedWeightedSamples (K : Type) [Field K] [NumberField K]
    (T : ℝ) (n : ℕ) : Prop :=
  ∃ W : ℂ → ℂ, IsDottieCompletedWeightedSampleCertificate K T n W

theorem mixedTheta_ne_zero_of_dottie_weighted_samples
    (K : Type) [Field K] [NumberField K] {T : ℝ} {n : ℕ}
    (h : HasDottieCompletedWeightedSamples K T n)
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    mixedThetaContinuation K w ≠ 0 := by
  obtain ⟨W, R, M, margin, tail, m, hR, hm, hM, hmargin, hH, hderiv, hTail, hSamples⟩ := h
  have hD : DifferentiableOn ℂ (W * mixedThetaCompletedReading K)
      (closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :=
    fun z hz ↦ (hH z hz).differentiableWithinAt
  have hbound := mixedTheta_weighted_boundary_of_rational_samples K hR hm hM hH hderiv hTail hSamples
  have hne := dottie_disk_nonzero_of_local_signed_boundary hD hmargin
    (by simpa only [Pi.mul_apply] using hbound) hw
  intro hz
  have hstrip := dottieScaledRightDisk_strip hw
  have hReading := (mixedThetaCompletedReading_zero_iff K w
    ((by norm_num : (0 : ℝ) < 1 / 2).trans hstrip.1) hstrip.2).mpr hz
  exact hne (by simp only [Pi.mul_apply, hReading, mul_zero])

def HasDottieCompletedWeightedSamplesToSevenEighths (K : Type) [Field K] [NumberField K] : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∃ l u : ℝ, t ∈ Icc l u ∧
    ∀ ε : ℝ, 0 < ε → ∀ w : ℂ, w.im ∈ Icc l u →
      1 / 2 + ε ≤ w.re → w.re ≤ 7 / 8 →
      ∃ a : DottieBandRing l u,
        w ∈ ball (dottieScaledRightCenter a.val.1 a.val.2) (dottieScaledRadius a.val.2) ∧
        HasDottieCompletedWeightedSamples K a.val.1 a.val.2

theorem dedekindZetaRH_of_completed_weighted_samples_to_seven_eighths
    (K : Type) [Field K] [NumberField K]
    (hCover : HasDottieCompletedWeightedSamplesToSevenEighths K) : DedekindZetaRH K := by
  apply (dedekindZetaRH_iff_seven_eighths_nonnegative_band K).mpr
  intro w hlo hhi hIm
  obtain ⟨l, u, hHeight, hLocal⟩ := hCover w.im hIm
  obtain ⟨ε, hε, hClear⟩ := exists_dedekind_band_clearance
    (mixedThetaContinuation_isDedekind K) l u
  by_cases hNear : w.re - 1 / 2 < ε
  · exact hClear w hHeight hlo (by linarith only [hhi]) hNear
  · obtain ⟨_, hw, hData⟩ := hLocal ε hε w hHeight (by linarith only [le_of_not_gt hNear]) hhi
    exact mixedTheta_ne_zero_of_dottie_weighted_samples K hData (ball_subset_closedBall hw)

theorem dedekindZetaRH_of_dirichlet_and_twelfthRoot_galois_weighted_samples
    (hD : ∀ (m : ℕ) [NeZero m] (χ : DirichletCharacter ℂ m), StripZerosOnLine χ.LFunction)
    (hCover : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
      (∃ ζ : L, IsPrimitiveRoot ζ 12) → ¬ IsAbelianGalois ℚ L →
        HasDottieCompletedWeightedSamplesToSevenEighths L)
    (K : Type*) [Field K] [NumberField K] : DedekindZetaRH K := by
  refine dedekindZetaRH_of_galois_twelfthRoot_fields (fun L _ _ _ hζ ↦ ?_) K
  by_cases hA : IsAbelianGalois ℚ L
  · let : IsAbelianGalois ℚ L := hA
    exact dedekindZetaRH_of_dirichlet_of_abelian hD L
  · exact dedekindZetaRH_of_completed_weighted_samples_to_seven_eighths L (hCover L hζ hA)

#check @dedekindZetaRH_of_dirichlet_and_twelfthRoot_galois_weighted_samples
#print axioms dottie_disk_nonzero_of_local_signed_boundary
#print axioms mixedTheta_weighted_boundary_of_rational_samples
#print axioms mixedTheta_ne_zero_of_dottie_weighted_samples
#print axioms dedekindZetaRH_of_completed_weighted_samples_to_seven_eighths
#print axioms dedekindZetaRH_of_dirichlet_and_twelfthRoot_galois_weighted_samples

end FieldTarget
