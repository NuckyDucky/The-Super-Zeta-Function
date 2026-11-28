import DedekindWeightedDottieSamples
import DottieRationalWeight
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Filter MeasureTheory Metric Set
open DedekindZetaZeroFree.AbelianQuotient SuperZeta.StirlingCorrection

set_option maxHeartbeats 1000000 in
/-- The absence of zeros on the closed disk is enough for a certificate with a
finite rational weight, a finite Mellin cutoff, and finitely many samples. -/
theorem exists_dottieRationalWeightedSamples_of_nonzero
    (K : Type) [Field K] [NumberField K] (T : ℝ) (n : ℕ)
    (hzero : ∀ z ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n),
      mixedThetaContinuation K z ≠ 0) :
    ∃ (N : ℕ) (a : Fin N → ℚ × ℚ),
      IsDottieCompletedWeightedSampleCertificate K T n
        (dottieRationalWeight (dottieScaledRightCenter T n) a) := by
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  let F := mixedThetaCompletedReading K
  let S := Complex.re ⁻¹' Ioo (0 : ℝ) 1
  have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
  have hS : IsOpen S := continuous_re.isOpen_preimage _ isOpen_Ioo
  have hF : DifferentiableOn ℂ F S := mixedThetaCompletedReading_differentiableOn K
  have hStrip : closedBall c r ⊆ S := by
    intro z hz
    have h := dottieScaledRightDisk_strip hz
    exact ⟨(by norm_num : (0 : ℝ) < 1 / 2).trans h.1, h.2⟩
  have hFne (z : ℂ) (hz : z ∈ closedBall c r) : F z ≠ 0 := by
    have hs : 0 < z.re ∧ z.re < 1 := hStrip hz
    exact fun h ↦ hzero z hz ((mixedThetaCompletedReading_zero_iff K z hs.1 hs.2).mp h)
  let U := S ∩ F ⁻¹' ({0}ᶜ : Set ℂ)
  have hU : IsOpen U := hF.continuousOn.isOpen_inter_preimage hS isOpen_compl_singleton
  have hClosed : closedBall c r ⊆ U := by
    intro z hz
    refine ⟨hStrip hz, ?_⟩
    simpa only [mem_preimage, mem_compl_iff, mem_singleton_iff] using hFne z hz
  obtain ⟨η, hη, hOpen⟩ := (isCompact_closedBall c r).exists_thickening_subset_open hU hClosed
  rw [thickening_closedBall hη hr.le] at hOpen
  let R := r + η / 2
  have hrR : r < R := by dsimp [R]; linarith only [hη]
  have hOuter : closedBall c R ⊆ U :=
    (closedBall_subset_ball (by dsimp [R]; linarith only [hη])).trans hOpen
  have hOuterStrip : closedBall c R ⊆ S := hOuter.trans inter_subset_left
  have hInv : DifferentiableOn ℂ (fun z ↦ -I / F z) (closedBall c R) := by
    refine (differentiableOn_const (-I)).div (hF.mono hOuterStrip) ?_
    intro z hz
    simpa only [mem_preimage, mem_compl_iff, mem_singleton_iff] using (hOuter hz).2
  obtain ⟨BF, hBF⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
    (hF.mono hStrip).continuousOn
  let A := max 1 BF
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hε : 0 < 1 / (4 * A) := one_div_pos.mpr (mul_pos (by norm_num) hA)
  obtain ⟨N, a, hWeight⟩ := exists_dottieRationalWeight_approx hr.le hrR hε hInv
  let W := dottieRationalWeight c a
  have hW : Differentiable ℂ W := dottieRationalWeight_differentiable c a
  have hSign (z : ℂ) (hz : z ∈ closedBall c r) : (W z * F z).im ≤ -3 / 4 := by
    have hNorm : ‖W z * F z - (-I)‖ ≤ 1 / 4 := by
      have heq : W z * F z - (-I) = (W z - (-I / F z)) * F z := by
        rw [sub_mul, div_mul_cancel₀ _ (hFne z hz)]
      rw [heq, norm_mul]
      refine (mul_le_mul (hWeight z hz).le ((hBF z hz).trans (le_max_right (1 : ℝ) BF))
        (norm_nonneg _) hε.le).trans_eq ?_
      change (1 / (4 * A)) * A = 1 / 4
      field_simp [hA.ne']
    have hIm := (le_abs_self (W z * F z - (-I)).im).trans
      ((Complex.abs_im_le_norm _).trans hNorm)
    rw [sub_im, neg_im, I_im] at hIm
    linarith only [hIm]
  let H := W * F
  have hH : DifferentiableOn ℂ H S := hW.differentiableOn.mul hF
  have hHAt : ∀ z ∈ closedBall c r, DifferentiableAt ℂ H z :=
    fun z hz ↦ (hH z (hStrip hz)).differentiableAt (hS.mem_nhds (hStrip hz))
  obtain ⟨BH, hBH⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn
    (hH.mono hOuterStrip).continuousOn
  let M := max 0 BH / (R - r)
  have hd : 0 < R - r := sub_pos.mpr hrR
  have hM : 0 ≤ M := div_nonneg (le_max_left _ _) hd.le
  have hDeriv (z : ℂ) (hz : z ∈ closedBall c r) : ‖deriv H z‖ ≤ M := by
    have hLocal : closedBall z (R - r) ⊆ closedBall c R := by
      intro v hv
      apply mem_closedBall.mpr
      refine (dist_triangle v z c).trans ?_
      linarith only [mem_closedBall.mp hz, mem_closedBall.mp hv]
    have hReg := hH.mono (hLocal.trans hOuterStrip)
    rw [← closure_ball z hd.ne'] at hReg
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hd hReg.diffContOnCl
      (fun v hv ↦ (hBH v (hLocal (sphere_subset_closedBall hv))).trans (le_max_right _ _))
  obtain ⟨BW, hBW⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn
    hW.continuous.continuousOn
  let B := max 1 BW
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  let τ := (1 : ℝ) / (16 * B)
  have hτ : 0 < τ := one_div_pos.mpr (mul_pos (by norm_num) hB)
  let tail (s : ℝ) := 2 * ∫ t : ℝ in Ioi s,
    ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖
  have hlim : Tendsto tail atTop (nhds 0) := by
    have h := tendsto_integral_Ioi_zero
      (f := fun t : ℝ ↦ ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖)
      (μ := volume) (tendsto_id : Tendsto (fun t : ℝ ↦ t) atTop atTop)
    simpa only [tail, id_eq, mul_zero] using h.const_mul (2 : ℝ)
  obtain ⟨s, hs, hTail⟩ := ((eventually_ge_atTop (1 : ℝ)).and
    (hlim.eventually (gt_mem_nhds hτ))).exists
  obtain ⟨m, hm⟩ := exists_nat_gt (max 0 (M * (2 * r) / (1 / 8)))
  have hm' : (0 : ℝ) < m := (le_max_left _ _).trans_lt hm
  have hGrid : M * (2 * r / (m : ℝ)) ≤ 1 / 8 := by
    have hmul := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 1 / 8)).mp
      ((le_max_right _ _).trans_lt hm)
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hm').mpr (by simpa only [mul_comm (m : ℝ) (1 / 8 : ℝ)] using hmul.le)
  refine ⟨N, a, s, M, 1 / 2, τ, m, hs, by exact_mod_cast hm', hM, by norm_num,
    hHAt, hDeriv, hTail.le, ?_⟩
  intro q hq j _
  let v := rationalContourSample c r q m j
  have hv : v ∈ closedBall c r := sphere_subset_closedBall (rationalContourSample_mem_sphere hr hq)
  have hvS : 0 < v.re ∧ v.re < 1 := hStrip hv
  have herr := (mixedThetaCompletedTruncation_error_le K s hs v hvS.1 hvS.2).trans hTail.le
  have hErr : (W v * mixedThetaCompletedTruncation K s v).im - (W v * F v).im ≤ ‖W v‖ * τ := by
    rw [← sub_im, ← mul_sub]
    refine (le_abs_self _).trans ((abs_im_le_norm _).trans ?_)
    rw [norm_mul, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left herr (norm_nonneg _)
  have hTailAt : ‖W v‖ * τ ≤ 1 / 16 := by
    refine (mul_le_mul_of_nonneg_right
      ((hBW v hv).trans (le_max_right (1 : ℝ) BW)) hτ.le).trans_eq ?_
    change B * (1 / (16 * B)) = 1 / 16
    field_simp [hB.ne']
  have hSignAt := hSign v hv
  change (W v * mixedThetaCompletedTruncation K s v).im +
    M * (2 * r / (m : ℝ)) + ‖W v‖ * τ ≤ -(1 / 2)
  linarith only [hSignAt, hGrid, hErr, hTailAt]

theorem dottie_completed_weighted_samples_iff_nonzero
    (K : Type) [Field K] [NumberField K] (T : ℝ) (n : ℕ) :
    HasDottieCompletedWeightedSamples K T n ↔
      ∀ z ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n),
        mixedThetaContinuation K z ≠ 0 := by
  constructor
  · exact fun h _ hz ↦ mixedTheta_ne_zero_of_dottie_weighted_samples K h hz
  · intro h
    obtain ⟨_, _, hCert⟩ := exists_dottieRationalWeightedSamples_of_nonzero K T n h
    exact ⟨_, hCert⟩

theorem dedekindZetaRH_iff_completed_weighted_samples_to_seven_eighths
    (K : Type) [Field K] [NumberField K] :
    DedekindZetaRH K ↔ HasDottieCompletedWeightedSamplesToSevenEighths K := by
  refine ⟨?_, dedekindZetaRH_of_completed_weighted_samples_to_seven_eighths K⟩
  intro hRH t _
  refine ⟨t - 1, t + 1, ⟨by linarith, by linarith⟩, ?_⟩
  intro ε hε w hw hlo hhi
  obtain ⟨n, hi⟩ := dottieScaledRightDisk_inset_covers (by linarith only [hlo, hε])
    (hhi.trans (by norm_num))
  let a : DottieBandRing (t - 1) (t + 1) := ⟨(w.im + 1 / 512, n), by simpa using hw⟩
  refine ⟨a, mem_ball.mpr (hi.trans_lt ?_), ?_⟩
  · change (30 / 2048) * dottieRingScale n < dottieScaledRadius n
    exact mul_lt_mul_of_pos_right (by norm_num) (dottieRingScale_pos n)
  · apply (dottie_completed_weighted_samples_iff_nonzero K a.val.1 a.val.2).mpr
    intro z hz hzZero
    have hStrip := dottieScaledRightDisk_strip hz
    exact (ne_of_gt hStrip.1) (hRH (mixedThetaContinuation K)
      (mixedThetaContinuation_isDedekind K) z (by linarith only [hStrip.1]) hStrip.2 hzZero)

#check @exists_dottieRationalWeightedSamples_of_nonzero
#check @dottie_completed_weighted_samples_iff_nonzero
#check @dedekindZetaRH_iff_completed_weighted_samples_to_seven_eighths
#print axioms exists_dottieRationalWeightedSamples_of_nonzero
#print axioms dottie_completed_weighted_samples_iff_nonzero
#print axioms dedekindZetaRH_iff_completed_weighted_samples_to_seven_eighths

end FieldTarget
