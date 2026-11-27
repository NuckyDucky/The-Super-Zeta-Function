import DedekindMixedThetaSignedRings
import DedekindMixedThetaTail

/-! On the open strip neither pole-clearing factor vanishes. The completed
reading gives the same zero test with an absolute Mellin tail bound that is
independent of the height. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex MeasureTheory Set
open DedekindZetaZeroFree.AbelianQuotient

noncomputable section

private theorem pole_factor_ne_zero {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) :
    w * (1 - w) ≠ 0 := by
  have h0 : w ≠ 0 := by rintro rfl; norm_num at hlo
  have h1 : w ≠ 1 := by rintro rfl; norm_num at hhi
  exact mul_ne_zero h0 (sub_ne_zero.mpr h1.symm)

/-- The completed mixed-theta reading without the two pole-clearing factors. -/
def mixedThetaCompletedReading (K : Type*) [Field K] [NumberField K] (w : ℂ) : ℂ :=
  mixedThetaSignedReading K w / (w * (1 - w))

theorem mixedThetaCompletedReading_zero_iff (K : Type*) [Field K] [NumberField K]
    (w : ℂ) (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaCompletedReading K w = 0 ↔ mixedThetaContinuation K w = 0 := by
  rw [mixedThetaCompletedReading, div_eq_zero_iff, or_iff_left (pole_factor_ne_zero hlo hhi)]
  exact mixedThetaSignedReading_zero_iff K w hlo hhi

theorem mixedThetaCompletedReading_differentiableOn (K : Type*) [Field K] [NumberField K] :
    DifferentiableOn ℂ (mixedThetaCompletedReading K) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
  have hp : Differentiable ℂ (fun w : ℂ => w * (1 - w)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  exact (mixedThetaSignedReading_differentiableOn K).div hp.differentiableOn
    (fun w hw => pole_factor_ne_zero hw.1 hw.2)

theorem mixedThetaCompletedReading_eq_mellin (K : Type) [Field K] [NumberField K]
    (w : ℂ) (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaCompletedReading K w = (Theta.mixedThetaPair K).Λ₀ w -
      (Theta.mixedThetaPair K).f₀ / (w * (1 - w)) := by
  rw [mixedThetaCompletedReading, mixedThetaSignedReading_eq_mellin_sub K w hlo hhi, sub_div,
    mul_div_cancel_left₀ _ (pole_factor_ne_zero hlo hhi)]

/-- Retain the finite folded integral and keep the pole term exact. -/
def mixedThetaCompletedTruncation (K : Type) [Field K] [NumberField K] (R : ℝ)
    (w : ℂ) : ℂ :=
  mixedThetaTruncation K R w - (Theta.mixedThetaPair K).f₀ / (w * (1 - w))

theorem mixedThetaCompletedTruncation_error_le (K : Type) [Field K] [NumberField K]
    (R : ℝ) (hR : 1 ≤ R) (w : ℂ) (hlo : 0 < w.re) (hhi : w.re < 1) :
    ‖mixedThetaCompletedReading K w - mixedThetaCompletedTruncation K R w‖ ≤
      2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ := by
  rw [mixedThetaCompletedReading_eq_mellin K w hlo hhi, mixedThetaCompletedTruncation,
    sub_sub_sub_cancel_right]
  exact mixedTheta_mellin_tail_le K R hR w hlo.le hhi.le

/-- A unit rotation leaves the tail budget unchanged. This transfers a
computed signed bound on the retained integral to the full reading. -/
theorem mixedThetaCompletedReading_im_le_of_truncation (K : Type) [Field K] [NumberField K]
    (R : ℝ) (hR : 1 ≤ R) (axis w : ℂ) (haxis : ‖axis‖ = 1)
    (hlo : 0 < w.re) (hhi : w.re < 1) :
    (axis * mixedThetaCompletedReading K w).im ≤
      (axis * mixedThetaCompletedTruncation K R w).im +
        2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ := by
  have h := mixedThetaCompletedTruncation_error_le K R hR w hlo hhi
  have hdiff : (axis * (mixedThetaCompletedReading K w -
      mixedThetaCompletedTruncation K R w)).im ≤
      2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ := by
    refine (le_abs_self _).trans ((abs_im_le_norm _).trans ?_)
    rw [norm_mul, haxis, one_mul]
    exact h
  rw [mul_sub, sub_im] at hdiff
  exact ((sub_le_iff_le_add).mp hdiff).trans_eq (add_comm _ _)

/-- The finite-ring argument can use the completed reading with its smaller
absolute Mellin tail budget. -/
theorem dedekindZetaRH_of_completed_mixedTheta_signed_rings (K : Type*)
    [Field K] [NumberField K]
    (h31 : ∀ w : ℂ, 31 / 32 < w.re → w.re < 1 → mixedThetaContinuation K w ≠ 0)
    (hbands : ∀ N : ℕ, HasFiniteDottieBoundaryCertificate
      (mixedThetaContinuation K) (mixedThetaCompletedReading K) (-(N : ℝ)) (N : ℝ)) :
    DedekindZetaRH K :=
  dedekindZetaRH_of_finite_signed_dottie_boundaries
    (mixedThetaContinuation_isDedekind K) (mixedThetaCompletedReading_differentiableOn K)
    (fun w hlo hhi => (mixedThetaCompletedReading_zero_iff K w hlo hhi).mpr)
    (mixedThetaContinuation_reflects K) h31 hbands

#check @dedekindZetaRH_of_completed_mixedTheta_signed_rings
#print axioms mixedThetaCompletedReading_zero_iff
#print axioms mixedThetaCompletedReading_differentiableOn
#print axioms mixedThetaCompletedReading_eq_mellin
#print axioms mixedThetaCompletedTruncation_error_le
#print axioms mixedThetaCompletedReading_im_le_of_truncation
#print axioms dedekindZetaRH_of_completed_mixedTheta_signed_rings

end

end FieldTarget
