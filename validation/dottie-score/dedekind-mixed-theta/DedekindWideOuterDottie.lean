import DedekindWeightedDottieEnclosures

namespace FieldTarget

open Complex Filter Metric Set
open DedekindZetaZeroFree.AbelianQuotient SuperZeta.StirlingCorrection

noncomputable section

/-- The folded Mellin reading gives an extension off its two poles, including
outside the open critical strip. -/
def mixedThetaOuterReading (K : Type) [Field K] [NumberField K] (w : ℂ) : ℂ :=
  (Theta.mixedThetaPair K).Λ₀ w - (Theta.mixedThetaPair K).f₀ / (w * (1 - w))

theorem mixedThetaOuterReading_differentiableOn (K : Type) [Field K] [NumberField K] :
    DifferentiableOn ℂ (mixedThetaOuterReading K) {w | w ≠ 0 ∧ w ≠ 1} := by
  have hFactors : Differentiable ℂ (fun w : ℂ ↦ w * (1 - w)) :=
    differentiable_id.mul ((differentiable_const (1 : ℂ)).sub differentiable_id)
  refine (Theta.mixedThetaPair K).differentiable_Λ₀.differentiableOn.sub
    ((differentiableOn_const (Theta.mixedThetaPair K).f₀).div hFactors.differentiableOn ?_)
  intro w hw
  exact mul_ne_zero hw.1 (sub_ne_zero.mpr hw.2.symm)

/-- Distance in the height coordinate alone can certify avoidance of both poles. -/
theorem dottie_outerDisk_avoids_poles {T ρ : ℝ} (n : ℕ) (hρ : ρ < |T - 1 / 512|) :
    closedBall (dottieScaledRightCenter T n) ρ ⊆ {w : ℂ | w ≠ 0 ∧ w ≠ 1} := by
  intro v hv
  let c := dottieScaledRightCenter T n
  have hBound : ‖v - c‖ ≤ ρ := (dist_eq_norm v c) ▸ mem_closedBall.mp hv
  have hvIm : v.im ≠ 0 := by
    intro hzero
    have h := (abs_im_le_norm (v - c)).trans hBound
    have hDiff : (v - c).im = -(T - 1 / 512) := by
      rw [sub_im]
      change v.im - (T - 1 / 512) = _
      rw [hzero, zero_sub]
    rw [hDiff, abs_neg] at h
    exact (not_le_of_gt hρ) h
  exact ⟨fun h ↦ hvIm (by simp [h]), fun h ↦ hvIm (by simp [h])⟩

#print axioms mixedThetaOuterReading_differentiableOn
#print axioms dottie_outerDisk_avoids_poles

end
end FieldTarget
