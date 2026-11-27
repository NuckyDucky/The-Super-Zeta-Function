import DottieDyadicGeometry
import Mathlib.Analysis.Complex.ExponentialBounds

namespace FieldTarget

open Complex Metric SuperZeta.StirlingCorrection

/-- At the same height, the Dottie disk fits in the radius-half disk
centered at `σ + t I` exactly up to its leftmost real coordinate. -/
theorem dottie_disk_subset_near_one_iff {σ t : ℝ} (hσ : 1 ≤ σ) (n : ℕ) :
    closedBall (dottieScaledRightCenter (t + 1 / 512) n) (dottieScaledRadius n) ⊆
      closedBall ((σ : ℂ) + (t : ℂ) * I) (1 / 2 : ℝ) ↔
    σ - 1 ≤ dottieRingScale n / 2048 := by
  let c := dottieScaledRightCenter (t + 1 / 512) n
  let a := (σ : ℂ) + (t : ℂ) * I
  let r := dottieScaledRadius n
  let x := 1 / 2 + dottieRingScale n / 64
  have hr : 0 ≤ r := (mul_pos (by norm_num : (0 : ℝ) < 31 / 2048) (dottieRingScale_pos n)).le
  have hc : c ∈ closedBall (dottieScaledRightCenter (t + 1 / 512) n) (dottieScaledRadius n) :=
    mem_closedBall_self hr
  have hx : x < 1 := (dottieScaledRightDisk_strip hc).2
  have hδ : c - a = ((x - σ : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [a, c, x, dottieScaledRightCenter, Complex.mul_re]
    · simp [a, c, dottieScaledRightCenter, Complex.mul_im]
  have hd : dist c a = σ - x := by
    rw [dist_eq_norm, hδ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  have hedge : c - (r : ℂ) ∈ closedBall c r := by
    rw [mem_closedBall, dist_eq_norm, show c - (r : ℂ) - c = -(r : ℂ) by ring,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  have hedgeDist : dist (c - (r : ℂ)) a = σ - x + r := by
    rw [dist_eq_norm, sub_right_comm c (r : ℂ) a, hδ, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    ring
  change closedBall c r ⊆ closedBall a (1 / 2 : ℝ) ↔ _
  constructor
  · intro h
    have hleft := mem_closedBall.mp (h hedge)
    rw [hedgeDist] at hleft
    dsimp [r, dottieScaledRadius, x] at hleft
    linarith
  · intro hs
    apply closedBall_subset_closedBall'
    rw [hd]
    dsimp [r, dottieScaledRadius, x]
    linarith

/-- The real center used in the original large-height zero-free argument. -/
noncomputable def alpogeNearOneReal (t : ℝ) : ℝ :=
  1 + 1 / (10000 * Real.log (|t| + 2))

theorem alpogeNearOneReal_bounds {t : ℝ} (ht : 3 ≤ |t|) :
    1 < alpogeNearOneReal t ∧ alpogeNearOneReal t ≤ 1 + 1 / 128 := by
  have hlog : 1 < Real.log (|t| + 2) := by
    apply (Real.lt_log_iff_exp_lt (by linarith)).mpr
    linarith [Real.exp_one_lt_d9]
  have hpos : 0 < 10000 * Real.log (|t| + 2) := by linarith
  have hsmall : 1 / (10000 * Real.log (|t| + 2)) ≤ (1 : ℝ) / 128 :=
    (one_div_le_one_div_of_le (by norm_num) (by linarith))
  exact ⟨by unfold alpogeNearOneReal; linarith [one_div_pos.mpr hpos],
    by unfold alpogeNearOneReal; linarith⟩

theorem dottie_base_disk_subset_alpoge {t : ℝ} (ht : 3 ≤ |t|) :
    closedBall (dottieScaledRightCenter (t + 1 / 512) 0) (dottieScaledRadius 0) ⊆
      closedBall ((alpogeNearOneReal t : ℂ) + (t : ℂ) * I) (1 / 2 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := alpogeNearOneReal_bounds ht
  apply (dottie_disk_subset_near_one_iff hlo.le 0).mpr
  norm_num [dottieRingScale]
  linarith

#check @dottie_disk_subset_near_one_iff
#print axioms dottie_disk_subset_near_one_iff
#print axioms dottie_base_disk_subset_alpoge

end FieldTarget
