import DottieMarkedHeight

/-! Apply dyadic homotheties about the critical line at the selected Dottie
height. The height witnesses and the original point stay available separately. -/

namespace SuperZeta.StirlingCorrection

open Complex Function Set SuperZeta.Reciprocal
open scoped ComplexConjugate

noncomputable section

/-- The largest disk uses sixteen times the archived radius. Subsequent
disks halve both the radius and the distance of the center from the line. -/
def dottieRingScale (n : ℕ) : ℝ := 16 * (1 / 2 : ℝ) ^ n

def dottieScaledRightCenter (T : ℝ) (n : ℕ) : ℂ :=
  ⟨1 / 2 + dottieRingScale n / 64, T - 1 / 512⟩

def dottieScaledRadius (n : ℕ) : ℝ := (31 / 2048) * dottieRingScale n

private theorem dottieRingScale_pos (n : ℕ) : 0 < dottieRingScale n := by
  unfold dottieRingScale
  positivity

private theorem dottieRingScale_le (n : ℕ) : dottieRingScale n ≤ 16 := by
  have h : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold dottieRingScale
  linarith

private theorem exists_dottieRingScale {x : ℝ} (hx : 0 < x) (hmax : x ≤ 63 / 128) :
    ∃ n : ℕ, dottieRingScale n / 2048 ≤ x ∧ x ≤ (63 / 2048) * dottieRingScale n := by
  classical
  have hex : ∃ n : ℕ, dottieRingScale n / 2048 ≤ x := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 128 * x by positivity)
      (by norm_num : (1 / 2 : ℝ) < 1)
    exact ⟨n, by unfold dottieRingScale; linarith⟩
  let n := Nat.find hex
  refine ⟨n, Nat.find_spec hex, ?_⟩
  by_cases hn : n = 0
  · rw [hn]
    norm_num [dottieRingScale]
    exact hmax
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hmn : m < Nat.find hex := by simpa only [← show n = Nat.find hex from rfl, hm] using Nat.lt_succ_self m
    have hprev : x < dottieRingScale m / 2048 := lt_of_not_ge (Nat.find_min hex hmn)
    have hpos := dottieRingScale_pos m
    rw [hm, dottieRingScale, pow_succ]
    change 0 < 16 * (1 / 2 : ℝ) ^ m at hpos
    change x < (16 * (1 / 2 : ℝ) ^ m) / 2048 at hprev
    linarith

/-- The original horizontal bounds dilate by exactly the selected scale. -/
theorem dottieScaledRightDisk_real_bounds {T : ℝ} {n : ℕ} {w : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    dottieRingScale n / 2048 ≤ w.re - 1 / 2 ∧
      w.re - 1 / 2 ≤ (63 / 2048) * dottieRingScale n := by
  have hn : ‖w - dottieScaledRightCenter T n‖ ≤ dottieScaledRadius n := by
    simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw
  have hb := abs_le.mp ((Complex.abs_re_le_norm _).trans hn)
  have hl : -((31 / 2048 : ℝ) * dottieRingScale n) ≤
      w.re - (1 / 2 + dottieRingScale n / 64) := hb.1
  have hr : w.re - (1 / 2 + dottieRingScale n / 64) ≤
      (31 / 2048) * dottieRingScale n := hb.2
  exact ⟨by linarith, by linarith⟩

/-- Every scaled disk stays entirely on its own side of the critical line
and strictly inside the strip, including its circumference. -/
theorem dottieScaledRightDisk_strip {T : ℝ} {n : ℕ} {w : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    1 / 2 < w.re ∧ w.re < 1 := by
  obtain ⟨hl, hr⟩ := dottieScaledRightDisk_real_bounds hw
  constructor
  · linarith [dottieRingScale_pos n]
  · linarith [dottieRingScale_le n]

/-- At the reference height of the original input, some scaled disk covers
each real coordinate in the right strip through `127/128`. -/
theorem dottieScaledRightDisk_covers {w : ℂ}
    (hlo : 1 / 2 < w.re) (hhi : w.re ≤ 127 / 128) :
    ∃ n : ℕ, w ∈ Metric.closedBall (dottieScaledRightCenter (w.im + 1 / 512) n)
      (dottieScaledRadius n) := by
  obtain ⟨n, hlo', hhi'⟩ := exists_dottieRingScale
    (show 0 < w.re - 1 / 2 by linarith) (show w.re - 1 / 2 ≤ 63 / 128 by linarith)
  refine ⟨n, Metric.mem_closedBall.mpr ?_⟩
  have h : w - dottieScaledRightCenter (w.im + 1 / 512) n =
      ((w.re - (1 / 2 + dottieRingScale n / 64) : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · simp [dottieScaledRightCenter]
  rw [dist_eq_norm, h, Complex.norm_real, Real.norm_eq_abs, dottieScaledRadius]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Reflection across the critical line carries the entire right disk to the
left disk at the same height and with the same radius. -/
theorem dottieScaledRightDisk_reflect {T : ℝ} {n : ℕ} {w : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    1 - conj w ∈ Metric.closedBall (1 - conj (dottieScaledRightCenter T n)) (dottieScaledRadius n) := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw ⊢
  rw [show 1 - conj w - (1 - conj (dottieScaledRightCenter T n)) =
      -conj (w - dottieScaledRightCenter T n) by rw [map_sub]; ring, norm_neg, Complex.norm_conj]
  exact hw

/-- The same height witnesses can nominate wider measuring disks. The disk
contains the original complex input, with a scale chosen from its real part. -/
theorem dottie_scaled_band_selects_marked_returns {w : ℂ}
    (hlo : 1 / 2 < w.re) (hhi : w.re ≤ 127 / 128)
    (him : w.im + 1 / 512 ∈ Icc (dottieHeight - 10^8) (dottieHeight + 10^8))
    (hmarked : ∀ x ∈ Icc (archivedDottieFlank - dottieFlankWidth)
        (archivedDottieFlank + dottieFlankWidth), ∀ right : Bool,
        ∃ P Q, MarkedDottiePair (dottieWitnessLift right x) P Q (dottieWitnessWinding right)) :
    ∃ x n, dottieHeightAtFlank x = w.im + 1 / 512 ∧
      w ∈ Metric.closedBall (dottieScaledRightCenter (dottieHeightAtFlank x) n) (dottieScaledRadius n) ∧
      ∀ right : Bool, ∃ P Q,
        MarkedDottiePair (dottieWitnessLift right x) P Q (dottieWitnessWinding right) ∧
        minimalPeriod (step (dottieWitnessLift right x)) (P, Q) = 640 := by
  let w₀ : ℂ := ⟨33 / 64, w.im⟩
  have hre : w₀.re ∈ Icc (1 / 2 + 1 / 2048) (1 / 2 + 63 / 2048) := by
    norm_num [w₀, mem_Icc]
  obtain ⟨x, hheight, _, hpair⟩ := dottie_band_selects_marked_returns hre him hmarked
  obtain ⟨n, hw⟩ := dottieScaledRightDisk_covers hlo hhi
  exact ⟨x, n, hheight, by rw [hheight]; exact hw, hpair⟩

#print axioms dottieScaledRightDisk_real_bounds
#print axioms dottieScaledRightDisk_strip
#print axioms dottieScaledRightDisk_covers
#print axioms dottieScaledRightDisk_reflect
#print axioms dottie_scaled_band_selects_marked_returns

end

end SuperZeta.StirlingCorrection

namespace QuarticModel

open Complex SuperZeta.StirlingCorrection
open scoped ComplexConjugate

/-- With the retained and remainder bounds on the chosen circumference,
the same signed test excludes zeros of the actual quartic Gaussian factor
on the full scaled disk and its reflected partner. -/
theorem archivedScaledRightDisk_exclusion_of_remainder {T S : ℝ} {n : ℕ}
    (hS : 0 < S) (H : ℂ → ℂ)
    (model : ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (H z).im ≤ -(190 * ((z.re - 1 / 2) * S)))
    (tail : ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (archivedMellin z - H z).im ≤ 189 * ((z.re - 1 / 2) * S))
    {w : ℂ} (hw : w ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    (archivedMellin w).im ≤ -(dottieRingScale n * S / 2048) ∧
      dottieRingScale n * S / 2048 ≤ (archivedMellin (1 - conj w)).im ∧
      archivedGaussianFactor w ≠ 0 ∧ archivedGaussianFactor (1 - conj w) ≠ 0 := by
  have hs := dottieRingScale_pos n
  have hr : 0 < dottieScaledRadius n := mul_pos (by norm_num) hs
  have hboundary : ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (archivedMellin z).im ≤ -(dottieRingScale n * S / 2048) := by
    intro z hz
    have hgap := (dottieScaledRightDisk_real_bounds (Metric.sphere_subset_closedBall hz)).1
    have hscaled := mul_le_mul_of_nonneg_right hgap hS.le
    have htail := tail z hz
    rw [sub_im] at htail
    linarith [model z hz]
  have hright := archivedMellin_im_le_on_disk hr hboundary hw
  have hleft : dottieRingScale n * S / 2048 ≤ (archivedMellin (1 - conj w)).im := by
    rw [(archivedMellin_mirror_coordinates w).2]
    linarith
  have hmargin : 0 < dottieRingScale n * S / 2048 := div_pos (mul_pos hs hS) (by norm_num)
  obtain ⟨hRe, hRe'⟩ := dottieScaledRightDisk_strip hw
  have hMirrorRe : 0 < (1 - conj w).re := by simp; linarith
  refine ⟨hright, hleft, ?_, ?_⟩
  · intro hz
    rw [(archivedGaussianFactor_zero_iff_mellin (by linarith : 0 < w.re)).mp hz, zero_im] at hright
    linarith
  · intro hz
    rw [(archivedGaussianFactor_zero_iff_mellin hMirrorRe).mp hz, zero_im] at hleft
    linarith

#print axioms archivedScaledRightDisk_exclusion_of_remainder

end QuarticModel
