import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Shared dyadic disks and reflection in the spectral plane. -/

namespace SuperZeta.StirlingCorrection

open Complex Set
open scoped ComplexConjugate

noncomputable section

/-- The largest disk uses sixteen times the archived radius. Subsequent
disks halve both the radius and the distance of the center from the line. -/
def dottieRingScale (n : ℕ) : ℝ := 16 * (1 / 2 : ℝ) ^ n

def dottieScaledRightCenter (T : ℝ) (n : ℕ) : ℂ :=
  ⟨1 / 2 + dottieRingScale n / 64, T - 1 / 512⟩

def dottieScaledRadius (n : ℕ) : ℝ := (31 / 2048) * dottieRingScale n

theorem dottieRingScale_pos (n : ℕ) : 0 < dottieRingScale n := by
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

#print axioms dottieScaledRightDisk_real_bounds
#print axioms dottieScaledRightDisk_strip
#print axioms dottieScaledRightDisk_covers
#print axioms dottieScaledRightDisk_reflect

end

end SuperZeta.StirlingCorrection
