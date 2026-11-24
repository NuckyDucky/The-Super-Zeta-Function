import QuarticConductorSign
import Mathlib.Analysis.Complex.AbsMax

/-! The Gaussian zero comparison and the same-height reflection used by the
ring argument, applied to the actual Mellin factor of the quartic field. -/

open Filter MeasureTheory Set
open scoped ComplexConjugate

namespace QuarticModel

open Complex ArtinPrimitiveRootsConjecture FieldCoefficientTransfer

theorem archivedMellin_conj (w : ℂ) : archivedMellin (conj w) = conj (archivedMellin w) := by
  unfold archivedMellin mellin
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg ht0.le]
    exact Real.pi_pos.ne
  have hp : conj ((t : ℂ) ^ (w-1)) = (t : ℂ) ^ (conj w-1) := by
    simpa only [map_sub, map_one, conj_ofReal] using (cpow_conj (t : ℂ) (w-1) harg).symm
  simp only [smul_eq_mul, map_mul, hp, conj_ofReal]

/-- The horizontal mirror preserves height and conjugates the Mellin reading. -/
theorem archivedMellin_mirror (w : ℂ) :
    archivedMellin (1-conj w) = conj (archivedMellin w) :=
  (archivedMellin_functional_equation (conj w)).trans (archivedMellin_conj w)

theorem archivedMellin_mirror_coordinates (w : ℂ) :
    (archivedMellin (1-conj w)).re = (archivedMellin w).re ∧
    (archivedMellin (1-conj w)).im = -(archivedMellin w).im := by
  rw [archivedMellin_mirror]
  exact ⟨conj_re _,conj_im _⟩

/-- The Gaussian strip statement reduces to the original completed reading
on the upper right half of the strip, including the real boundary. -/
theorem archivedGaussian_strip_iff_upper_right :
    FieldTarget.StripZerosOnLine archivedGaussianFactor ↔
      ∀ w : ℂ, (1/2 : ℝ) < w.re → w.re < 1 → 0 ≤ w.im → archivedMellin w ≠ 0 := by
  constructor
  · intro h w hright hhi _ hz
    have hl : 0 < w.re := by linarith
    exact (ne_of_gt hright) (h w hl hhi ((archivedGaussianFactor_zero_iff_mellin hl).mpr hz))
  · intro h w hlo hhi hw
    have hh (z : ℂ) (hr : (1/2 : ℝ) < z.re) (hu : z.re < 1)
        (hz : archivedMellin z = 0) : False := by
      by_cases hi : 0 ≤ z.im
      · exact h z hr hu hi hz
      · apply h (conj z)
        · simpa only [conj_re] using hr
        · simpa only [conj_re] using hu
        · rw [conj_im]
          exact neg_nonneg.mpr (le_of_not_ge hi)
        · rw [archivedMellin_conj, hz, map_zero]
    have hz := (archivedGaussianFactor_zero_iff_mellin hlo).mp hw
    rcases lt_trichotomy w.re (1/2 : ℝ) with hleft | heq | hright
    · exfalso
      apply hh (1-conj w)
      · simp only [sub_re, one_re, conj_re]
        linarith
      · simp only [sub_re, one_re, conj_re]
        linarith
      · rw [archivedMellin_mirror, hz, map_zero]
    · exact heq
    · exact (hh w hright hhi hz).elim

theorem archivedQuarticRH_iff_upper_right :
    DedekindZetaRH K ↔ FieldTarget.StripZerosOnLine riemannZeta ∧
      FieldTarget.StripZerosOnLine chi4.LFunction ∧
      ∀ w : ℂ, (1/2 : ℝ) < w.re → w.re < 1 → 0 ≤ w.im → archivedMellin w ≠ 0 := by
  rw [archivedQuarticRH_iff_three_factors, archivedGaussian_strip_iff_upper_right]

theorem archivedMellin_im_le_on_disk {c : ℂ} {r m : ℝ} (hr : 0 < r)
    (hboundary : ∀ z ∈ Metric.sphere c r, (archivedMellin z).im ≤ -m)
    {w : ℂ} (hw : w ∈ Metric.closedBall c r) : (archivedMellin w).im ≤ -m := by
  let f := fun z : ℂ => Complex.exp (-Complex.I * archivedMellin z)
  have hreg : Differentiable ℂ f := Complex.differentiable_exp.comp
    ((differentiable_const (-Complex.I)).mul (archivedMellin_differentiable archivedTheta_reflection))
  have hnorm (z : ℂ) : ‖f z‖ = Real.exp (archivedMellin z).im := by
    change ‖Complex.exp (-Complex.I * archivedMellin z)‖ = _
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hedge : ∀ z ∈ frontier (Metric.ball c r), ‖f z‖ ≤ Real.exp (-m) := by
    intro z hz
    rw [frontier_ball c hr.ne'] at hz
    rw [hnorm, Real.exp_le_exp]
    exact hboundary z hz
  have hclosed : w ∈ closure (Metric.ball c r) := by rwa [closure_ball c hr.ne']
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
    hreg.diffContOnCl hedge hclosed
  rwa [hnorm, Real.exp_le_exp] at hmax

/-- The archived right-circle center with a variable reference height. -/
noncomputable def archivedRightCenter (T : ℝ) : ℂ := ⟨33/64,T-1/512⟩

theorem archivedRightDisk_horizontal_gap {T : ℝ} {w : ℂ}
    (hw : w ∈ Metric.closedBall (archivedRightCenter T) (31/2048)) :
    1/2048 ≤ w.re - 1/2 := by
  have hn : ‖w-archivedRightCenter T‖ ≤ 31/2048 := by
    simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw
  have hb := (abs_le.mp ((Complex.abs_re_le_norm _).trans hn)).1
  change -(31/2048 : ℝ) ≤ w.re-33/64 at hb
  linarith

/-- A signed enclosure on the published circumference propagates to the
whole disk and its same-height mirror for the actual field's Gaussian factor. -/
theorem archivedRightDisk_exclusion_of_remainder {T S : ℝ} (hS : 0 < S) (H : ℂ → ℂ)
    (model : ∀ w ∈ Metric.sphere (archivedRightCenter T) (31/2048),
      (H w).im ≤ -(190*((w.re-1/2)*S)))
    (tail : ∀ w ∈ Metric.sphere (archivedRightCenter T) (31/2048),
      (archivedMellin w-H w).im ≤ 189*((w.re-1/2)*S))
    {w : ℂ} (hw : w ∈ Metric.closedBall (archivedRightCenter T) (31/2048)) :
    (archivedMellin w).im ≤ -(S/2048) ∧ S/2048 ≤ (archivedMellin (1-conj w)).im ∧
      archivedGaussianFactor w ≠ 0 := by
  have hboundary : ∀ z ∈ Metric.sphere (archivedRightCenter T) (31/2048),
      (archivedMellin z).im ≤ -(S/2048) := by
    intro z hz
    have hgap := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hz).le)
    have hscaled := mul_le_mul_of_nonneg_right hgap hS.le
    have htail := tail z hz
    rw [Complex.sub_im] at htail
    linarith [model z hz]
  have hright := archivedMellin_im_le_on_disk (by norm_num) hboundary hw
  have hleft := (archivedMellin_mirror_coordinates w).2
  have hRe : 0 < w.re := by linarith [archivedRightDisk_horizontal_gap hw]
  refine ⟨hright, by linarith, fun hz => ?_⟩
  have hm := (archivedGaussianFactor_zero_iff_mellin hRe).mp hz
  rw [hm, Complex.zero_im] at hright
  linarith

#print axioms archivedMellin_conj
#print axioms archivedMellin_mirror_coordinates
#print axioms archivedGaussian_strip_iff_upper_right
#print axioms archivedQuarticRH_iff_upper_right
#print axioms archivedRightDisk_exclusion_of_remainder

end QuarticModel
