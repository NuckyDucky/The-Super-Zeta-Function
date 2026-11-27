import DottieCayleyWeightedRiemann
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace FieldTarget

open Complex SuperZeta.StirlingCorrection

noncomputable section

/-- The orange reading uses the same completion, rotation, and scale as the
blue reading, before the exponential factor. -/
def dottieCayleyUnweighted (w : ℂ) : ℂ :=
  (((15 : ℂ) + 8 * I) / 17) * Gammaℝ w / (dottieCayleyScale : ℂ) * riemannZeta w

private theorem weighted_eq_exp_mul_unweighted (w : ℂ) :
    dottieCayleyWeight w * riemannZeta w =
      exp (-((dottieCayleySlope : ℂ) * (w - dottieCayleyCenter))) *
        dottieCayleyUnweighted w := by
  unfold dottieCayleyWeight dottieCayleyUnweighted
  ring

private theorem dottieCayleySlope_bounds : 0 < dottieCayleySlope ∧ dottieCayleySlope < 10 := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hratio : 1 < (100000001 : ℝ) / (2 * Real.pi) :=
    (lt_div_iff₀ hπ).mpr (by linarith [Real.pi_lt_four])
  have hpow : (8 / 3 : ℝ) ^ 20 < Real.exp 20 := by
    rw [show Real.exp 20 = (Real.exp 1) ^ 20 by simp [← Real.exp_nat_mul]]
    exact pow_lt_pow_left₀ (by linarith [Real.exp_one_gt_d9]) (by norm_num) (by decide)
  have hlog : Real.log ((100000001 : ℝ) / (2 * Real.pi)) < 20 := by
    apply (Real.log_lt_iff_lt_exp ((by norm_num : (0 : ℝ) < 1).trans hratio)).mpr
    have hquot : (100000001 : ℝ) / (2 * Real.pi) < 100000001 :=
      (div_lt_iff₀ hπ).mpr (by linarith [Real.pi_gt_three])
    exact hquot.trans ((by norm_num : (100000001 : ℝ) < (8 / 3 : ℝ) ^ 20).trans hpow)
  unfold dottieCayleySlope
  constructor <;> linarith [Real.log_pos hratio]

private theorem exp_eq_one_in_dottieCayleyDisk {w : ℂ}
    (hw : w ∈ Metric.closedBall dottieCayleyCenter (31 / 128 : ℝ)) :
    exp (-((dottieCayleySlope : ℂ) * (w - dottieCayleyCenter))) = 1 ↔
      w = dottieCayleyCenter := by
  let u := -((dottieCayleySlope : ℂ) * (w - dottieCayleyCenter))
  have hsize : ‖u‖ < 2 * Real.pi := by
    have hw' : ‖w - dottieCayleyCenter‖ ≤ (31 / 128 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have hs := dottieCayleySlope_bounds
    dsimp [u]
    rw [norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
    calc
      _ ≤ dottieCayleySlope * (31 / 128 : ℝ) := mul_le_mul_of_nonneg_left hw' hs.1.le
      _ < 2 * Real.pi := by linarith [hs.2, Real.pi_gt_three]
  constructor
  · intro he
    obtain ⟨n, hn⟩ := exp_eq_one_iff.mp (show exp u = 1 from he)
    have hn0 : n = 0 := by
      by_contra hne
      have hInt : (1 : ℤ) ≤ |n| := by have := abs_pos.mpr hne; omega
      have hReal : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast hInt
      rw [hn, norm_mul, norm_mul, norm_I, mul_one, norm_mul, norm_ofNat, norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_intCast] at hsize
      exact (not_lt_of_ge (by nlinarith only [hReal, Real.pi_pos])) hsize
    have hu0 : u = 0 := by simp [hn, hn0]
    have hSlope : (dottieCayleySlope : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr dottieCayleySlope_bounds.1.ne'
    exact sub_eq_zero.mp ((mul_eq_zero.mp (neg_eq_zero.mp hu0)).resolve_left hSlope)
  · intro hz
    simp [hz]

/-- At the same point of this disk, the two readings agree exactly at the
center or at an ordinary zeta zero. A projected crossing can pair two inputs. -/
theorem dottieCayley_same_input_iff {w : ℂ}
    (hw : w ∈ Metric.closedBall dottieCayleyCenter (31 / 128 : ℝ)) :
    dottieCayleyWeight w * riemannZeta w = dottieCayleyUnweighted w ↔
      w = dottieCayleyCenter ∨ riemannZeta w = 0 := by
  have hw' : w ∈ Metric.closedBall (dottieScaledRightCenter dottieCayleyReference 0)
      (dottieScaledRadius 0) := by simpa only [dottieCayley_center_eq, dottieCayley_radius_eq] using hw
  have hr : 0 < w.re := (by norm_num : (0 : ℝ) < 1 / 2).trans (dottieScaledRightDisk_strip hw').1
  have ha : (((15 : ℂ) + 8 * I) / 17) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num [div_re, mul_re, mul_im] at this
  have hγ : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_re_pos hr
  have hscale : (dottieCayleyScale : ℂ) ≠ 0 := ofReal_ne_zero.mpr dottieCayleyScale_pos.ne'
  have heq : dottieCayleyWeight w * riemannZeta w = dottieCayleyUnweighted w ↔
      (exp (-((dottieCayleySlope : ℂ) * (w - dottieCayleyCenter))) - 1) *
        dottieCayleyUnweighted w = 0 := by
    rw [sub_one_mul, sub_eq_zero, weighted_eq_exp_mul_unweighted]
  rw [heq, mul_eq_zero, sub_eq_zero, exp_eq_one_in_dottieCayleyDisk hw]
  simp only [dottieCayleyUnweighted, mul_eq_zero, div_eq_zero_iff, ha, hγ, hscale, false_or]

#check @dottieCayley_same_input_iff
#print axioms dottieCayley_same_input_iff

end

end FieldTarget
