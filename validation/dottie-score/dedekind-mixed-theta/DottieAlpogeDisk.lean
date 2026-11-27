import DottieNearOneDisk
import DottieCayleyGrowthBridge
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoGrowthBall
import Mathlib.Analysis.Real.Pi.Bounds

namespace FieldTarget

open Complex Metric SuperZeta.StirlingCorrection

/-- Transfer the original radius-half zeta estimate pointwise to a Dottie
disk, using the same height and the exact containment inequality. -/
theorem riemannZeta_le_on_dottie_disk_of_alpoge {σ t : ℝ} {n : ℕ}
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (ht : 3 ≤ |t|)
    (hfit : σ - 1 ≤ dottieRingScale n / 2048)
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter (t + 1 / 512) n) (dottieScaledRadius n)) :
    ‖riemannZeta w‖ ≤ 6 * (|t| + 2) :=
  Formalism.ZF.zfo_growth_ball Formalism.ZF.growthBound hσ hσ₂ ht (by linarith [abs_nonneg t])
    ((dottie_disk_subset_near_one_iff hσ.le n).mpr hfit hw)

theorem riemannZeta_cayley_disk_bound_from_alpoge
    (w : ℂ) (hw : w ∈ closedBall dottieCayleyCenter (31 / 128 : ℝ)) :
    ‖riemannZeta w‖ ≤ 600000018 := by
  let t : ℝ := 100000001
  have ht : 3 ≤ |t| := by norm_num [t]
  obtain ⟨hlo, hhi⟩ := alpogeNearOneReal_bounds ht
  have hσ₂ : alpogeNearOneReal t ≤ 2 := hhi.trans (by norm_num)
  have hfit : alpogeNearOneReal t - 1 ≤ dottieRingScale 0 / 2048 := by
    norm_num [dottieRingScale]
    linarith
  have hw' : w ∈ closedBall (dottieScaledRightCenter (t + 1 / 512) 0) (dottieScaledRadius 0) := by
    change w ∈ closedBall (dottieScaledRightCenter dottieCayleyReference 0) (dottieScaledRadius 0)
    simpa only [dottieCayley_center_eq, dottieCayley_radius_eq] using hw
  have hb := riemannZeta_le_on_dottie_disk_of_alpoge hlo hσ₂ ht hfit hw'
  norm_num [t] at hb
  exact hb

/-- The common thirds-reference factor for either native word, expressed
at the ordinary input `w = 2*s`. -/
private theorem norm_nativeThirdFactor_le_four {w : ℂ} (h₀ : 0 ≤ w.re) (h₁ : w.re ≤ 1) :
    ‖(Real.pi : ℂ) ^ (-w) * ((3 : ℂ) ^ w - 1)‖ ≤ 4 := by
  have hπ : ‖(Real.pi : ℂ) ^ (-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (neg_nonpos.mpr h₀)
  have h3 : ‖(3 : ℂ) ^ w‖ ≤ 3 := by
    rw [show (3 : ℂ) = ((3 : ℝ) : ℂ) from rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) h₁
  have hsub : ‖(3 : ℂ) ^ w - 1‖ ≤ 4 := by
    exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  rw [norm_mul]
  exact (mul_le_mul hπ hsub (norm_nonneg _) zero_le_one).trans (by norm_num)

theorem native_thirds_reading_le_on_dottie_disk_of_alpoge {σ t : ℝ} {n : ℕ}
    (hσ : 1 < σ) (hσ₂ : σ ≤ 2) (ht : 3 ≤ |t|)
    (hfit : σ - 1 ≤ dottieRingScale n / 2048)
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter (t + 1 / 512) n) (dottieScaledRadius n)) :
    ‖((Real.pi : ℂ) ^ (-w) * ((3 : ℂ) ^ w - 1)) * riemannZeta w‖ ≤ 24 * (|t| + 2) := by
  have hs := dottieScaledRightDisk_strip hw
  have hA := norm_nativeThirdFactor_le_four (by linarith [hs.1]) hs.2.le
  have hζ := riemannZeta_le_on_dottie_disk_of_alpoge hσ hσ₂ ht hfit hw
  rw [norm_mul]
  exact (mul_le_mul hA hζ (norm_nonneg _) (by norm_num)).trans (by linarith)

#print axioms Formalism.ZF.zfo_growth_ball
#check @riemannZeta_le_on_dottie_disk_of_alpoge
#print axioms riemannZeta_le_on_dottie_disk_of_alpoge
#print axioms riemannZeta_cayley_disk_bound_from_alpoge
#print axioms native_thirds_reading_le_on_dottie_disk_of_alpoge

end FieldTarget
