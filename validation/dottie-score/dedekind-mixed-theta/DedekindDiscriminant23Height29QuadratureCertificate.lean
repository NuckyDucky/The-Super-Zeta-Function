import Discriminant23ClassMellinGauss
import DedekindDiscriminant23Height29FactorEnclosures
import DedekindDiscriminant23Height29DFT

namespace FieldTarget

open Complex Metric SuperZeta.StirlingCorrection

noncomputable section

theorem discriminant23_height29_sample_coordinate_bounds (j : ℕ) :
    1 / 4 ≤ (discriminant23Height29ReadingPoint j).re ∧
    (discriminant23Height29ReadingPoint j).re ≤ 5 / 4 ∧
    |(discriminant23Height29ReadingPoint j).im| ≤ 59 / 2 := by
  let d : ℂ := ((1 / 2 : ℝ) : ℂ) * discriminant23Height29Root ^ j
  have hNorm : ‖d‖ = 1 / 2 := by
    dsimp only [d]
    rw [norm_mul, norm_pow, discriminant23_height29_root_primitive.norm'_eq_one (by norm_num),
      one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hRe := abs_le.mp ((abs_re_le_norm d).trans_eq hNorm)
  have hIm := abs_le.mp ((abs_im_le_norm d).trans_eq hNorm)
  rw [show discriminant23Height29ReadingPoint j = (3 / 4 : ℂ) + 29 * I + d by
    rw [discriminant23Height29ReadingPoint, discriminant23_height29_dottie_geometry.1]]
  have h₁ : ((3 / 4 : ℂ) + 29 * I).re = 3 / 4 := by norm_num [Complex.mul_re]
  have h₂ : ((3 / 4 : ℂ) + 29 * I).im = 29 := by norm_num [Complex.mul_im]
  rw [Complex.add_re, Complex.add_im, h₁, h₂]
  exact ⟨by linarith only [hRe.1], by linarith only [hRe.2],
    abs_le.mpr ⟨by linarith only [hIm.1], by linarith only [hIm.2]⟩⟩

/-- The pole is accounted for at the same point as the quadrature. -/
def discriminant23Height29BaseQuadrature (w : ℂ) : ℂ :=
  discriminant23ClassCombinationQuadrature 2 w - (3 / 2 : ℂ) / (w * (1 - w))

theorem discriminant23_height29_base_quadrature_error (j : ℕ) :
    ‖discriminant23Height29BaseFactor (discriminant23Height29ReadingPoint j) -
      discriminant23Height29BaseQuadrature (discriminant23Height29ReadingPoint j)‖ ≤ 2 / 10 ^ 26 := by
  let w := discriminant23Height29ReadingPoint j
  obtain ⟨hlo, hhi, ht⟩ := discriminant23_height29_sample_coordinate_bounds j
  have h := discriminant23_classCombination_quadrature_error (b := 2) (by norm_num) (w := w)
    (by change -1 / 4 ≤ (discriminant23Height29ReadingPoint j).re; linarith only [hlo])
    hhi (ht.trans (by norm_num))
  rw [discriminant23_classCombinationReading_two] at h
  change ‖discriminant23Height29BaseFactor w - discriminant23Height29BaseQuadrature w‖ ≤ _
  rw [show discriminant23Height29BaseFactor w - discriminant23Height29BaseQuadrature w =
      discriminant23TotalClassReading w - discriminant23ClassCombinationQuadrature 2 w by
    unfold discriminant23Height29BaseFactor discriminant23Height29BaseQuadrature
    ring]
  exact h

theorem discriminant23_height29_hecke_quadrature_error (j : ℕ) :
    ‖discriminant23CharacterClassReading (discriminant23Height29ReadingPoint j) -
      discriminant23ClassCombinationQuadrature (-1) (discriminant23Height29ReadingPoint j)‖ ≤
      2 / 10 ^ 26 := by
  let w := discriminant23Height29ReadingPoint j
  obtain ⟨hlo, hhi, ht⟩ := discriminant23_height29_sample_coordinate_bounds j
  have h := discriminant23_classCombination_quadrature_error (b := -1) (by norm_num) (w := w)
    (by change -1 / 4 ≤ (discriminant23Height29ReadingPoint j).re; linarith only [hlo])
    hhi (ht.trans (by norm_num))
  simpa only [discriminant23_classCombinationReading_neg_one] using h

/-- The remaining hypotheses concern finite quadrature sums at the fixed samples. -/
theorem discriminant23_height29_ne_zero_of_quadrature_enclosures
    (hBase : ∀ j < 128, ‖discriminant23Height29BaseQuadrature (discriminant23Height29ReadingPoint j) -
      discriminant23Height29BaseApprox j‖ ≤ 8 / 10 ^ 26)
    (hHecke : ∀ j < 128, ‖discriminant23ClassCombinationQuadrature (-1) (discriminant23Height29ReadingPoint j) -
      discriminant23Height29HeckeApprox j‖ ≤ 8 / 10 ^ 26)
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter (29 + 1 / 512) 0) (dottieWeightOuterRadius 0)) :
    mixedThetaContinuation Discriminant23GaloisField w ≠ 0 ∧
    mixedThetaContinuation (discriminant23QuadraticSubfield : Type) w ≠ 0 ∧
    discriminant23CharacterFold w ≠ 0 := by
  apply discriminant23_height29_ne_zero_of_sample_enclosures _ hw
  apply discriminant23_height29_sample_error_of_factor_enclosures
  · intro j hj
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add (discriminant23_height29_base_quadrature_error j) (hBase j hj)).trans (by norm_num))
  · intro j hj
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      ((add_le_add (discriminant23_height29_hecke_quadrature_error j) (hHecke j hj)).trans (by norm_num))

#check @discriminant23_height29_ne_zero_of_quadrature_enclosures
#print axioms discriminant23_height29_sample_coordinate_bounds
#print axioms discriminant23_height29_base_quadrature_error
#print axioms discriminant23_height29_hecke_quadrature_error
#print axioms discriminant23_height29_ne_zero_of_quadrature_enclosures

end
end FieldTarget
