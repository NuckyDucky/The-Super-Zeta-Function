import ContourCircleSamples
import DottieCayleyWeightedRiemann

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection
open scoped NNReal

noncomputable section

def dottieCayleySampleRoot : ℂ := exp (2 * (Real.pi : ℂ) * I / 96)

def dottieCayleySamplePoint (j : ℕ) : ℂ :=
  dottieCayleyCenter + (5 / 16 : ℂ) * dottieCayleySampleRoot ^ j

/-- Degree 64, in the normalized displacement from the center. -/
def dottieCayleyZetaPolynomial (samples : ℕ → ℂ) (w : ℂ) : ℂ :=
  contourSamplePolynomial samples dottieCayleySampleRoot 96 65
    ((w - dottieCayleyCenter) / (5 / 16 : ℂ))

private theorem dottieCayleySampleRoot_primitive : IsPrimitiveRoot dottieCayleySampleRoot 96 := by
  exact Complex.isPrimitiveRoot_exp 96 (by decide)

private theorem dottieCayleySampleRoot_unit : ‖dottieCayleySampleRoot‖ = 1 := by
  rw [dottieCayleySampleRoot, norm_exp]
  norm_num [Complex.div_re, Complex.mul_re, Complex.mul_im]

private theorem dottieCayleyCauchyDisk_bounds {w : ℂ}
    (hw : w ∈ closedBall dottieCayleyCenter (1 / 2 : ℝ)) :
    1 / 4 ≤ w.re ∧ 1 ≤ ‖w - 1‖ ∧ ‖w‖ ≤ 100000003 := by
  have hball : ‖w - dottieCayleyCenter‖ ≤ (1 / 2 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have hcre : dottieCayleyCenter.re = 3 / 4 := by
    norm_num [dottieCayleyCenter, Complex.mul_re]
  have hcim : dottieCayleyCenter.im = 100000001 := by
    norm_num [dottieCayleyCenter, Complex.mul_im]
  have hRe := (Complex.abs_re_le_norm (w - dottieCayleyCenter)).trans hball
  have hIm := (Complex.abs_im_le_norm (w - dottieCayleyCenter)).trans hball
  simp only [Complex.sub_re, Complex.sub_im, hcre, hcim] at hRe hIm
  have hpole := Complex.abs_im_le_norm (w - 1)
  simp only [Complex.sub_im, Complex.one_im, sub_zero] at hpole
  have hcenter : ‖dottieCayleyCenter‖ ≤ 100000002 := by
    have h := Complex.norm_le_abs_re_add_abs_im dottieCayleyCenter
    rw [hcre, hcim] at h
    exact h.trans (by norm_num)
  have hnorm := norm_add_le (w - dottieCayleyCenter) dottieCayleyCenter
  rw [sub_add_cancel] at hnorm
  exact ⟨by linarith [(abs_le.mp hRe).1],
    by linarith [(abs_le.mp hIm).1, le_abs_self w.im],
    by linarith⟩

/-- The explicit zeta growth inequality supplies the majorant on the larger disk. -/
theorem dottieCayleyCauchyMajorant_of_growth
    (growth : ∀ w : ℂ, 0 < w.re → w ≠ 1 →
      ‖riemannZeta w‖ ≤ 1 + 1 / ‖w - 1‖ + ‖w‖ * (1 + 1 / w.re)) :
    ∀ w ∈ sphere dottieCayleyCenter (1 / 2 : ℝ), ‖riemannZeta w‖ ≤ 10 ^ 9 := by
  intro w hw
  obtain ⟨hre, hsep, hnorm⟩ := dottieCayleyCauchyDisk_bounds (sphere_subset_closedBall hw)
  have hre0 : 0 < w.re := (by norm_num : (0 : ℝ) < 1 / 4).trans_le hre
  have hne : w ≠ 1 := by rintro rfl; norm_num at hsep
  have h1 : 1 / ‖w - 1‖ ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  have h4 : 1 / w.re ≤ 4 := (div_le_iff₀ hre0).mpr (by linarith)
  calc
    _ ≤ 1 + 1 / ‖w - 1‖ + ‖w‖ * (1 + 1 / w.re) := growth w hre0 hne
    _ ≤ 1 + 1 + 100000003 * (1 + 4) := by gcongr
    _ ≤ _ := by norm_num

/-- The actual 96 samples suffice with a uniform error below one billionth,
provided each sample has error at most one trillionth. -/
theorem dottieCayleyZetaPolynomial_error_le (samples : ℕ → ℂ)
    (hM : ∀ w ∈ sphere dottieCayleyCenter (1 / 2 : ℝ), ‖riemannZeta w‖ ≤ 10 ^ 9)
    (hSample : ∀ j < 96, ‖samples j - riemannZeta (dottieCayleySamplePoint j)‖ ≤ 1 / 10 ^ 12)
    {w : ℂ} (hw : w ∈ closedBall dottieCayleyCenter (31 / 128 : ℝ)) :
    ‖riemannZeta w - dottieCayleyZetaPolynomial samples w‖ ≤ 1 / 10 ^ 9 := by
  have hF : DifferentiableOn ℂ riemannZeta (closedBall dottieCayleyCenter (↑(1 / 2 : ℝ≥0))) := by
    intro z hz
    have hz' : z ∈ closedBall dottieCayleyCenter (1 / 2 : ℝ) := by simpa using hz
    have hsep := (dottieCayleyCauchyDisk_bounds hz').2.1
    have hne : z ≠ 1 := by rintro rfl; norm_num at hsep
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  have hM' : ∀ z ∈ sphere dottieCayleyCenter (↑(1 / 2 : ℝ≥0)), ‖riemannZeta z‖ ≤ (10 : ℝ) ^ 9 := by
    simpa using hM
  have hx : ‖w - dottieCayleyCenter‖ ≤ (31 / 128 : ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have h := contourSamplePolynomial_error_le (N := 96) (n := 65) (h := 5 / 16)
    hF hM' (by norm_num) (by norm_num) dottieCayleySampleRoot_primitive dottieCayleySampleRoot_unit
    (by norm_num) (by norm_num) hx (by simpa only [dottieCayleySamplePoint, ofReal_div,
      ofReal_ofNat] using hSample)
  rw [add_sub_cancel, ofReal_div, ofReal_ofNat, ofReal_ofNat] at h
  unfold dottieCayleyZetaPolynomial
  apply h.trans
  norm_num

private theorem dottieCayleyContour_mem_closedBall {a : ℂ} (ha : a ∈ contourQuarterTurns) (t : ℝ) :
    rationalContourPoint dottieCayleyCenter (31 / 128) a t ∈
      closedBall dottieCayleyCenter (31 / 128 : ℝ) := by
  have haNorm : ‖a‖ = 1 := by
    simp only [contourQuarterTurns, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> simp
  apply sphere_subset_closedBall
  rw [mem_sphere, dist_eq_norm]
  simp [rationalContourPoint, haNorm, rationalUnitArc_norm]

/-- The signed arc check can now use the finite polynomial in place of exact
zeta evaluations on each interval. The weight multiplies the error allowance. -/
theorem dottieCayley_riemannZeta_ne_zero_of_sample_polynomial {W : ℂ → ℂ} {m : ℕ}
    (hW : DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1)) (hm : 0 < m)
    (samples : ℕ → ℂ)
    (hM : ∀ w ∈ sphere dottieCayleyCenter (1 / 2 : ℝ), ‖riemannZeta w‖ ≤ 10 ^ 9)
    (hSample : ∀ j < 96, ‖samples j - riemannZeta (dottieCayleySamplePoint j)‖ ≤ 1 / 10 ^ 12)
    (hArcs : ∀ a ∈ contourQuarterTurns, ∀ j : Fin m, ∀ t ∈
      Icc (((j : ℕ) : ℝ) / m) ((((j : ℕ) : ℝ) + 1) / m),
      let w := rationalContourPoint dottieCayleyCenter (31 / 128) a t
      (W w * dottieCayleyZetaPolynomial samples w).im + ‖W w‖ / 10 ^ 9 ≤ -(1 / 16)) :
    ∀ w ∈ closedBall dottieCayleyCenter (31 / 128 : ℝ), riemannZeta w ≠ 0 := by
  apply dottieCayley_riemannZeta_ne_zero_of_weighted_arcs hW hm
  intro a ha j t ht
  let w := rationalContourPoint dottieCayleyCenter (31 / 128) a t
  have hP := dottieCayleyZetaPolynomial_error_le samples hM hSample (dottieCayleyContour_mem_closedBall ha t)
  have herr : (W w * (riemannZeta w - dottieCayleyZetaPolynomial samples w)).im ≤ ‖W w‖ / 10 ^ 9 := by
    refine (Complex.im_le_norm _).trans ?_
    rw [norm_mul, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hP) (norm_nonneg _)
  change (W w * riemannZeta w).im ≤ -(1 / 16)
  rw [mul_sub, Complex.sub_im] at herr
  have hsign := hArcs a ha j t ht
  dsimp only at hsign
  linarith

#print axioms dottieCayleyCauchyMajorant_of_growth
#print axioms dottieCayleyZetaPolynomial_error_le
#check @dottieCayley_riemannZeta_ne_zero_of_sample_polynomial
#print axioms dottieCayley_riemannZeta_ne_zero_of_sample_polynomial

end

end FieldTarget
