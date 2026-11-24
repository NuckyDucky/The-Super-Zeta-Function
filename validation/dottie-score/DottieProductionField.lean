import DottieProductionReferenceTight
import DottieMomentArchiveScores
import DottieQuarterCombinedCertificate
import DottieHalfCombinedCertificate
import DottieLongBand3Assembly

namespace QuarticModel

open SuperZeta SuperZeta.StirlingCorrection
open private archivedRightInput_val from ArchivedQuarticSpectralAddress

/-- Use the sharpened signed allowance at the same recovered input. -/
theorem dottieProductionRightNonzero_of_tight_signed
    (hsharp : ∀ k < 11, (DottieFixedIntervals.archivedScoredMomentBox dottiePrefixEnd k).fits
      (DottieFixedIntervals.fixedSharpInput k) = true)
    (href : ∀ k < 6, (DottieFixedIntervals.archivedScoredMomentBox 276824064 k).fits
      (DottieFixedIntervals.fixedReferenceInput k) = true)
    (hsigned : ∀ z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31 / 2048),
      (dottieOmittedSharpBlock z + dottieShorterMiddleSmooth z).im ≤
        (188889 / 1000) * ((z.re - 1 / 2) * dottieCircleReference))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) (ink : ℂ → ℂ)
    (hR : riemannZeta w ≠ 0) (hB : FieldCoefficientTransfer.chi4.LFunction w ≠ 0) :
    archivedQuarticZeta w ≠ 0 := by
  have hretained : ∀ z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31 / 2048),
      (dottieRetained z).im ≤ -(190 * ((z.re - 1 / 2) * dottieCircleReference)) := by
    apply dottie_retained_margin_of_finite_band_bound dottieProductionCircleReference_lower
      (DottieFixedIntervals.dottie_sharp_margin_of_archive_score_checks hsharp href)
    intro z hz
    obtain ⟨hr, hi⟩ := dottie_right_sphere_coordinate_bounds hz
    exact dottie_retained_bands_bound_of_integer_sums dottie_retained_quarter_integer_sums
      dottie_retained_half_integer_sums
      (dottie_retained_full_bounds_of_long_chunk DottieLongBand3Assembly.certificate) hr hi
  have hS : 0 < dottieCircleReference := lt_of_lt_of_le (by norm_num)
    dottieProductionCircleReference_tight
  have ht := archivedDottie_chart_painted_orders hS hretained
    (fun z hz => dottieProductionOmitted_of_tight_signed hz (hsigned z hz)) hw ink
  obtain ⟨_, _, _, _, _, horders, _⟩ := ht
  let x := archivedRightInput hw
  have hx : x.val = w := archivedRightInput_val hw
  intro hz
  obtain hRzero | hBzero | hGaussian := (archivedFieldZero_at_chart x ink).mp (by rwa [hx])
  · have hs₀ : 0 < (x.val / 2).re := by linarith only [x.property.1.1]
    have hs₁ : (x.val / 2).re < 1 / 2 := by linarith only [x.property.1.2]
    have he := (UnitSpectrum.equality_iff_riemann_zero hs₀ hs₁).2.mp
      (show UnitSpectrum.continuation (x.val / 2) = _ from hRzero)
    rw [show 2 * (x.val / 2) = x.val by ring, hx] at he
    exact hR he
  · exact hB (hx ▸ hBzero)
  · exact horders hGaussian

theorem dottieProductionRightNonzero
    (hsharp : ∀ k < 11, (DottieFixedIntervals.archivedScoredMomentBox dottiePrefixEnd k).fits
      (DottieFixedIntervals.fixedSharpInput k) = true)
    (href : ∀ k < 6, (DottieFixedIntervals.archivedScoredMomentBox 276824064 k).fits
      (DottieFixedIntervals.fixedReferenceInput k) = true)
    (hsigned : ∀ z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31 / 2048),
      (dottieOmittedSharpBlock z + dottieShorterMiddleSmooth z).im ≤
        188 * ((z.re - 1 / 2) * dottieCircleReference))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) (ink : ℂ → ℂ)
    (hR : riemannZeta w ≠ 0) (hB : FieldCoefficientTransfer.chi4.LFunction w ≠ 0) :
    archivedQuarticZeta w ≠ 0 := by
  apply dottieProductionRightNonzero_of_tight_signed hsharp href _ hw ink hR hB
  intro z hz
  have hscale : 0 ≤ (z.re - 1 / 2) * dottieCircleReference :=
    (by norm_num : (0 : ℝ) ≤ (1 / 2048) * (2 / 10^30)).trans (dottieProductionCircleScale_lower hz)
  exact (hsigned z hz).trans (mul_le_mul_of_nonneg_right (by norm_num) hscale)

#print axioms dottieProductionRightNonzero_of_tight_signed
#print axioms dottieProductionRightNonzero

end QuarticModel
