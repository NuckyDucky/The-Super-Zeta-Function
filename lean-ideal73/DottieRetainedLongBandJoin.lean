import DottieBandArchivedShort4096
import DottieBandArchivedShort2
import DottieBandArchivedShort3

/-! Join each original long band to its already verified short neighbor.
The result uses the exact three integer premises of the contour estimate. -/

namespace QuarticModel

set_option autoImplicit false

theorem dottie_retained_quarter_bounds_of_long_chunk
    (h : DottieBandChunk 1854467118035498894 131072 ⟨148,-20,438⟩) :
    DottieBandIntegerSums 1854467118035498894 1854467118035634061 438 12 := by
  have joined := dottie_band_append_chunks h DottieBandBlock1854467118035629966_4096.certificate
  exact dottie_band_integer_sums_of_chunk joined (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem dottie_retained_half_bounds_of_long_chunk
    (h : DottieBandChunk 3708934236071001884 262144 ⟨562,-36,998⟩) :
    DottieBandIntegerSums 3708934236071001884 3708934236071268123 998 482 := by
  have joined := dottie_band_append_chunks h DottieBandBlock3708934236071264028_4096.certificate
  exact dottie_band_integer_sums_of_chunk joined (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem dottie_retained_full_bounds_of_long_chunk
    (h : DottieBandChunk 7417868472142007863 524288 ⟨1320,-4,1550⟩) :
    DottieBandIntegerSums 7417868472142007863 7417868472142536246 1550 1338 := by
  have joined := dottie_band_append_chunks h DottieBandBlock7417868472142532151_4096.certificate
  exact dottie_band_integer_sums_of_chunk joined (by decide +kernel) (by decide +kernel) (by decide +kernel)

open SuperZeta.StirlingCorrection in
theorem dottie_retained_bands_bound_of_long_chunks
    (h₄ : DottieBandChunk 1854467118035498894 131072 ⟨148,-20,438⟩)
    (h₂ : DottieBandChunk 3708934236071001884 262144 ⟨562,-36,998⟩)
    (h₁ : DottieBandChunk 7417868472142007863 524288 ⟨1320,-4,1550⟩)
    {w : ℂ} (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖∑ n ∈ dottieRetainedBandNorms, dottieSmoothTerm w n‖ ≤ 36/10^35 :=
  dottie_retained_bands_bound_of_integer_sums
    (dottie_retained_quarter_bounds_of_long_chunk h₄)
    (dottie_retained_half_bounds_of_long_chunk h₂)
    (dottie_retained_full_bounds_of_long_chunk h₁) hr hi

#print axioms dottie_retained_quarter_bounds_of_long_chunk
#print axioms dottie_retained_half_bounds_of_long_chunk
#print axioms dottie_retained_full_bounds_of_long_chunk
#print axioms dottie_retained_bands_bound_of_long_chunks

end QuarticModel
