import DottieJointSharpChunk0
import DottieJointSharpChunk128
import DottieJointSharpChunk256
import DottieJointSharpChunk384
import DottieJointSharpChunk512
import DottieJointSharpChunk640
import DottieJointSharpChunk768
import DottieJointSharpChunk896

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false

def dottieSharp1024Ticks : List (ℤ × ℤ) := [
  (10635297314757000, -3381976410176912),
  (-6779627022985059, 2155940430071511),
  (2160886571258360, -687183843258154),
  (-459162992326351, 146021854608271),
  (73175052918189, -23271481897268),
  (-9329302974765, 2967018141778),
  (991183584268, -315235496230),
  (-90263508820, 28708019511),
  (7192475231, -2287596380),
  (-509438763, 162032844),
  (32474933, -10329276)
]

private theorem noPairs (f : ℕ → ℤ) (a lo : ℕ) : dottiePairRowBlock f a lo 0 = 0 := rfl

/-- The complete 1,024-pair sharp block, assembled from eight checked pieces. -/
theorem dottie_sharp_1024_moments (k : Fin 11) :
    dottiePairRowBlock (fun n => momentWeightRealTicks n k) 26858 0 1024 =
      (dottieSharp1024Ticks.getD k (0,0)).1 ∧
    dottiePairRowBlock (fun n => momentWeightImagTicks n k) 26858 0 1024 =
      (dottieSharp1024Ticks.getD k (0,0)).2 := by
  have hDiv : (1024 : ℕ)/128 = 8 := by decide +kernel
  have hMod : (1024 : ℕ)%128 = 0 := by decide +kernel
  constructor
  · rw [dottiePairRowBlock_eq_blocks _ _ _ 128, hDiv, hMod]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.zero_mul, noPairs,
      (dottie_sharp_chunk0_moments k).1, (dottie_sharp_chunk128_moments k).1, (dottie_sharp_chunk256_moments k).1, 
      (dottie_sharp_chunk384_moments k).1, (dottie_sharp_chunk512_moments k).1, (dottie_sharp_chunk640_moments k).1, 
      (dottie_sharp_chunk768_moments k).1, (dottie_sharp_chunk896_moments k).1]
    fin_cases k <;> decide +kernel
  · rw [dottiePairRowBlock_eq_blocks _ _ _ 128, hDiv, hMod]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.zero_mul, noPairs,
      (dottie_sharp_chunk0_moments k).2, (dottie_sharp_chunk128_moments k).2, (dottie_sharp_chunk256_moments k).2, 
      (dottie_sharp_chunk384_moments k).2, (dottie_sharp_chunk512_moments k).2, (dottie_sharp_chunk640_moments k).2, 
      (dottie_sharp_chunk768_moments k).2, (dottie_sharp_chunk896_moments k).2]
    fin_cases k <;> decide +kernel

theorem dottie_sharp_1024_within_cutoff : 1024 ≤ dottiePairRowSize 1442840576 26858 := by
  decide +kernel

#print axioms dottie_sharp_1024_moments
#print axioms dottie_sharp_1024_within_cutoff

end QuarticModel.DottieFixedIntervals
