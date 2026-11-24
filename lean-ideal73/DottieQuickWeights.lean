import DottieCachedLog
import DottieReferenceScore

/-! Use the cached mantissa and reduced atanh argument in the exact same
reference score. Each new integer weight has the original error budget. -/

namespace QuarticModel

open private quarticCosine cos_four quarticCosine_distance from DottieReferenceWeights
open private referenceCosArgument reference_weight_error_of from DottieReferenceScore

private def quickCosineQuarterTicks (L : ℕ) : ℤ :=
  (fixedCosBounds (dottieAngleNumeratorOf L) dottieAngleDenominator).1

private def quickCosineTicks (n : ℕ) : ℤ :=
  let c := quickCosineQuarterTicks (dottieCachedLogLowerTicks n)
  let b := (fixedCosScale : ℤ)
  8*c^4-8*b^2*c^2+b^4

/-- Evaluates the integer weighted cosine after eight residual log terms. -/
def dottieQuickWeightTicks (n : ℕ) : ℤ :=
  (inverseSqrtTicks fixedCosScale n : ℤ)*quickCosineTicks n

private theorem quickCosine_scaled (L : ℕ) :
    |quarticCosine ((quickCosineQuarterTicks L : ℝ)/fixedCosScale) -
      Real.cos (4*(dottieNormAngleQuarterOf L : ℝ))| ≤ 288*(6/2^48) := by
  let q : ℝ := (dottieNormAngleQuarterOf L : ℝ)
  let c : ℝ := (quickCosineQuarterTicks L : ℝ)/fixedCosScale
  have enclosure := fixedCosBounds_spec (dottieAngleNumeratorOf L) dottieAngleDenominator
    dottieAngleDenominator_pos (dottieAngleNumeratorOf_natAbs_le L)
  rw [dottieAngleTicks_eq_quarter_of] at enclosure
  have hlo : c ≤ Real.cos q := enclosure.1
  have hwidth := fixedCosBounds_width (dottieAngleNumeratorOf L) dottieAngleDenominator
  change _ - c = _ at hwidth
  have hd : |c-Real.cos q| ≤ 6/2^48 := by
    apply abs_le.mpr
    constructor <;> linarith only [hlo, enclosure.2, hwidth]
  have hc : |c| ≤ 2 := by
    calc
      |c| = |c-Real.cos q+Real.cos q| := by rw [sub_add_cancel]
      _ ≤ |c-Real.cos q|+|Real.cos q| := abs_add_le ..
      _ ≤ 2 := by linarith only [hd, Real.abs_cos_le_one q]
  rw [cos_four]
  have h := quarticCosine_distance c (Real.cos q) hc ((Real.abs_cos_le_one _).trans (by norm_num))
  exact h.trans (mul_le_mul_of_nonneg_left hd (by norm_num))

private theorem quick_cosine_error (n : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064) :
    |(quickCosineTicks n : ℝ)/(fixedCosScale : ℝ)^4 -
      Real.cos (referenceCosArgument n)| ≤ 1/1000000 := by
  let L := dottieCachedLogLowerTicks n
  let x : ℝ := ((quickCosineQuarterTicks L : ℝ)/fixedCosScale)
  let y : ℝ := Real.cos (4*(dottieNormAngleQuarterOf L : ℝ))
  let z : ℝ := Real.cos (referenceCosArgument n)
  have hl := dottieCachedLogLowerTicks_spec n hn hcap
  have hs : 0 < (2:ℝ)^96 := by positivity
  have hlo : 0 ≤ Real.log n-(L:ℝ)/2^96 := sub_nonneg.mpr ((div_le_iff₀ hs).2 (by linarith only [hl.1]))
  have hhi : Real.log n-(L:ℝ)/2^96 ≤ (120:ℝ)/2^96 := by
    rw [sub_le_iff_le_add, ← add_div]
    exact (le_div_iff₀ hs).2 (by linarith only [hl.2])
  have he : |y-z| ≤ 1/2000000 := dottie_norm_angle_cosine_error_of n L hn hcap hlo hhi
  have ht : |quarticCosine x-y| ≤ 288*(6/2^48) := quickCosine_scaled L
  have hrepr : (quickCosineTicks n : ℝ)/(fixedCosScale : ℝ)^4 = quarticCosine x := by
    simp only [quickCosineTicks, x, L, quarticCosine, Int.cast_sub, Int.cast_add, Int.cast_mul,
      Int.cast_pow, Int.cast_natCast, Int.cast_ofNat]
    field [show (fixedCosScale:ℝ) ≠ 0 by norm_num [fixedCosScale]]
  rw [hrepr]
  change |quarticCosine x-z| ≤ _
  rw [show quarticCosine x-z = (quarticCosine x-y)+(y-z) by ring]
  exact (abs_add_le _ _).trans ((add_le_add ht he).trans (by norm_num))

theorem dottieQuickWeightTicks_spec (n : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064) :
    |(dottieQuickWeightTicks n : ℝ)/(fixedCosScale : ℝ)^5 -
      (1/Real.sqrt n)*Real.cos (referenceCosArgument n)| ≤ (1/900000)/Real.sqrt n :=
  reference_weight_error_of n hn hcap (quickCosineTicks n) (quick_cosine_error n hn hcap)

#print axioms dottieQuickWeightTicks_spec

end QuarticModel
