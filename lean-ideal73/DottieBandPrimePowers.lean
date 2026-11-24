import ArchivedQuarticLatticeCoefficients
import DottieBandPrimality
import DottieRowSign
import DottieBandCoefficientChecks
import DottieRetainedBandBounds

/-! Compute the exact split prime-power coefficients using the two
Gaussian ideals. Certify the first nonzero retained-band coefficient. -/

namespace QuarticModel

open Finset PowerSeries
open scoped Classical
set_option autoImplicit false

theorem dottie_band_split_prime_power {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) (hn : (-r)^2 = -1) (e : ℕ) :
    archivedLatticeCoeff (p^e) = ∑ j ∈ range (e+1),
      archivedIdealCharacter (gaussianPrimeAt r hr)^j *
        archivedIdealCharacter (gaussianPrimeAt (-r) hn)^(e-j) := by
  let IPos := gaussianPrimeAt r hr
  let INeg := gaussianPrimeAt (-r) hn
  let cPos := archivedIdealCharacter IPos
  let cNeg := archivedIdealCharacter INeg
  have hs : gaussianPrimesAbove p = {IPos,INeg} := split_gaussian_primes hp r hr hn
  have hne : IPos ≠ INeg := gaussianPrimeAt_distinct hp r hr
  have hmPos : IPos ∈ gaussianPrimesAbove p := by simp [hs]
  have hmNeg : INeg ∈ gaussianPrimesAbove p := by simp [hs]
  have he : signedLocalEulerSeries p =
      weightedGeometricAtDegree (cPos : ℂ) 1 * weightedGeometricAtDegree (cNeg : ℂ) 1 := by
    rw [signedLocalEulerSeries, Finset.prod_coe_sort (gaussianPrimesAbove p)
      (fun I => weightedGeometricAtDegree (archivedIdealCharacter I : ℂ) (I.inertiaDeg ℤ)),
      hs, Finset.prod_insert (by simpa only [Finset.mem_singleton] using hne),
      Finset.prod_singleton, primeAt_degree r hr hmPos, primeAt_degree (-r) hn hmNeg]
  apply Int.cast_injective (α := ℂ)
  rw [archivedLatticeCoeff_eq_signedIdealNormSum _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    signedIdealNormSum_primePower, he, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [coeff_weightedGeometricAtDegree _ (by decide : (1 : ℕ) ≠ 0),cPos,cNeg,IPos,INeg]

theorem dottie_retained_band_first_nonzero_coeff :
    archivedLatticeCoeff 1854467118035498909 = 2 := by
  let p : ℕ := 1854467118035498909
  let : Fact p.Prime := ⟨dottie_first_nonzero_band_prime⟩
  let r : ZMod p := 595362390891366445
  have hr : r^2 = -1 := by decide +kernel
  have hn : (-r)^2 = -1 := by simpa only [neg_sq] using hr
  let zPos : GaussianInt := ⟨1121841470,771970747⟩
  let zNeg : GaussianInt := ⟨1121841470,-771970747⟩
  have hrPos : gaussianResidue r hr zPos = 0 := by
    change (1121841470 : ZMod p)+771970747*r = 0
    decide +kernel
  have hrNeg : gaussianResidue (-r) hn zNeg = 0 := by
    change (1121841470 : ZMod p)+((-771970747 : ℤ) : ZMod p)*(-r) = 0
    rw [Int.cast_neg,neg_mul_neg]
    exact hrPos
  have hPos : gaussianPrimeAt r hr = Ideal.span {zPos} :=
    gaussianPrimeAt_eq_span r hr zPos (by decide +kernel) hrPos
  have hNeg : gaussianPrimeAt (-r) hn = Ideal.span {zNeg} :=
    gaussianPrimeAt_eq_span (-r) hn zNeg (by decide +kernel) hrNeg
  have hzPos : archivedGaussianSign zPos = 1 := by
    rw [← dottieRowSign_eq_archivedGaussianSign 1121841470 771970747]
    decide +kernel
  have hzNeg : archivedGaussianSign zNeg = 1 := by
    rw [← dottieRowSign_eq_archivedGaussianSign 1121841470 (-771970747)]
    decide +kernel
  have h := dottie_band_split_prime_power (p := p) (by decide) r hr hn 1
  rw [pow_one,hPos,hNeg,archivedIdealCharacter_span,archivedIdealCharacter_span,hzPos,hzNeg] at h
  simpa [p] using h

theorem dottie_retained_band_before_first_nonzero (i : ℕ) (hi : i < 15) :
    archivedLatticeCoeff (1854467118035498894+i) = 0 := by
  by_cases hi₈ : i < 8
  · exact dottie_retained_band_first_eight_zero i hi₈
  · have hlo : 8 ≤ i := Nat.le_of_not_gt hi₈
    interval_cases i
    · exact dottie_band_zero_check_sound (twos := 1) (m := 927233559017749451)
        (signCode := none) (by decide +kernel)
    · exact dottie_band_zero_check_sound (twos := 0) (m := 1854467118035498903)
        (signCode := none) (by decide +kernel)
    · exact dottie_band_zero_check_sound (twos := 3) (m := 231808389754437363)
        (signCode := none) (by decide +kernel)
    · exact dottie_band_zero_check_sound (twos := 0) (m := 1854467118035498905)
        (signCode := some 1085064926) (by decide +kernel)
    · exact dottie_band_zero_check_sound (twos := 1) (m := 991)
        (signCode := none) (by decide +kernel)
    · exact dottie_band_zero_check_sound (twos := 0) (m := 1854467118035498907)
        (signCode := none) (by decide +kernel)
    · exact dottie_band_zero_check_sound (twos := 2) (m := 463616779508874727)
        (signCode := none) (by decide +kernel)

/-- First actual chunk in the same integer sum format consumed by the
full retained-band integral. -/
theorem dottie_retained_band_first_chunk :
    DottieBandIntegerSums 1854467118035498894 1854467118035498909 2 2 := by
  have hzero (k : ℕ) (hk : k ≤ 15) :
      (∑ i ∈ range k, archivedLatticeCoeff (1854467118035498894+i)) = 0 := by
    exact Finset.sum_eq_zero (fun i hi => dottie_retained_band_before_first_nonzero i
      ((mem_range.mp hi).trans_le hk))
  constructor
  · intro k hk
    rw [hzero k hk]
    norm_num
  · change |∑ i ∈ range (15+1), archivedLatticeCoeff (1854467118035498894+i)| ≤ 2
    rw [sum_range_succ,hzero 15 le_rfl]
    change |0+archivedLatticeCoeff 1854467118035498909| ≤ 2
    rw [dottie_retained_band_first_nonzero_coeff]
    norm_num

#print axioms dottie_band_split_prime_power
#print axioms dottie_retained_band_first_nonzero_coeff
#print axioms dottie_retained_band_before_first_nonzero
#print axioms dottie_retained_band_first_chunk

end QuarticModel
