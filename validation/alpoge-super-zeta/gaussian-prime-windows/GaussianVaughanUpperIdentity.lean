import GaussianVaughanHigherKernel
import GaussianVaughanCofactorBound
import GaussianVaughanPrimeComplement

/-! Apply the reciprocal Dirichlet convolution to the upper prime reading.
The higher powers remain a single full reading, before either cutoff. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Finset QuarticModel
open scoped Classical

noncomputable section

private abbrev thetaKernel (v : ℝ) : ℂ := archivedGaussianVaughanKernel v
private abbrev convolvedThetaKernel (v : ℝ) : ℂ := archivedGaussianVaughanConvolvedKernel v

def archivedGaussianVaughanWeightedPrimes (W : ℝ → ℝ) (V : ℝ) : ArithmeticFunction ℂ :=
  ⟨fun p => archivedGaussianVaughanPrimeCoefficients p * (W (p / V) : ℂ), by simp⟩

def archivedGaussianVaughanShortPrimeReading (W : ℝ → ℝ) (V v : ℝ) : ℂ :=
  dirichletKernelSum (archivedGaussianVaughanWeightedPrimes W V) thetaKernel v

def archivedGaussianVaughanWeightedPrimeReading (W : ℝ → ℝ) (V v : ℝ) : ℂ :=
  dirichletKernelSum (archivedGaussianVaughanWeightedPrimes W V) convolvedThetaKernel v

def archivedGaussianVaughanUpperCofactorTail (W : ℝ → ℝ) (X : ℝ) : ℂ :=
  let V := X / (Real.log X) ^ (5 / 2 : ℝ)
  let M := Nat.floor ((Real.log X) ^ (8 / 3 : ℝ))
  ∑' m : ℕ, if M < m then archivedGaussianMoebiusCoefficients m *
    archivedGaussianVaughanWeightedPrimeReading (fun u => 1 - W u) V (m / X) else 0

theorem archivedGaussianMoebius_summable_at_two :
    LSeriesSummable archivedGaussianMoebiusCoefficients (2 : ℂ) := by
  apply LSeriesSummable_of_le_const_mul_rpow (x := 11 / 8) (by norm_num)
  refine ⟨8, fun n hn => ?_⟩
  rw [show (11 / 8 : ℝ) - 1 = 3 / 8 by norm_num]
  exact archivedGaussianMoebius_three_eighths_bound hn

theorem archivedGaussianVaughanWeightedPrimes_term_norm {W : ℝ → ℝ} {V C : ℝ}
    (hV : 0 < V) (hW : ∀ u ≥ 0, |W u| ≤ C) (p : ℕ) :
    ‖LSeries.term (archivedGaussianVaughanWeightedPrimes W V) (2 : ℂ) p‖ ≤
      C * ‖LSeries.term archivedGaussianVaughanPrimeCoefficients (2 : ℂ) p‖ := by
  by_cases hp : p = 0
  · simp [hp]
  rw [LSeries.term_of_ne_zero hp, LSeries.term_of_ne_zero hp]
  change ‖(archivedGaussianVaughanPrimeCoefficients p * (W (p / V) : ℂ)) / (p : ℂ) ^ (2 : ℂ)‖ ≤ _
  rw [show (archivedGaussianVaughanPrimeCoefficients p * (W (p / V) : ℂ)) / (p : ℂ) ^ (2 : ℂ) =
    (W (p / V) : ℂ) * (archivedGaussianVaughanPrimeCoefficients p / (p : ℂ) ^ (2 : ℂ)) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hW _ (by positivity)) (norm_nonneg _)

theorem archivedGaussianVaughanWeightedPrimes_summable {W : ℝ → ℝ} {V C : ℝ}
    (hV : 0 < V) (hW : ∀ u ≥ 0, |W u| ≤ C) :
    LSeriesSummable (archivedGaussianVaughanWeightedPrimes W V) (2 : ℂ) := by
  have hp := archivedGaussianVaughanPrime_summable (z := (2 : ℂ)) (by norm_num)
  exact ((hp.norm.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _)
    (archivedGaussianVaughanWeightedPrimes_term_norm hV hW)).of_norm

private theorem archivedGaussianPrime_ofReal_re (p : ℕ) :
    ((archivedGaussianVaughanPrimeCoefficients p).re : ℂ) = archivedGaussianVaughanPrimeCoefficients p := by
  by_cases hp : p.Prime <;> simp [archivedGaussianVaughanPrimeCoefficients, hp,
    archivedGaussianMangoldt, ← Complex.ofReal_mul]

private theorem convolvedTheta_eq (v : ℝ) :
    dirichletKernelSum signedIdealCoefficients thetaKernel v = convolvedThetaKernel v := by
  unfold dirichletKernelSum convolvedThetaKernel archivedGaussianVaughanConvolvedKernel
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [signedIdealCoefficients_eq_archivedLatticeCoeff, ofReal_mul, intCast_re,
    ofReal_intCast]

private theorem weightedPrimeReading_eq_real (W : ℝ → ℝ) (V v : ℝ) :
    archivedGaussianVaughanWeightedPrimeReading W V v =
      ((∑' p : ℕ, (archivedGaussianVaughanPrimeCoefficients p).re *
        archivedGaussianVaughanConvolvedKernel (p * v) * W (p / V) : ℝ) : ℂ) := by
  unfold archivedGaussianVaughanWeightedPrimeReading dirichletKernelSum
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro p
  simp only [archivedGaussianVaughanWeightedPrimes, coe_mk, ofReal_mul,
    archivedGaussianPrime_ofReal_re]
  ring

private theorem archivedSum_eq_cast_kernelSum {X : ℝ} (hX : 0 < X) :
    (archivedGaussianVaughanSum X : ℂ) =
      dirichletKernelSum archivedGaussianMangoldt thetaKernel X⁻¹ := by
  rw [archivedGaussianVaughanSum, if_pos hX, Complex.ofReal_tsum, dirichletKernelSum]
  apply tsum_congr
  intro n
  have h : ((archivedGaussianMangoldt n).re : ℂ) = archivedGaussianMangoldt n := by
    simp [archivedGaussianMangoldt, ← Complex.ofReal_mul]
  rw [ofReal_mul, h, div_eq_mul_inv]

theorem archivedGaussianVaughanPrime_window_split (W : ℝ → ℝ) (V : ℝ) :
    archivedGaussianMangoldt = archivedGaussianVaughanHigherCoefficients +
      archivedGaussianVaughanWeightedPrimes W V +
      archivedGaussianMoebiusCoefficients *
        (archivedGaussianVaughanWeightedPrimes (fun u => 1 - W u) V * signedIdealCoefficients) := by
  have hUpper :
      archivedGaussianMoebiusCoefficients *
        (archivedGaussianVaughanWeightedPrimes (fun u => 1 - W u) V * signedIdealCoefficients) =
      archivedGaussianVaughanWeightedPrimes (fun u => 1 - W u) V := by
    rw [show archivedGaussianMoebiusCoefficients *
        (archivedGaussianVaughanWeightedPrimes (fun u => 1 - W u) V * signedIdealCoefficients) =
        (archivedGaussianMoebiusCoefficients * signedIdealCoefficients) *
          archivedGaussianVaughanWeightedPrimes (fun u => 1 - W u) V by ac_rfl,
      archivedGaussianMoebius_mul_signed, one_mul]
  rw [hUpper]
  ext p
  change archivedGaussianMangoldt p = archivedGaussianMangoldt p -
    archivedGaussianVaughanPrimeCoefficients p +
    archivedGaussianVaughanPrimeCoefficients p * (W (p / V) : ℂ) +
    archivedGaussianVaughanPrimeCoefficients p * ((1 - W (p / V) : ℝ) : ℂ)
  rw [ofReal_sub, ofReal_one]
  ring

private theorem dirichletKernelSum_of_add {a b : ArithmeticFunction ℂ} {H : ℝ → ℂ}
    {v : ℝ} (ha : Summable (fun n : ℕ => a n * H (n * v)))
    (hb : Summable (fun n : ℕ => b n * H (n * v))) :
    dirichletKernelSum (a + b) H v = dirichletKernelSum a H v + dirichletKernelSum b H v := by
  simpa only [dirichletKernelSum, ArithmeticFunction.add_apply, add_mul] using ha.tsum_add hb

private theorem gaussian_one_sub_weight_norm {W : ℝ → ℝ}
    (hW : ∀ u ≥ 0, |W u| ≤ 1) (u : ℝ) (hu : 0 ≤ u) : |1 - W u| ≤ 2 := by
  exact (abs_sub _ _).trans (by rw [abs_one]; linarith [hW u hu])

private theorem weighted_convolution_as_sum {W : ℝ → ℝ} {V v D : ℝ} (hv : 0 < v)
    (hK : ∀ u > 0, ‖thetaKernel u‖ ≤ D * u ^ (-(2 : ℝ)))
    (hQ : LSeriesSummable (archivedGaussianVaughanWeightedPrimes W V) (2 : ℂ)) :
    dirichletKernelSum (archivedGaussianMoebiusCoefficients *
      (archivedGaussianVaughanWeightedPrimes W V * signedIdealCoefficients)) thetaKernel v =
      ∑' m : ℕ, archivedGaussianMoebiusCoefficients m *
        archivedGaussianVaughanWeightedPrimeReading W V (m * v) := by
  have hB := (archivedGaussianFactor_hasSum (w := (2 : ℂ)) (by norm_num)).LSeriesSummable
  have hQB := ArithmeticFunction.LSeriesSummable_mul hQ hB
  rw [dirichletKernelSum_convolution hv hK archivedGaussianMoebius_summable_at_two hQB]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · simp [hm]
  have hm₀ : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  rw [dirichletKernelSum_convolution (mul_pos hm₀ hv) hK hQ hB]
  simp only [convolvedTheta_eq, archivedGaussianVaughanWeightedPrimeReading]
  rfl

set_option maxHeartbeats 1200000 in
private theorem archivedSum_eq_full_upper (W : ℝ → ℝ) {X V : ℝ} (hX : 0 < X) (hV : 0 < V)
    (hW : ∀ u ≥ 0, |W u| ≤ 1) :
    (archivedGaussianVaughanSum X : ℂ) =
      archivedGaussianVaughanHigherKernel X⁻¹ + archivedGaussianVaughanShortPrimeReading W V X⁻¹ +
      ∑' m : ℕ, archivedGaussianMoebiusCoefficients m *
        archivedGaussianVaughanWeightedPrimeReading (fun u => 1 - W u) V (m / X) := by
  let A := archivedGaussianMoebiusCoefficients
  let B := signedIdealCoefficients
  let P := archivedGaussianVaughanWeightedPrimes W V
  let Q := archivedGaussianVaughanWeightedPrimes (fun u => 1 - W u) V
  let E := archivedGaussianVaughanHigherCoefficients
  have hA : LSeriesSummable A (2 : ℂ) := archivedGaussianMoebius_summable_at_two
  have hB : LSeriesSummable B (2 : ℂ) := (archivedGaussianFactor_hasSum
    (w := (2 : ℂ)) (by norm_num)).LSeriesSummable
  have hP : LSeriesSummable P (2 : ℂ) :=
    archivedGaussianVaughanWeightedPrimes_summable hV hW
  have hQ : LSeriesSummable Q (2 : ℂ) :=
    archivedGaussianVaughanWeightedPrimes_summable hV (gaussian_one_sub_weight_norm hW)
  have hE : LSeriesSummable E (2 : ℂ) := archivedGaussianVaughanHigher_summable (by norm_num)
  obtain ⟨D, _, hTheta⟩ := archivedGaussianVaughanKernel_powerBound (a := 2) (by norm_num)
  have hK (v : ℝ) (hv : 0 < v) : ‖thetaKernel v‖ ≤ D * v ^ (-(2 : ℝ)) := by
    simpa only [norm_real, Real.norm_eq_abs] using hTheta v hv
  have hv := inv_pos.mpr hX
  have hEP := (dirichletKernelSum_summable hv hK hE).of_norm
  have hPP := (dirichletKernelSum_summable hv hK hP).of_norm
  have hEPs : LSeriesSummable (E + P : ArithmeticFunction ℂ) (2 : ℂ) := hE.add hP
  have hEP' := (dirichletKernelSum_summable hv hK hEPs).of_norm
  have hQB := ArithmeticFunction.LSeriesSummable_mul hQ hB
  have hAB := ArithmeticFunction.LSeriesSummable_mul hA hQB
  have hRest := (dirichletKernelSum_summable hv hK hAB).of_norm
  rw [archivedSum_eq_cast_kernelSum hX, archivedGaussianVaughanPrime_window_split W V,
    dirichletKernelSum_of_add hEP' hRest, dirichletKernelSum_of_add hEP hPP]
  rw [weighted_convolution_as_sum hv hK hQ]
  simp only [archivedGaussianVaughanHigherKernel, archivedGaussianVaughanShortPrimeReading,
    ← div_eq_mul_inv, E, P]

set_option maxHeartbeats 1200000 in
/-- The full archived sum is the published upper reading, the complete
higher powers, the small primes, and exactly the omitted cofactors. -/
theorem archivedGaussianVaughanUpperPrimeSum_exact (W : ℝ → ℝ) {X : ℝ} (hX : 1 < X)
    (hW : ∀ u ≥ 0, |W u| ≤ 1) :
    archivedGaussianVaughanSum X =
      archivedGaussianVaughanUpperPrimeSum W X +
      (archivedGaussianVaughanHigherKernel X⁻¹).re +
      (archivedGaussianVaughanShortPrimeReading W (X / (Real.log X) ^ (5 / 2 : ℝ)) X⁻¹).re +
      (archivedGaussianVaughanUpperCofactorTail W X).re := by
  let V := X / (Real.log X) ^ (5 / 2 : ℝ)
  let M := Nat.floor ((Real.log X) ^ (8 / 3 : ℝ))
  let A := archivedGaussianMoebiusCoefficients
  let Q := archivedGaussianVaughanWeightedPrimes (fun u => 1 - W u) V
  let f (m : ℕ) : ℂ := A m *
    archivedGaussianVaughanWeightedPrimeReading (fun u => 1 - W u) V (m / X)
  let ms := Icc 1 M
  have hx := zero_lt_one.trans hX
  have hv := inv_pos.mpr hx
  have hV : 0 < V := div_pos hx (Real.rpow_pos_of_pos (Real.log_pos hX) _)
  have hA : LSeriesSummable A (2 : ℂ) := archivedGaussianMoebius_summable_at_two
  have hQ : LSeriesSummable Q (2 : ℂ) :=
    archivedGaussianVaughanWeightedPrimes_summable hV (gaussian_one_sub_weight_norm hW)
  have hS : (archivedGaussianVaughanSum X : ℂ) =
      archivedGaussianVaughanHigherKernel X⁻¹ + archivedGaussianVaughanShortPrimeReading W V X⁻¹ +
        ∑' m : ℕ, f m :=
    archivedSum_eq_full_upper W hx hV hW
  obtain ⟨K, _, hConvolved⟩ := archivedGaussianVaughanConvolvedKernel_powerBound (s := 2) (by norm_num)
  have hK' (v : ℝ) (hv' : 0 < v) : ‖convolvedThetaKernel v‖ ≤ K * v ^ (-(2 : ℝ)) := by
    simpa only [norm_real, Real.norm_eq_abs] using hConvolved v hv'
  have hU (v : ℝ) (hv' : 0 < v) :
      ‖archivedGaussianVaughanWeightedPrimeReading (fun u => 1 - W u) V v‖ ≤
        (K * ∑' p : ℕ, ‖LSeries.term Q (2 : ℂ) p‖) * v ^ (-(2 : ℝ)) :=
    dirichletKernelSum_norm_le hv' hK' hQ
  have hF : Summable f := by
    simpa only [f, ← div_eq_mul_inv] using (dirichletKernelSum_summable hv hU hA).of_norm
  have hTail : (∑' m : ↑(ms : Set ℕ)ᶜ, f m) = archivedGaussianVaughanUpperCofactorTail W X := by
    rw [_root_.tsum_subtype, archivedGaussianVaughanUpperCofactorTail]
    apply tsum_congr
    intro m
    change ((ms : Set ℕ)ᶜ).indicator f m = if M < m then f m else 0
    by_cases hm : m = 0
    · subst m
      simp [f, A]
    have hm₁ := Nat.pos_of_ne_zero hm
    by_cases hmM : M < m
    · have hms : m ∈ (ms : Set ℕ)ᶜ := by
        intro h
        exact (not_le_of_gt hmM) (mem_Icc.mp h).2
      rw [Set.indicator_of_mem hms, if_pos hmM]
    · have hms : m ∉ (ms : Set ℕ)ᶜ := by
        have h : m ∈ ms := mem_Icc.mpr ⟨hm₁, Nat.le_of_not_gt hmM⟩
        simpa only [Set.mem_compl_iff, not_not, Finset.mem_coe] using h
      rw [Set.indicator_of_notMem hms, if_neg hmM]
  have hSplit : (∑' m : ℕ, f m) = (∑ m ∈ ms, f m) + archivedGaussianVaughanUpperCofactorTail W X := by
    rw [← hTail]
    exact (hF.sum_add_tsum_compl (s := ms)).symm
  have hFin : (∑ m ∈ ms, f m).re = archivedGaussianVaughanUpperPrimeSum W X := by
    change (∑ m ∈ ms, f m).re = ∑ m ∈ ms, (A m).re *
      ∑' p : ℕ, (archivedGaussianVaughanPrimeCoefficients p).re *
        archivedGaussianVaughanConvolvedKernel (p * (m / X)) * (1 - W (p / V))
    rw [← Complex.reCLM_apply, map_sum]
    apply sum_congr rfl
    intro m _
    simp only [f, Complex.reCLM_apply, weightedPrimeReading_eq_real, mul_re, ofReal_re,
      ofReal_im, mul_zero, sub_zero]
  rw [hSplit] at hS
  have h := congrArg Complex.re hS
  simp only [ofReal_re, add_re, hFin] at h
  linarith

#print axioms archivedGaussianVaughanPrime_window_split
#print axioms archivedGaussianVaughanUpperPrimeSum_exact

end
end AlpogeSuperZeta
