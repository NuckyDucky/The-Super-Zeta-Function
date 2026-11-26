import GaussianVaughanUpperCofactor
import GaussianVaughanBelowWindowBound

/-! The exact upper-prime approximation and the resulting field criterion. -/

namespace AlpogeSuperZeta

open Complex Filter QuarticModel FieldTarget ArtinPrimitiveRootsConjecture

noncomputable section

theorem archivedGaussianVaughanUpperPrimeSum_error (hDir : DirichletLZerosOnLine)
    (W : ℝ → ℝ) (hW : ∀ u ≥ 0, |W u| ≤ 1)
    (hUnit : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → W u = 1) (hSupport : ∀ u ≥ 2, W u = 0) :
    ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop,
      |archivedGaussianVaughanSum X - archivedGaussianVaughanUpperPrimeSum W X| ≤
        C * X ^ (3 / 8 : ℝ) := by
  obtain ⟨A, hA, hHigher⟩ := archivedGaussianVaughanHigherKernel_left_powerBound hDir
  obtain ⟨B, hB, hShort⟩ := archivedGaussianVaughanShortPrimeReading_inv_bound W hW hSupport
  obtain ⟨C, hC, hTail⟩ := archivedGaussianVaughanUpperCofactorTail_inv_bound W hW hUnit
  refine ⟨A + B + C, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), hShort, hTail] with X hX hShort hTail
  have hx := zero_lt_one.trans hX
  let V := X / (Real.log X) ^ (5 / 2 : ℝ)
  let E := X ^ (3 / 8 : ℝ)
  have hE : 1 ≤ E := Real.one_le_rpow hX.le (by norm_num)
  let R₁ := archivedGaussianVaughanHigherKernel X⁻¹
  let R₂ := archivedGaussianVaughanShortPrimeReading W V X⁻¹
  let R₃ := archivedGaussianVaughanUpperCofactorTail W X
  have h1 : ‖R₁‖ ≤ A * E := by
    have h := hHigher X⁻¹ (inv_pos.mpr hx)
    rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv] at h
    exact h
  have h2 : ‖R₂‖ ≤ B * E := hShort.trans
    ((div_le_self hB hX.le).trans (le_mul_of_one_le_right hB hE))
  have h3 : ‖R₃‖ ≤ C * E := hTail.trans
    ((div_le_self hC hX.le).trans (le_mul_of_one_le_right hC hE))
  have hDiff : archivedGaussianVaughanSum X - archivedGaussianVaughanUpperPrimeSum W X =
      R₁.re + R₂.re + R₃.re := by
    have h := archivedGaussianVaughanUpperPrimeSum_exact W hX hW
    change _ = _ + R₁.re + R₂.re + R₃.re at h
    linarith
  rw [hDiff]
  calc
    _ ≤ |R₁.re| + |R₂.re| + |R₃.re| :=
      (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ A * E + B * E + C * E := by
      exact add_le_add (add_le_add ((abs_re_le_norm _).trans h1) ((abs_re_le_norm _).trans h2))
        ((abs_re_le_norm _).trans h3)
    _ = _ := by dsimp [E]; ring

/-- All three terms of the exact complementary estimate fit the required
error between the full sum and the original lower-prime window. -/
theorem archivedGaussianVaughanLowerPrimeSum_error (hDir : DirichletLZerosOnLine)
    (W : ℝ → ℝ) (hW : ∀ u ≥ 0, |W u| ≤ 1)
    (hUnit : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → W u = 1) (hSupport : ∀ u ≥ 2, W u = 0) :
    ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop,
      |archivedGaussianVaughanSum X - archivedGaussianVaughanLowerSum W X| ≤
        C * (X ^ (3 / 8 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ)) := by
  obtain ⟨A, hA, hUpper⟩ := archivedGaussianVaughanUpperPrimeSum_error hDir W hW hUnit hSupport
  obtain ⟨B, hB, hPrime⟩ := archivedGaussianVaughan_complement_error_with_prime_bound hDir
  obtain ⟨C, hC, hBelow⟩ := archivedGaussianVaughanBelowWindowSum_inv_bound W hW
  refine ⟨A + B + C, by positivity, ?_⟩
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hLog, hUpper, hBelow]
    with X hX hLog hUpper hBelow
  let v := X ^ (3 / 8 : ℝ)
  let E := v * (Real.log X) ^ (8 / 3 : ℝ)
  have hV : 1 ≤ v := Real.one_le_rpow hX.le (by norm_num)
  have hL : 1 ≤ (Real.log X) ^ (8 / 3 : ℝ) := Real.one_le_rpow hLog (by norm_num)
  have hVE : v ≤ E := le_mul_of_one_le_right (zero_le_one.trans hV) hL
  have hCE : |archivedGaussianVaughanBelowWindowSum W X| ≤ C * E :=
    hBelow.trans ((div_le_self hC.le hX.le).trans (le_mul_of_one_le_right hC.le (hV.trans hVE)))
  calc
    _ ≤ |archivedGaussianVaughanSum X - archivedGaussianVaughanUpperPrimeSum W X| +
        B * E + |archivedGaussianVaughanBelowWindowSum W X| := hPrime W hSupport X hX
    _ ≤ A * E + B * E + C * E := add_le_add (add_le_add_left
      (hUpper.trans (mul_le_mul_of_nonneg_left hVE hA)) _) hCE
    _ = _ := by dsimp [E, v]; ring

/-- The upper cutoff, completed primes, and below-window contributions
now have bounds. The signed prime-window inequality is the arithmetic input. -/
theorem quartic_rh_of_archived_vaughan_signed_windows
    (hDir : DirichletLZerosOnLine)
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (W : ℝ → ℝ) (hW : ∀ u ≥ 0, |W u| ≤ 1)
    (hUnit : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → W u = 1) (hSupport : ∀ u ≥ 2, W u = 0)
    (hcut : GaussianCutoffWindowBound (archivedGaussianVaughanLowerSum W)) :
    DedekindZetaRH QuarticModel.K := by
  obtain ⟨A, hA, hError⟩ := archivedGaussianVaughanLowerPrimeSum_error hDir W hW hUnit hSupport
  exact quartic_rh_of_archived_vaughan_prime_windows hDir hFree hpos W hA hError hcut

#check archivedGaussianVaughanUpperPrimeSum_error
#check archivedGaussianVaughanLowerPrimeSum_error
#check quartic_rh_of_archived_vaughan_signed_windows
#print axioms archivedGaussianVaughanUpperPrimeSum_error
#print axioms archivedGaussianVaughanLowerPrimeSum_error
#print axioms quartic_rh_of_archived_vaughan_signed_windows

end
end AlpogeSuperZeta
