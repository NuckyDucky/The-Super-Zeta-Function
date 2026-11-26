import GaussianVaughanPrimeBand
import GaussianVaughanNegativeWindow
import GaussianBiquadraticInertWeights

/-! The sign-reversed prime band is the inert count of the biquadratic
base minus its exact rational-character comparison on the same primes. -/

namespace AlpogeSuperZeta

open Filter Finset QuarticModel ArtinPrimitiveRootsConjecture
open scoped Classical

noncomputable section

private def biquadraticSplit (p : ℕ) : ℝ :=
  if p % 4 = 1 ∧ rationalNormSign p = 1 then 2 else 0

private theorem biquadratic_inert_excess_eq_neg {p : ℕ} (hp : p.Prime)
    (hp₂ : p ≠ 2) (hpD : p.Coprime 26509772707289) :
    biquadraticInertDegreeOneWeight p - biquadraticSplit p = -archivedGaussianPrimeWeight p := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases h : p % 4 = 1 ∧ rationalNormSign p = 1
  · have hI := archivedInertDegreeOneWeight_of_good_prime hp₂ hpD
    rw [ZMod.χ₄_nat_one_mod_four h.1] at hI
    simp only [biquadraticInertDegreeOneWeight, biquadraticSplit, if_pos h]
    norm_num at hI
    linarith
  · have hZero : archivedGaussianPrimeWeight p = 0 := by
      by_contra hn
      exact h ((archivedGaussianPrimeWeight_ne_zero_iff hp₂ hpD).mp hn)
    simp [biquadraticInertDegreeOneWeight, biquadraticSplit, h, hZero]

/-- Twice the split-prime reading is subtracted from the degree-one
inert reading, with the same two-scale theta weight in each sum. -/
def archivedGaussianVaughanInertExcess (X : ℝ) : ℝ :=
  ∑ p ∈ archivedGaussianVaughanBandPrimes X,
    (biquadraticInertDegreeOneWeight p - biquadraticSplit p) *
      (Real.log (p : ℝ) * archivedGaussianVaughanKernel (p / X))

theorem archivedGaussianVaughanInertExcess_eq_neg {X : ℝ} (hX : 1 < X)
    (hStart : 26509772707289 < X / (Real.log X) ^ (1 / 6 : ℝ)) :
    archivedGaussianVaughanInertExcess X = -archivedGaussianVaughanPrimeBand X := by
  rw [archivedGaussianVaughanInertExcess, archivedGaussianVaughanPrimeBand_eq_sum hX,
    ← sum_neg_distrib]
  refine sum_congr rfl fun p hp => ?_
  obtain ⟨⟨hlo, _⟩, hprime⟩ := (mem_archivedGaussianVaughanBandPrimes hX p).mp hp
  have hbig : 26509772707289 < p := by exact_mod_cast hStart.trans_le hlo
  have h₂ : p ≠ 2 := ne_of_gt ((by decide : (2 : ℕ) ≤ 26509772707289).trans_lt hbig)
  have hD : p.Coprime 26509772707289 := hprime.coprime_iff_not_dvd.mpr fun hd =>
    hbig.not_ge (Nat.le_of_dvd (by decide) hd)
  rw [biquadratic_inert_excess_eq_neg hprime h₂ hD, neg_mul]

theorem archivedGaussianVaughanInertExcess_eventually_eq_neg :
    ∀ᶠ X : ℝ in atTop,
      archivedGaussianVaughanInertExcess X = -archivedGaussianVaughanPrimeBand X := by
  have hRoot := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
    (eventually_gt_atTop (26509772707289 : ℝ))
  have hLog := (isLittleO_log_rpow_rpow_atTop (1 / 6 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).def one_pos
  filter_upwards [eventually_gt_atTop (1 : ℝ), hRoot, hLog] with X hX hRoot hLog
  have hx := zero_lt_one.trans hX
  have hL₀ := Real.rpow_pos_of_pos (Real.log_pos hX) (1 / 6 : ℝ)
  have hU : (Real.log X) ^ (1 / 6 : ℝ) ≤ X ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_of_nonneg hL₀.le, Real.norm_of_nonneg
      (Real.rpow_nonneg hx.le (1 / 2 : ℝ)), one_mul] using hLog
  have hS : X ^ (1 / 2 : ℝ) ≤ X / (Real.log X) ^ (1 / 6 : ℝ) := by
    apply (le_div_iff₀ hL₀).mpr
    calc
      _ ≤ X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hU (Real.rpow_nonneg hx.le _)
      _ = X := by rw [← Real.rpow_add hx, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]
  exact archivedGaussianVaughanInertExcess_eq_neg hX (hRoot.trans_le hS)

/-- The upper estimate for the inert excess supplies the sign-reversed
window. The same Gaussian factor and the same pole locations are used. -/
theorem quartic_rh_of_archived_vaughan_inert_excess_windows
    (hDir : DirichletLZerosOnLine)
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianVaughanInertExcess) :
    DedekindZetaRH QuarticModel.K := by
  obtain ⟨A, hA, hError⟩ := archivedGaussianVaughanPrimeBand_approx hDir
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hDiff : ∀ᶠ X : ℝ in atTop,
      |(-archivedGaussianVaughanSum X) - archivedGaussianVaughanInertExcess X| ≤
        A * (X ^ (3 / 8 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hError, hLog,
      archivedGaussianVaughanInertExcess_eventually_eq_neg] with X hX hError hLog hEq
    rw [hEq, neg_sub_neg, abs_sub_comm]
    have hP : 0 ≤ X ^ (3 / 8 : ℝ) := Real.rpow_nonneg (zero_le_one.trans hX.le) _
    have hL : 1 ≤ (Real.log X) ^ (8 / 3 : ℝ) := Real.one_le_rpow hLog (by norm_num)
    exact hError.trans (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hP hL) hA)
  exact quartic_rh_of_archived_vaughan_negative_sum_windows hDir hFree hpos
    (gaussianLogWindow_error_transfer hA hDiff hcut)

#check quartic_rh_of_archived_vaughan_inert_excess_windows
#print axioms archivedGaussianVaughanInertExcess_eq_neg
#print axioms archivedGaussianVaughanInertExcess_eventually_eq_neg
#print axioms quartic_rh_of_archived_vaughan_inert_excess_windows

end
end AlpogeSuperZeta
