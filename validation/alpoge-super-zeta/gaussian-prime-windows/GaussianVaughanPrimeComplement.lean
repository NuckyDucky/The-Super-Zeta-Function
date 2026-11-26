import GaussianVaughanConvolvedKernel

/-! The complementary cutoff on the actual Gaussian prime coefficients.
Keeping the full-prime correction and the omitted small primes explicit
gives the exact signed difference that the contour estimates must bound. -/

namespace AlpogeSuperZeta

open Complex Filter Finset
open scoped Classical

noncomputable section

private def primeTerm (v : ℝ) (p : ℕ) : ℝ :=
  (archivedGaussianVaughanPrimeCoefficients p).re *
    archivedGaussianVaughanConvolvedKernel (p * v)

private def primeRange (V : ℝ) : Finset ℕ := range (Nat.floor (2 * V) + 1)

private theorem primeTerm_eq {p : ℕ} (hp : p.Prime) (v : ℝ) :
    primeTerm v p = (archivedGaussianMangoldt p).re *
      archivedGaussianVaughanConvolvedKernel (p * v) := by
  simp [primeTerm, archivedGaussianVaughanPrimeCoefficients, hp]

private theorem primeTerm_zero {p : ℕ} (hp : ¬p.Prime) (v : ℝ) : primeTerm v p = 0 := by
  simp [primeTerm, archivedGaussianVaughanPrimeCoefficients, hp]

private theorem primeTerm_sum {v : ℝ} (hv : 0 < v) :
    Summable (primeTerm v) ∧
      (∑' p : ℕ, primeTerm v p) = (archivedGaussianVaughanCompletedPrimeKernel v).re := by
  obtain ⟨D, _, hK⟩ := archivedGaussianVaughanConvolvedKernel_powerBound (s := 2) (by norm_num)
  have hNorm (u : ℝ) (hu : 0 < u) :
      ‖(archivedGaussianVaughanConvolvedKernel u : ℂ)‖ ≤ D * u ^ (-(2 : ℝ)) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hK u hu
  have h := (dirichletKernelSum_summable hv hNorm
    (archivedGaussianVaughanPrime_summable (z := ((2 : ℝ) : ℂ)) (by norm_num))).of_norm
  constructor
  · change Summable (fun p => (archivedGaussianVaughanPrimeCoefficients p).re *
        archivedGaussianVaughanConvolvedKernel (p * v))
    simpa only [Complex.reCLM_apply, Complex.mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero] using Complex.reCLM.summable h
  · rw [archivedGaussianVaughanCompletedPrimeKernel_eq hv, Complex.re_tsum h]
    simp only [primeTerm, Complex.mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

private theorem split_at_prime_cutoff (W : ℝ → ℝ) {V q v : ℝ} (hV : 0 < V) (hv : 0 < v)
    (hW : ∀ u ≥ 2, W u = 0) :
    -(∑ p ∈ (primeRange V).filter (fun p : ℕ => p.Prime ∧ q < (p : ℝ)),
        (archivedGaussianMangoldt p).re * W (p / V) *
          archivedGaussianVaughanConvolvedKernel (p * v)) =
      (∑' p : ℕ, primeTerm v p * (1 - W (p / V))) -
        (archivedGaussianVaughanCompletedPrimeKernel v).re +
        ∑ p ∈ (primeRange V).filter (fun p : ℕ => (p : ℝ) ≤ q), primeTerm v p * W (p / V) := by
  let short (p : ℕ) := primeTerm v p * W (p / V)
  have hf (p : ℕ) (hp : p ∉ primeRange V) : short p = 0 := by
    have hn : ¬ p ≤ Nat.floor (2 * V) := by
      simpa only [primeRange, mem_range, Nat.lt_succ_iff] using hp
    have hr : 2 * V < (p : ℝ) :=
      lt_of_not_ge fun h => hn ((Nat.le_floor_iff (by positivity)).2 h)
    have hs : 2 ≤ (p : ℝ) / V := (le_div_iff₀ hV).2 hr.le
    simp only [short, hW _ hs, mul_zero]
  obtain ⟨hS, hEq⟩ := primeTerm_sum hv
  have hFin : Summable short := summable_of_ne_finset_zero hf
  have hFull : (∑' p : ℕ, primeTerm v p * (1 - W (p / V))) =
        (archivedGaussianVaughanCompletedPrimeKernel v).re -
          ∑ p ∈ primeRange V, short p := by
    calc
      _ = ∑' p : ℕ, (primeTerm v p - short p) := by
        simp only [short, mul_sub, mul_one]
      _ = _ := by rw [hS.tsum_sub hFin, hEq, tsum_eq_sum hf]
  have hSplit :
      (∑ p ∈ (primeRange V).filter (fun p : ℕ => q < (p : ℝ)), short p) +
        (∑ p ∈ (primeRange V).filter (fun p : ℕ => (p : ℝ) ≤ q), short p) =
      ∑ p ∈ primeRange V, short p := by
    simpa only [not_lt] using
      sum_filter_add_sum_filter_not (primeRange V) (fun p : ℕ => q < (p : ℝ)) short
  have hPrime :
      (∑ p ∈ (primeRange V).filter (fun p : ℕ => p.Prime ∧ q < (p : ℝ)),
        (archivedGaussianMangoldt p).re * W (p / V) *
          archivedGaussianVaughanConvolvedKernel (p * v)) =
        ∑ p ∈ (primeRange V).filter (fun p : ℕ => q < (p : ℝ)), short p := by
    calc
      _ = ∑ p ∈ (primeRange V).filter (fun p : ℕ => p.Prime ∧ q < (p : ℝ)), short p := by
        apply sum_congr rfl
        intro p hp
        rw [show short p = primeTerm v p * W (p / V) from rfl,
          primeTerm_eq (mem_filter.mp hp).2.1]
        ring
      _ = _ := by
        apply sum_subset
        · intro p hp
          exact mem_filter.mpr ⟨(mem_filter.mp hp).1, (mem_filter.mp hp).2.2⟩
        · intro p hp hnot
          have hnp : ¬p.Prime := fun h =>
            hnot (mem_filter.mpr ⟨(mem_filter.mp hp).1, h, (mem_filter.mp hp).2⟩)
          simp only [short, primeTerm_zero hnp, zero_mul]
  rw [hFull, hPrime]
  change _ = _ + ∑ p ∈ (primeRange V).filter (fun p : ℕ => (p : ℝ) ≤ q), short p
  linarith

private def cofactorSum (X : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 (Nat.floor ((Real.log X) ^ (8 / 3 : ℝ))),
    (archivedGaussianMoebiusCoefficients m).re * f (m / X)

def archivedGaussianVaughanUpperPrimeSum (W : ℝ → ℝ) (X : ℝ) : ℝ :=
  let V := X / (Real.log X) ^ (5 / 2 : ℝ)
  cofactorSum X fun v => ∑' p : ℕ, primeTerm v p * (1 - W (p / V))

def archivedGaussianVaughanCompletedPrimeSum (X : ℝ) : ℝ :=
  cofactorSum X fun v => (archivedGaussianVaughanCompletedPrimeKernel v).re

def archivedGaussianVaughanBelowWindowSum (W : ℝ → ℝ) (X : ℝ) : ℝ :=
  let V := X / (Real.log X) ^ (5 / 2 : ℝ)
  let q := X / (Real.log X) ^ (5 : ℕ)
  cofactorSum X fun v =>
    ∑ p ∈ (primeRange V).filter (fun p : ℕ => (p : ℝ) ≤ q), primeTerm v p * W (p / V)

/-- Exact replacement of the upper prime cutoff by the complementary
lower window, at the original cofactor and norm scale. -/
theorem archivedGaussianVaughanLowerSum_eq_complement (W : ℝ → ℝ) {X : ℝ}
    (hX : 1 < X) (hW : ∀ u ≥ 2, W u = 0) :
    archivedGaussianVaughanLowerSum W X = archivedGaussianVaughanUpperPrimeSum W X -
      archivedGaussianVaughanCompletedPrimeSum X + archivedGaussianVaughanBelowWindowSum W X := by
  have hX₀ := zero_lt_one.trans hX
  have hV : 0 < X / (Real.log X) ^ (5 / 2 : ℝ) :=
    div_pos hX₀ (Real.rpow_pos_of_pos (Real.log_pos hX) _)
  simp only [archivedGaussianVaughanLowerSum, if_pos hX, archivedGaussianVaughanUpperPrimeSum,
    archivedGaussianVaughanCompletedPrimeSum, archivedGaussianVaughanBelowWindowSum, cofactorSum]
  rw [← sum_neg_distrib, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  have hm₀ : 0 < (m : ℝ) := by exact_mod_cast (mem_Icc.mp hm).1
  have hv := div_pos hm₀ hX₀
  have h := split_at_prime_cutoff W (q := X / (Real.log X) ^ (5 : ℕ)) hV hv hW
  rw [← mul_sub, ← mul_add, ← h, ← mul_neg]
  congr 2
  apply sum_congr rfl
  intro p _
  rw [show (m : ℝ) * p / X = (p : ℝ) * (m / X) by ring]

/-- Once the upper sum approximates the full reading, the complementary
replacement spends only its completed-prime and below-window terms. -/
theorem archivedGaussianVaughan_complement_error {W : ℝ → ℝ}
    (hW : ∀ u ≥ 2, W u = 0) {X A B C : ℝ} (hX : 1 < X)
    (hA : |archivedGaussianVaughanSum X - archivedGaussianVaughanUpperPrimeSum W X| ≤ A)
    (hB : |archivedGaussianVaughanCompletedPrimeSum X| ≤ B)
    (hC : |archivedGaussianVaughanBelowWindowSum W X| ≤ C) :
    |archivedGaussianVaughanSum X - archivedGaussianVaughanLowerSum W X| ≤ A + B + C := by
  rw [archivedGaussianVaughanLowerSum_eq_complement W hX hW]
  rw [show archivedGaussianVaughanSum X - (archivedGaussianVaughanUpperPrimeSum W X -
      archivedGaussianVaughanCompletedPrimeSum X + archivedGaussianVaughanBelowWindowSum W X) =
      (archivedGaussianVaughanSum X - archivedGaussianVaughanUpperPrimeSum W X) +
        archivedGaussianVaughanCompletedPrimeSum X - archivedGaussianVaughanBelowWindowSum W X
      by ring]
  exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hA hB)) hC)

#check archivedGaussianVaughanLowerSum_eq_complement
#print axioms archivedGaussianVaughanLowerSum_eq_complement
#print axioms archivedGaussianVaughan_complement_error

end
end AlpogeSuperZeta
