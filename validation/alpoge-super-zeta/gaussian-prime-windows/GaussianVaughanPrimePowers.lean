import GaussianVaughanConvolvedKernel
import Mathlib.Data.Nat.Factorization.PrimePow

/-! Separate the prime squares from the absolutely convergent higher powers
in the Mellin transform of the actual Gaussian prime reading. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Set
open scoped Classical

noncomputable section

/-- Restrict an arithmetic function to prime powers of exponent at least k. -/
def primePowerTail (k : ℕ) (a : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if IsPrimePow n ∧ k ≤ n.factorization n.minFac then a n else 0, by simp⟩

theorem primePowerTail_at_pow (k : ℕ) (a : ArithmeticFunction ℂ)
    {p j : ℕ} (hp : p.Prime) (hj : 0 < j) :
    primePowerTail k a (p ^ j) = if k ≤ j then a (p ^ j) else 0 := by
  have hpow : IsPrimePow (p ^ j) := (isPrimePow_nat_iff _).mpr ⟨p, j, hp, hj, rfl⟩
  simp [primePowerTail, hpow, hp.pow_minFac hj.ne', hp.factorization_pow,
    Finsupp.single_eq_same]

/-- The sum of log p divided by p to a real exponent converges past one. -/
private theorem primeLogPower_summable {u : ℝ} (hu : 1 < u) :
    Summable (fun p : Nat.Primes => Real.log (p : ℝ) * (p : ℝ) ^ (-u)) := by
  have h := (LSeriesSummable_vonMangoldt (s := (u : ℂ)) (by simpa using hu)).norm
  refine (h.comp_injective
    (show Function.Injective (fun p : Nat.Primes => p.val) from Subtype.val_injective)).congr ?_
  intro p
  change ‖LSeries.term (fun n : ℕ => (vonMangoldt n : ℂ)) (u : ℂ) p.val‖ = _
  rw [LSeries.norm_term_eq, if_neg p.prop.ne_zero, ofReal_re, norm_real, Real.norm_eq_abs,
    abs_of_nonneg vonMangoldt_nonneg, vonMangoldt_apply_prime p.prop,
    Real.rpow_neg (by positivity : (0 : ℝ) ≤ p.val), div_eq_mul_inv]

set_option maxHeartbeats 900000 in
/-- Absolute convergence holds to the right of 1/k for a Mangoldt-bounded
sequence restricted to powers of exponent at least k. -/
theorem primePowerTail_summable (k : ℕ) (a : ArithmeticFunction ℂ) {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ n, ‖a n‖ ≤ C * vonMangoldt n) {z : ℂ} (hz : 0 < z.re)
    (hkz : 1 < (k : ℝ) * z.re) : LSeriesSummable (primePowerTail k a) z := by
  have hk : 0 < k := by
    by_contra! h
    norm_num [Nat.eq_zero_of_le_zero h] at hkz
  let r := (2 : ℝ) ^ (-z.re)
  have hr₀ : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr₁ : r < 1 := by
    dsimp only [r]
    rw [← Real.rpow_zero (2 : ℝ)]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (neg_lt_zero.mpr hz)
  let b (p : Nat.Primes) := C * (Real.log (p : ℝ) * (p : ℝ) ^ (-((k : ℝ) * z.re)))
  have hb : Summable b := (primeLogPower_summable hkz).mul_left C
  have hb₀ (p : Nat.Primes) : 0 ≤ b p := by
    exact mul_nonneg hC (mul_nonneg (Real.log_natCast_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  let f (q : Nat.Primes × ℕ) := ‖LSeries.term (primePowerTail k a) z ((q.1 : ℕ) ^ (q.2 + 1))‖
  let shift (q : Nat.Primes × ℕ) : Nat.Primes × ℕ := (q.1, q.2 + (k - 1))
  have hshift : Function.Injective shift :=
    Function.Injective.prodMap (fun _ _ h => h) (add_left_injective _)
  have hmajor : Summable (fun q : Nat.Primes × ℕ => b q.1 * r ^ q.2) :=
    hb.mul_of_nonneg (summable_geometric_of_lt_one hr₀ hr₁) hb₀ (fun _ => pow_nonneg hr₀ _)
  have hshiftSum : Summable (f ∘ shift) := by
    apply hmajor.of_nonneg_of_le (fun _ => norm_nonneg _)
    rintro ⟨p, j⟩
    have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr p.prop.pos
    have hp₂ : 2 ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
    have hj : 0 < k + j := by omega
    have hEq : j + (k - 1) + 1 = k + j := by omega
    change ‖LSeries.term (primePowerTail k a) z (p.val ^ (j + (k - 1) + 1))‖ ≤ _
    rw [hEq, LSeries.norm_term_eq, if_neg (pow_ne_zero _ p.prop.ne_zero),
      primePowerTail_at_pow k a p.prop hj, if_pos (by omega : k ≤ k + j)]
    have hpow : (((p.val ^ (k + j) : ℕ) : ℝ) ^ z.re)⁻¹ =
        (p : ℝ) ^ (-((k : ℝ) * z.re)) * ((p : ℝ) ^ (-z.re)) ^ j := by
      rw [← Real.rpow_neg (by positivity), Nat.cast_pow, pow_add,
        Real.mul_rpow (pow_nonneg hp₀.le _) (pow_nonneg hp₀.le _),
        ← Real.rpow_natCast_mul hp₀.le k, ← Real.rpow_pow_comm hp₀.le]
      rw [show (k : ℝ) * (-z.re) = -((k : ℝ) * z.re) by ring]
    have hΛ := vonMangoldt_apply_pow (n := p.val) hj.ne'
    have hr : (p : ℝ) ^ (-z.re) ≤ r :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp₂ (neg_nonpos.mpr hz.le)
    rw [div_eq_mul_inv, hpow]
    calc
      _ ≤ (C * Real.log (p : ℝ)) *
          ((p : ℝ) ^ (-((k : ℝ) * z.re)) * ((p : ℝ) ^ (-z.re)) ^ j) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [hΛ, vonMangoldt_apply_prime p.prop] using ha (p.val ^ (k + j))
      _ = b p * ((p : ℝ) ^ (-z.re)) ^ j := by unfold b; ring
      _ ≤ b p * r ^ j := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.rpow_nonneg hp₀.le _) hr j) (hb₀ p)
  have hf : Summable f := by
    apply (hshift.summable_iff (f := f) ?_).mp hshiftSum
    rintro ⟨p, j⟩ hout
    have hj : j + 1 < k := by
      by_contra! hn
      apply hout
      refine ⟨(p, j - (k - 1)), ?_⟩
      have hh : j - (k - 1) + (k - 1) = j := by omega
      simp only [shift, hh]
    have hnzero : primePowerTail k a (p.val ^ (j + 1)) = 0 := by
      rw [primePowerTail_at_pow k a p.prop (Nat.succ_pos _), if_neg (not_le.mpr hj)]
    simp [f, LSeries.term_def, hnzero]
  let g (n : ℕ) := ‖LSeries.term (primePowerTail k a) z n‖
  have hg : Summable (fun n : {n : ℕ // IsPrimePow n} => g n.val) := by
    apply (Nat.Primes.prodNatEquiv.summable_iff).mp
    exact hf
  rw [LSeriesSummable, ← summable_norm_iff]
  refine ((summable_subtype_iff_indicator (s := {n : ℕ | IsPrimePow n}) (f := g)).mp hg).congr
    (fun n => Set.indicator_apply_eq_self.mpr fun hn => ?_)
  change ¬IsPrimePow n at hn
  have ha₀ : primePowerTail k a n = 0 := by simp [primePowerTail, hn]
  simp [g, LSeries.term_def, ha₀]

theorem archivedGaussianMangoldt_norm_le (n : ℕ) :
    ‖archivedGaussianMangoldt n‖ ≤ 2 * vonMangoldt n := by
  simp only [archivedGaussianMangoldt, ArithmeticFunction.coe_mk, norm_mul, norm_real,
    Real.norm_eq_abs, abs_of_nonneg vonMangoldt_nonneg]
  exact mul_le_mul_of_nonneg_right (archivedGaussianPrimeWeight_abs_le_two n) vonMangoldt_nonneg

def archivedGaussianVaughanSquareCoefficients : ArithmeticFunction ℂ :=
  ⟨fun n => if IsPrimePow n ∧ n.factorization n.minFac = 2 then archivedGaussianMangoldt n else 0,
    by simp⟩

theorem archivedGaussianVaughanHigher_eq_square_add_tail :
    archivedGaussianVaughanHigherCoefficients =
      archivedGaussianVaughanSquareCoefficients + primePowerTail 3 archivedGaussianMangoldt := by
  ext n
  change archivedGaussianMangoldt n - (if n.Prime then archivedGaussianMangoldt n else 0) =
    (if IsPrimePow n ∧ n.factorization n.minFac = 2 then archivedGaussianMangoldt n else 0) +
      (if IsPrimePow n ∧ 3 ≤ n.factorization n.minFac then archivedGaussianMangoldt n else 0)
  by_cases hpow : IsPrimePow n
  · obtain ⟨p, j, hp, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hpow
    rw [hp.pow_minFac hj.ne', hp.factorization_pow, Finsupp.single_eq_same]
    rcases eq_or_lt_of_le (show 1 ≤ j by omega) with hj₁ | hj₁
    · subst j
      simp [hp]
    have hnp := Nat.Prime.not_prime_pow' (x := p) (by omega : j ≠ 1)
    rcases eq_or_lt_of_le (show 2 ≤ j by omega) with hj₂ | hj₂
    · subst j
      simp [hnp, hpow]
    · have hj₂' : j ≠ 2 := by omega
      have hj₃ : 3 ≤ j := by omega
      simp [hpow, hnp, hj₂', hj₃]
  have hprime : ¬n.Prime := fun h => hpow h.isPrimePow
  simp [hpow, hprime, archivedGaussianMangoldt, vonMangoldt_eq_zero_iff.mpr hpow]

/-- The remaining Gaussian powers are holomorphic strictly right of 1/3. -/
theorem archivedGaussianVaughanTail_analyticAt {z : ℂ} (hz : 1 / 3 < z.re) :
    AnalyticAt ℂ (LSeries (primePowerTail 3 archivedGaussianMangoldt)) z := by
  have hconv : LSeries.abscissaOfAbsConv (primePowerTail 3 archivedGaussianMangoldt) ≤
        ((1 / 3 : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro u hu
    apply primePowerTail_summable 3 _ (by norm_num : (0 : ℝ) ≤ 2) archivedGaussianMangoldt_norm_le
    · rw [ofReal_re]
      linarith
    · rw [ofReal_re]
      norm_num
      linarith
  exact LSeries_analyticOnNhd _ z (hconv.trans_lt (EReal.coe_lt_coe_iff.mpr hz))

theorem archivedGaussianVaughanTail_uniform {σ : ℝ} (hσ : 1 / 3 < σ) :
    ∃ C ≥ 0, ∀ z : ℂ, σ ≤ z.re → ‖LSeries (primePowerTail 3 archivedGaussianMangoldt) z‖ ≤ C := by
  let a := primePowerTail 3 archivedGaussianMangoldt
  have hs : LSeriesSummable a (σ : ℂ) := by
    apply primePowerTail_summable 3 _ (by norm_num : (0 : ℝ) ≤ 2) archivedGaussianMangoldt_norm_le
    · rw [ofReal_re]
      linarith
    · rw [ofReal_re]
      norm_num
      linarith
  refine ⟨∑' n, ‖LSeries.term a (σ : ℂ) n‖, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro z hz
  have h : ∀ n, ‖LSeries.term a z n‖ ≤ ‖LSeries.term a (σ : ℂ) n‖ :=
    fun _ => LSeries.norm_term_le_of_re_le_re _ (by simpa using hz) _
  have hzNorm := hs.norm.of_nonneg_of_le (fun _ => norm_nonneg _) h
  exact (norm_tsum_le_tsum_norm hzNorm).trans (hzNorm.tsum_le_tsum h hs.norm)

#print axioms primePowerTail_at_pow
#print axioms primePowerTail_summable
#print axioms archivedGaussianMangoldt_norm_le
#print axioms archivedGaussianVaughanHigher_eq_square_add_tail
#print axioms archivedGaussianVaughanTail_analyticAt
#print axioms archivedGaussianVaughanTail_uniform

end
end AlpogeSuperZeta
