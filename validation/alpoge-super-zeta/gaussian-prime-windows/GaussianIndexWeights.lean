import GaussianIndexRamp
import GaussianInertPrimeWeights

/-! Weights of the two degrees of inert Gaussian primes in the
common-divisor index. The base coefficient keeps the finitely many
excluded primes exactly. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Finset QuarticModel
open scoped Classical

noncomputable section

def archivedGoodIndexPrime (p : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ p.Coprime 26509772707289

def archivedInertIndexWeight (p f : ℕ) : ℝ :=
  if archivedGoodIndexPrime p then
    (∑ I ∈ gaussianPrimesAbove p,
      if I.inertiaDeg ℤ = f ∧ archivedIdealCharacter I = -1 then (1 : ℝ) else 0) *
      ((f : ℝ) * Real.log p)
  else 0

def archivedIndexBaseWeight (p : ℕ) : ℝ :=
  if p.Prime then
    (if archivedGoodIndexPrime p then 1 + (ZMod.χ₄ (p : ZMod 4) : ℝ)
      else archivedGaussianPrimeWeight p) * Real.log p
  else 0

theorem archivedInertIndexWeight_nonneg (p f : ℕ) :
    0 ≤ archivedInertIndexWeight p f := by
  unfold archivedInertIndexWeight
  split_ifs with h
  · refine mul_nonneg (sum_nonneg fun I _ => ?_) (mul_nonneg (Nat.cast_nonneg _) ?_)
    · split_ifs <;> norm_num
    · exact Real.log_nonneg (by exact_mod_cast h.1.one_lt.le)
  · exact le_rfl

theorem archivedInertIndexWeight_eq_zero_of_not_prime {p : ℕ} (f : ℕ) (hp : ¬p.Prime) :
    archivedInertIndexWeight p f = 0 := by
  simp [archivedInertIndexWeight, archivedGoodIndexPrime, hp]

theorem gaussianIndexPrime_shape {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (gaussianPrimesAbove p).card ≤ 2 ∧
      ∀ I ∈ gaussianPrimesAbove p, I.inertiaDeg ℤ = 1 ∨ I.inertiaDeg ℤ = 2 := by
  by_cases h₃ : p % 4 = 3
  · refine ⟨by simp [inert_gaussian_primes h₃], fun I hi => ?_⟩
    have hI := eq_inert_gaussian_prime h₃ hi
    exact Or.inr (hI.symm ▸ inert_gaussian_prime_degree h₃)
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr h₃
  have hpos : r ^ 2 = -1 := by rw [pow_two, ← hr]
  have hneg : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hpos
  have hs := split_gaussian_primes hp r hpos hneg
  constructor
  · rw [hs]
    exact (card_insert_le _ _).trans (by simp)
  · intro I hi
    have hsplit := hi
    rw [hs, mem_insert, mem_singleton] at hsplit
    left
    rcases hsplit with rfl | rfl
    · exact primeAt_degree r hpos hi
    · exact primeAt_degree (-r) hneg hi

theorem archivedInertIndexWeight_le (p : Nat.Primes) (f : ℕ) :
    archivedInertIndexWeight p.val f ≤ 2 * ((f : ℝ) * Real.log p.val) := by
  have hl : 0 ≤ Real.log (p.val : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
  unfold archivedInertIndexWeight
  split_ifs with h
  · let : Fact p.val.Prime := ⟨p.property⟩
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hl)
    calc
      _ ≤ ∑ _I ∈ gaussianPrimesAbove p.val, (1 : ℝ) :=
        sum_le_sum (fun _I _ => by split_ifs <;> norm_num)
      _ ≤ 2 := by
        rw [sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast (gaussianIndexPrime_shape h.2.1).1
  · positivity

/-- At a good prime this subtracts the Gaussian base count. At an
excluded prime the original signed coefficient is kept in the base term. -/
theorem archivedIndexWeight_balance (p : ℕ) :
    2 * archivedInertIndexWeight p 1 - archivedIndexBaseWeight p =
      -(vonMangoldt p * (if p.Prime then archivedGaussianPrimeWeight p else 0)) := by
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    by_cases h : archivedGoodIndexPrime p
    · simp only [archivedInertIndexWeight, archivedIndexBaseWeight, if_pos hp, if_pos h,
        Nat.cast_one, one_mul, vonMangoldt_apply_prime hp]
      change 2 * (archivedInertDegreeOneWeight p * Real.log p) -
        (1 + (ZMod.χ₄ (p : ZMod 4) : ℝ)) * Real.log p =
        -(Real.log p * archivedGaussianPrimeWeight p)
      linear_combination Real.log (p : ℝ) *
        archivedInertDegreeOneWeight_of_good_prime h.2.1 h.2.2
    · simp [archivedInertIndexWeight, archivedIndexBaseWeight, hp, h,
        vonMangoldt_apply_prime hp, mul_comm]
  · simp [archivedInertIndexWeight_eq_zero_of_not_prime 1 hp, archivedIndexBaseWeight, hp]

theorem archivedInertIndexWeight_one_summable {θ : ℝ} (hθ : 0 < θ) :
    Summable (fun n : ℕ => archivedInertIndexWeight n 1 / (n : ℝ) ^ (1 + θ)) := by
  let b (n : ℕ) := archivedInertIndexWeight n 1 / (n : ℝ) ^ (1 + θ)
  let P : Set ℕ := {n | n.Prime}
  have hsub : Summable (fun p : Nat.Primes => b p.val) := by
    have hs := (summable_prime_log_div_rpow (s := 1 + θ) (by linarith)).mul_left (2 : ℝ)
    apply hs.of_nonneg_of_le (fun p =>
      div_nonneg (archivedInertIndexWeight_nonneg _ _) (Real.rpow_nonneg p.val.cast_nonneg _))
    intro p
    change archivedInertIndexWeight p.val 1 / (p.val : ℝ) ^ (1 + θ) ≤
      2 * (Real.log p.val / (p.val : ℝ) ^ (1 + θ))
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by simpa using archivedInertIndexWeight_le p 1)
      (Real.rpow_nonneg p.val.cast_nonneg _)
  have hi : Summable (P.indicator b) := summable_subtype_iff_indicator.mp hsub
  refine hi.congr fun n => ?_
  by_cases hn : n ∈ P
  · exact Set.indicator_of_mem hn _
  · simp [Set.indicator_of_notMem hn, b, archivedInertIndexWeight_eq_zero_of_not_prime 1 hn]

/-- The labels left by Möbius inversion have the index `(p^f+1)p^j`.
For the degree-one tail the exponent starts at one. -/
def archivedInertTailIndex (f k : ℕ) (pj : Nat.Primes × ℕ) : ℕ :=
  (pj.1.val ^ f + 1) * pj.1.val ^ (pj.2 + k)

theorem archivedInertTailIndex_pos (f k : ℕ) (pj : Nat.Primes × ℕ) :
    0 < archivedInertTailIndex f k pj :=
  Nat.mul_pos (Nat.succ_pos _) (pow_pos pj.1.property.pos _)

theorem archivedInertTail_summable (f k : ℕ) (hfk : f + k = 2) {θ : ℝ}
    (hθ : 1 / 2 < θ) :
    Summable (fun pj : Nat.Primes × ℕ =>
      archivedInertIndexWeight pj.1.val f / (archivedInertTailIndex f k pj : ℝ) ^ θ) := by
  let r := (2 : ℝ) ^ (-θ)
  let u (p : Nat.Primes) := (2 * (f : ℝ)) * (Real.log p.val / (p.val : ℝ) ^ (2 * θ))
  have hu := (summable_prime_log_div_rpow (s := 2 * θ) (by linarith)).mul_left (2 * (f : ℝ))
  have hu₀ (p : Nat.Primes) : 0 ≤ u p :=
    mul_nonneg (by positivity) (div_nonneg
      (Real.log_nonneg (by exact_mod_cast p.property.one_lt.le))
      (Real.rpow_nonneg p.val.cast_nonneg _))
  have hr₀ : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by
    simpa [r] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (show -θ < 0 by linarith)
  let m (pj : Nat.Primes × ℕ) := u pj.1 * r ^ pj.2
  have hm : Summable m := by
    have hg := summable_geometric_of_lt_one hr₀ hr₁
    apply (summable_prod_of_nonneg (f := m) fun pj => mul_nonneg (hu₀ pj.1) (pow_nonneg hr₀ _)).2
    refine ⟨fun p => hg.mul_left (u p), ?_⟩
    simpa only [m, hg.tsum_mul_left] using hu.mul_right (∑' j : ℕ, r ^ j)
  refine hm.of_nonneg_of_le (fun pj => div_nonneg (archivedInertIndexWeight_nonneg _ _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_
  rintro ⟨p, j⟩
  have hp : (0 : ℝ) < p.val := by exact_mod_cast p.property.pos
  have hN : p.val ^ (j + 2) ≤ archivedInertTailIndex f k (p, j) := by
    unfold archivedInertTailIndex
    rw [show j + 2 = f + (j + k) by omega, pow_add]
    exact Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hq : (p.val : ℝ) ^ (-θ) ≤ r := by
    have h2 : (2 : ℝ) ≤ p.val := by exact_mod_cast p.property.two_le
    rw [show r = (2 : ℝ) ^ (-θ) from rfl, Real.rpow_neg hp.le,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_anti₀ (by positivity) (Real.rpow_le_rpow (by norm_num) h2 (by linarith))
  calc
    _ ≤ archivedInertIndexWeight p.val f / ((p.val ^ (j + 2) : ℕ) : ℝ) ^ θ := by
      apply div_le_div_of_nonneg_left (archivedInertIndexWeight_nonneg _ _)
        (Real.rpow_pos_of_pos (Nat.cast_pos.mpr (pow_pos p.property.pos _)) _)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hN) (by linarith)
    _ ≤ 2 * ((f : ℝ) * Real.log p.val) / ((p.val ^ (j + 2) : ℕ) : ℝ) ^ θ :=
      div_le_div_of_nonneg_right (archivedInertIndexWeight_le p f) (by positivity)
    _ = u p * ((p.val : ℝ) ^ (-θ)) ^ j := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul hp.le,
        show ((j + 2 : ℕ) : ℝ) * θ = 2 * θ + θ * j by push_cast; ring,
        Real.rpow_add hp, Real.rpow_mul_natCast hp.le, Real.rpow_neg hp.le, inv_pow]
      dsimp only [u]
      ring
    _ ≤ m (p, j) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hq _) (hu₀ p)

#print axioms archivedIndexWeight_balance
#print axioms archivedInertIndexWeight_one_summable
#print axioms archivedInertTail_summable

end
end AlpogeSuperZeta
