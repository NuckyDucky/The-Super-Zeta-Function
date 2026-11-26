import GaussianVaughanWindow
import GaussianMoebiusCommonDivisor

/-! Read the retained Gaussian Vaughan coefficient at its unique large prime. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Finset QuarticModel
open scoped Classical

noncomputable section

private theorem inverse_isMultiplicative {R : Type*} [CommSemiring R]
    {A B : ArithmeticFunction R} (hB : B.IsMultiplicative) (hAB : A * B = 1) :
    A.IsMultiplicative := by
  have hAone : A 1 = 1 := by
    have h := congrArg (fun f : ArithmeticFunction R => f 1) hAB
    simpa only [mul_apply_one, hB.map_one, mul_one, one_one] using h
  let C : ArithmeticFunction R :=
    ⟨fun n => if n = 0 then 0 else n.factorization.prod (fun p j => A (p ^ j)), if_pos rfl⟩
  have hC : C.IsMultiplicative := by
    refine IsMultiplicative.iff_ne_zero.mpr ⟨by simp [C], ?_⟩
    intro m n hm hn hc
    simp only [C, coe_mk, if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn),
      Nat.factorization_mul hm hn]
    exact Finsupp.prod_add_index_of_disjoint (by simpa using hc.disjoint_primeFactors) _
  have hpow {p : ℕ} (hp : p.Prime) (j : ℕ) : C (p ^ j) = A (p ^ j) := by
    simp [C, hp.ne_zero, hp.factorization_pow,
      Finsupp.prod_single_index, hAone]
  have hCB : C * B = 1 := by
    apply (IsMultiplicative.eq_iff_eq_on_prime_powers _ (hC.mul hB) _
      isMultiplicative_one).mpr
    intro p j hp
    calc
      (C * B) (p ^ j) = (A * B) (p ^ j) := by
        rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
        apply sum_congr rfl
        intro uv huv
        have hd := Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal huv)
        obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp hd
        rw [hi, hpow hp]
      _ = _ := by rw [hAB]
  have hCA : C = A := by
    calc
      C = C * (B * A) := by rw [mul_comm B A, hAB, mul_one]
      _ = A := by rw [← mul_assoc, hCB, one_mul]
  exact hCA ▸ hC

/-- The coprime prime factor can be included in the actual norm coefficient. -/
theorem archivedGaussianMangoldt_marked_prime {m p : ℕ} (hp : p.Prime)
    (hmp : m.Coprime p) :
    archivedGaussianMoebiusCoefficients m * archivedGaussianMangoldt p =
      -(archivedGaussianMoebiusCoefficients (m * p)) * Complex.log (p : ℂ) := by
  have hA := inverse_isMultiplicative signedIdealCoefficients_multiplicative
    archivedGaussianMoebius_mul_signed
  have hprime : archivedGaussianMoebiusCoefficients p =
      -(archivedGaussianPrimeWeight p : ℂ) := by
    simpa using archivedGaussianMoebius_ratio_prime_power hp 1
  have hL : archivedGaussianMangoldt p =
      (archivedGaussianPrimeWeight p : ℂ) * Complex.log (p : ℂ) := by
    simp only [archivedGaussianMangoldt, coe_mk, vonMangoldt_apply_prime hp, Complex.natCast_log]
  rw [hL, hA.map_mul_of_coprime hmp, hprime]
  ring

/-- A prime divisor above the square root is simple and is the largest prime
factor of the norm. -/
theorem gaussianLargePrime_address {n p : ℕ} (hp : p ∈ n.primeFactors)
    (hlarge : n < p ^ 2) :
    n / p < p ∧ (n / p).Coprime p ∧ ∀ q ∈ n.primeFactors, q ≠ p → q < p := by
  obtain ⟨hprime, hdiv, hn⟩ := Nat.mem_primeFactors.mp hp
  have he := Nat.div_mul_cancel hdiv
  have hm : n / p < p := by
    by_contra! h
    apply (not_le_of_gt hlarge)
    simpa only [he, pow_two] using Nat.mul_le_mul_right p h
  have hmpos : 0 < n / p := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at he
    exact hn he.symm
  refine ⟨hm, (hprime.coprime_iff_not_dvd.mpr ?_).symm, ?_⟩
  · exact fun h => (not_le_of_gt hm) (Nat.le_of_dvd hmpos h)
  · intro q hq hne
    obtain ⟨hqprime, hqdiv, _⟩ := Nat.mem_primeFactors.mp hq
    rw [← he] at hqdiv
    rcases hqprime.dvd_mul.mp hqdiv with h | h
    · exact (Nat.le_of_dvd hmpos h).trans_lt hm
    · exact (hne ((Nat.prime_dvd_prime_iff_eq hqprime hprime).mp h)).elim

private theorem norm_lt_largePrime_sq {V : ℝ} {n p : ℕ} (hV : 0 ≤ V)
    (hnV : (n : ℝ) ≤ V ^ 2) (hpV : V < (p : ℝ)) : n < p ^ 2 := by
  have hsum : 0 < (p : ℝ) + V := by linarith
  have hsq : V ^ 2 < (p : ℝ) ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hpV) hsum]
  exact_mod_cast hnV.trans_lt hsq

theorem gaussianLargePrime_marks_card_le_one {n : ℕ} {V : ℝ} (hV : 0 ≤ V)
    (hnV : (n : ℝ) ≤ V ^ 2) :
    (n.primeFactors.filter (fun p : ℕ => V < (p : ℝ))).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp, hpV⟩ := mem_filter.mp hp
  obtain ⟨hq, hqV⟩ := mem_filter.mp hq
  by_contra hne
  have hqp := (gaussianLargePrime_address hp (norm_lt_largePrime_sq hV hnV hpV)).2.2 q hq
    (fun h => hne h.symm)
  have hpq := (gaussianLargePrime_address hq (norm_lt_largePrime_sq hV hnV hqV)).2.2 p hp hne
  exact (lt_asymm hqp) hpq

/-- Regroup the retained sum by product. The weight can retain both original
cutoffs and any kernel evaluated at the same product. -/
theorem archivedGaussianLargePrime_reindex (n : ℕ) (V : ℝ)
    (W : ℕ → ℕ → ℂ) (hV : 0 ≤ V) (hnV : (n : ℝ) ≤ V ^ 2) :
    (∑ uv ∈ n.divisorsAntidiagonal, if uv.2.Prime ∧ V < (uv.2 : ℝ) then
      archivedGaussianMoebiusCoefficients uv.1 * archivedGaussianMangoldt uv.2 * W uv.1 uv.2
      else 0) =
    -(archivedGaussianMoebiusCoefficients n) *
      ∑ p ∈ n.primeFactors.filter (fun p : ℕ => V < (p : ℝ)),
        Complex.log (p : ℂ) * W (n / p) p := by
  rw [Nat.sum_divisorsAntidiagonal' (fun m p => if p.Prime ∧ V < (p : ℝ) then
    archivedGaussianMoebiusCoefficients m * archivedGaussianMangoldt p * W m p else 0)]
  simp only [Nat.primeFactors_eq_to_filter_divisors_prime, sum_filter, mul_sum, mul_ite, mul_zero]
  apply sum_congr rfl
  intro p hp
  by_cases hp' : p.Prime <;> by_cases hpV : V < (p : ℝ)
  · obtain ⟨hd, hn⟩ := Nat.mem_divisors.mp hp
    have hmark := hp'.mem_primeFactors hd hn
    have hc := (gaussianLargePrime_address hmark (norm_lt_largePrime_sq hV hnV hpV)).2.1
    simp only [if_pos hp', if_pos hpV, if_pos (And.intro hp' hpV)]
    rw [archivedGaussianMangoldt_marked_prime hp' hc, Nat.div_mul_cancel hd, mul_assoc]
  · simp [hpV]
  · simp [hp']
  · simp [hp']

/-- The asymmetric cut gives at most one marked prime and bounds its cofactor. -/
theorem gaussianLargePrime_asymmetric_addresses {X m p β η : ℝ} (hX : 1 ≤ X)
    (hm : 0 ≤ m) (hp : X ^ β < p) (hprod : m * p ≤ X ^ (1 + η))
    (hscale : 1 + η ≤ 2 * β) :
    m * p < p ^ 2 ∧ m ≤ X ^ (1 + η - β) := by
  have hx : 0 < X := zero_lt_one.trans_le hX
  have hv : 0 < X ^ β := Real.rpow_pos_of_pos hx _
  have hsq : X ^ (2 * β) = (X ^ β) ^ 2 := by
    rw [pow_two, ← Real.rpow_add hx]
    congr 1
    ring
  constructor
  · calc
      m * p ≤ X ^ (1 + η) := hprod
      _ ≤ X ^ (2 * β) := Real.rpow_le_rpow_of_exponent_le hX hscale
      _ = (X ^ β) ^ 2 := hsq
      _ < p ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hp) (show 0 < p + X ^ β by linarith)]
  · apply le_of_mul_le_mul_right _ hv
    calc
      m * X ^ β ≤ m * p := mul_le_mul_of_nonneg_left hp.le hm
      _ ≤ X ^ (1 + η) := hprod
      _ = X ^ (1 + η - β) * X ^ β := by
        rw [← Real.rpow_add hx]
        congr 1
        ring

/-- With α = η = τ = κ/4 and β = 1-κ/2, the short product has a strict
cutoff gap, and the cofactor and higher-power error have the stated exponents. -/
theorem gaussianLargePrime_cutoff_exponents {κ : ℝ} (hκ : 0 < κ) (hκ₂ : κ < 1 / 2) :
    let α := κ / 4
    let β := 1 - κ / 2
    let η := κ / 4
    let τ := κ / 4
    0 < α ∧ 0 < β ∧ 0 < τ ∧ τ < 1 ∧
      α + β = 1 - κ / 4 ∧ 1 + η ≤ 2 * β ∧
      1 + η - β = 3 * κ / 4 ∧ τ + α * (1 - τ + τ) = κ / 2 := by
  dsimp only
  refine ⟨by linarith, by linarith, by linarith, by linarith,
    by ring, by linarith, by ring, by ring⟩

/-- Apply the asymmetric exponents to the actual prime divisor of a norm. -/
theorem gaussianLargePrime_cofactor {X κ : ℝ} {n p : ℕ} (hX : 1 ≤ X)
    (hκ : 0 < κ) (hκ₂ : κ < 1 / 2)
    (hn : (n : ℝ) ≤ X ^ (1 + κ / 4)) (hp : p ∈ n.primeFactors)
    (hpX : X ^ (1 - κ / 2) < (p : ℝ)) :
    n < p ^ 2 ∧ ((n / p : ℕ) : ℝ) ≤ X ^ (3 * κ / 4) := by
  obtain ⟨_, _, _, _, _, hscale, hcofactor, _⟩ := gaussianLargePrime_cutoff_exponents hκ hκ₂
  have he : ((n / p : ℕ) : ℝ) * (p : ℝ) = (n : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨hsq, hm⟩ := gaussianLargePrime_asymmetric_addresses hX
    (show 0 ≤ ((n / p : ℕ) : ℝ) by positivity) hpX (by rwa [he]) hscale
  rw [he] at hsq
  exact ⟨by exact_mod_cast hsq, by simpa only [hcofactor] using hm⟩

/-- Both archived prime signs are retained in the signed coefficient at 65. -/
theorem archivedGaussianLargePrime_65 :
    archivedGaussianMoebiusCoefficients 65 = -4 ∧
      (65 : ℕ).primeFactors.filter (fun p => 10 < p) = {13} := by
  have hA := inverse_isMultiplicative signedIdealCoefficients_multiplicative
    archivedGaussianMoebius_mul_signed
  have h5 : archivedGaussianMoebiusCoefficients 5 = -2 := by
    simpa [archivedGaussianPrimeWeight_at_5_and_13.1] using
      archivedGaussianMoebius_ratio_prime_power (p := 5) (by decide) 1
  have h13 : archivedGaussianMoebiusCoefficients 13 = 2 := by
    simpa [archivedGaussianPrimeWeight_at_5_and_13.2] using
      archivedGaussianMoebius_ratio_prime_power (p := 13) (by decide) 1
  constructor
  · rw [show (65 : ℕ) = 5 * 13 by decide, hA.map_mul_of_coprime (by decide), h5, h13]
    norm_num
  · rw [show (65 : ℕ) = 5 * 13 by decide,
      Nat.primeFactors_mul (by decide) (by decide),
      (show Nat.Prime 5 by decide).primeFactors,
      (show Nat.Prime 13 by decide).primeFactors]
    decide +kernel

#print axioms archivedGaussianMangoldt_marked_prime
#print axioms gaussianLargePrime_address
#print axioms gaussianLargePrime_marks_card_le_one
#print axioms archivedGaussianLargePrime_reindex
#print axioms gaussianLargePrime_asymmetric_addresses
#print axioms gaussianLargePrime_cutoff_exponents
#print axioms gaussianLargePrime_cofactor
#print axioms archivedGaussianLargePrime_65

end
end AlpogeSuperZeta
