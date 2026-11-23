import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Inertia

/-! Count ideals at rational prime powers by assigning one exponent to
each distinct prime ideal above the rational prime. -/

namespace IdealPrimePower

open UniqueFactorizationMonoid
open scoped Classical

variable (R : Type*) [CommRing R] [IsDedekindDomain R]

noncomputable def primesAbove (p : ℕ) : Finset (Ideal R) :=
  (normalizedFactors (Ideal.span ({(p : R)} : Set R))).toFinset

abbrev PrimeAbove (p : ℕ) := ↥(primesAbove R p)

private theorem above_prime {p : ℕ} (P : PrimeAbove R p) : Prime P.val :=
  prime_of_normalized_factor _ (Multiset.mem_toFinset.mp P.property)

variable [CharZero R] [Module.Free ℤ R] [Module.Finite ℤ R]

omit [CharZero R] [Module.Free ℤ R] in
theorem primeAbove_inertiaDeg_pos {p : ℕ} (P : PrimeAbove R p) : 0 < P.val.inertiaDeg ℤ := by
  let : P.val.IsPrime := Ideal.isPrime_of_prime (above_prime R P)
  exact P.val.inertiaDeg_pos ℤ

private theorem above_norm {p : ℕ} [Fact p.Prime] (P : PrimeAbove R p) :
    P.val.absNorm = p ^ P.val.inertiaDeg ℤ := by
  let H : Ideal ℤ := Ideal.span {(p : ℤ)}
  let : H.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h0 : H ≠ ⊥ := by simp [H, (Fact.out : p.Prime).ne_zero]
  have hm : P.val ∈ H.primesOver R :=
    (Ideal.mem_primesOver_iff_mem_normalizedFactors R h0).mpr (by
      simpa only [H, Ideal.map_span, Set.image_singleton, map_natCast]
        using Multiset.mem_toFinset.mp P.property)
  let : P.val.LiesOver H := hm.2
  let : P.val.IsPrime := hm.1
  exact (Ideal.pow_inertiaDeg p P.val).symm

noncomputable def exponentDegree {p : ℕ} (f : PrimeAbove R p → ℕ) : ℕ :=
  ∑ P, P.val.inertiaDeg ℤ * f P

noncomputable def exponentProduct {p : ℕ} (f : PrimeAbove R p → ℕ) : Ideal R :=
  ∏ P, P.val ^ f P

private noncomputable def factorList {p : ℕ} (f : PrimeAbove R p → ℕ) : Multiset (Ideal R) :=
  ∑ P, Multiset.replicate (f P) P.val

private theorem norm_product {p : ℕ} [Fact p.Prime] (f : PrimeAbove R p → ℕ) :
    (exponentProduct R f).absNorm = p ^ exponentDegree R f := by
  simp only [exponentProduct, exponentDegree, map_prod, map_pow, above_norm, ← pow_mul]
  exact Finset.prod_pow_eq_pow_sum _ _ _

omit [Module.Free ℤ R] [Module.Finite ℤ R] in
private theorem factors_product {p : ℕ} (f : PrimeAbove R p → ℕ) :
    normalizedFactors (exponentProduct R f) = factorList R f := by
  unfold exponentProduct factorList
  have h (s : Finset (PrimeAbove R p)) :
      normalizedFactors (∏ P ∈ s, P.val ^ f P) = ∑ P ∈ s, Multiset.replicate (f P) P.val := by
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.sum_empty, normalizedFactors_one]
    | insert P s hs ih =>
      rw [Finset.prod_insert hs, Finset.sum_insert hs, normalizedFactors_mul
        (pow_ne_zero _ (above_prime R P).ne_zero)
        (Finset.prod_ne_zero_iff.mpr fun Q _ => pow_ne_zero _ (above_prime R Q).ne_zero), ih]
      simp [normalizedFactors_pow, normalizedFactors_irreducible (above_prime R P).irreducible,
        normalize_eq, Multiset.nsmul_singleton]
  exact h Finset.univ

private noncomputable def exponents (p : ℕ) (I : Ideal R) : PrimeAbove R p → ℕ :=
  fun P => (normalizedFactors I).count P.val

omit [Module.Free ℤ R] [Module.Finite ℤ R] in
private theorem exponents_product {p : ℕ} (f : PrimeAbove R p → ℕ) :
    exponents R p (exponentProduct R f) = f := by
  funext P
  unfold exponents
  rw [factors_product, factorList, Multiset.count_sum', Finset.sum_eq_single P]
  · simp
  · intro Q _ hQ
    have h : P.val ≠ Q.val := fun h => hQ (Subtype.ext h.symm)
    simp [Multiset.count_replicate, Ne.symm h]
  · simp

omit [Module.Finite ℤ R] in
private theorem factor_above {p n : ℕ} [Fact p.Prime] {I P : Ideal R}
    (hI : I.absNorm = p^n) (hP : P ∈ normalizedFactors I) : P ∈ primesAbove R p := by
  have hp := Ideal.isPrime_of_prime (prime_of_normalized_factor _ hP)
  have hmem : (p : R)^n ∈ I := by simpa only [hI, Nat.cast_pow] using I.absNorm_mem
  have hinc : I ≤ P := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP)
  have hpMem := hp.mem_of_pow_mem n (hinc hmem)
  let H : Ideal ℤ := Ideal.span {(p : ℤ)}
  let : H.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h0 : H ≠ ⊥ := by simp [H, (Fact.out : p.Prime).ne_zero]
  have hpMap : H.map (algebraMap ℤ R) ≤ P := by
    simp only [H, Ideal.map_span, Set.image_singleton, map_natCast]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpMem)
  have hL : P.LiesOver H := (Ideal.liesOver_iff_dvd_map hp.ne_top).mpr (Ideal.dvd_iff_le.mpr hpMap)
  apply Multiset.mem_toFinset.mpr
  simpa only [H, Ideal.map_span, Set.image_singleton, map_natCast] using
    (Ideal.mem_primesOver_iff_mem_normalizedFactors R h0).mp ⟨hp, hL⟩

omit [Module.Finite ℤ R] in
private theorem factors_exponents {p n : ℕ} [Fact p.Prime] {I : Ideal R}
    (hI : I.absNorm = p^n) : factorList R (exponents R p I) = normalizedFactors I := by
  ext P
  rw [factorList, Multiset.count_sum']
  by_cases hP : P ∈ primesAbove R p
  · let Q : PrimeAbove R p := ⟨P,hP⟩
    rw [Finset.sum_eq_single Q]
    · simp [Q, exponents]
    · intro R _ hR
      have h : P ≠ R.val := fun h => hR (Subtype.ext h.symm)
      simp [Multiset.count_replicate, Ne.symm h]
    · simp
  · have hno : P ∉ normalizedFactors I := fun h => hP (factor_above R hI h)
    rw [Multiset.count_eq_zero.mpr hno]
    apply Finset.sum_eq_zero
    intro R _
    have h : P ≠ R.val := fun h => hP (h ▸ R.property)
    simp [Multiset.count_replicate, Ne.symm h]

omit [Module.Finite ℤ R] in
private theorem product_exponents {p n : ℕ} [Fact p.Prime] {I : Ideal R}
    (hI : I.absNorm = p^n) : exponentProduct R (exponents R p I) = I := by
  have h0 : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hI
    exact (pow_ne_zero n (Fact.out : p.Prime).ne_zero) hI.symm
  have hprod : exponentProduct R (exponents R p I) ≠ ⊥ :=
    Finset.prod_ne_zero_iff.mpr fun P _ => pow_ne_zero _ (above_prime R P).ne_zero
  rw [← Ideal.prod_normalizedFactors_eq_self hprod, factors_product,
    factors_exponents R hI, Ideal.prod_normalizedFactors_eq_self h0]

/-- Integral ideals of norm `p^n` are in bijection with exponent choices of
weighted degree `n` on the distinct prime ideals above `p`. -/
noncomputable def primePowerIdealsEquivExponents (p : ℕ) [Fact p.Prime] (n : ℕ) :
    {I : Ideal R // I.absNorm = p^n} ≃
      {f : PrimeAbove R p → ℕ // exponentDegree R f = n} where
  toFun I := ⟨exponents R p I.val, Nat.pow_right_injective (Fact.out : p.Prime).two_le <|
    (norm_product R _).symm.trans (by rw [product_exponents R I.property, I.property])⟩
  invFun f := ⟨exponentProduct R f.val, (norm_product R _).trans (by rw [f.property])⟩
  left_inv I := Subtype.ext (product_exponents R I.property)
  right_inv f := Subtype.ext (exponents_product R f.val)

#print axioms primePowerIdealsEquivExponents

end IdealPrimePower
