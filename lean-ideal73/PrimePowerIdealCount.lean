import PrimeDecomposition73
import Mathlib.Data.Fintype.BigOperators

/-! Every ideal of norm 73^n in the quartic field, with its exact count. -/

noncomputable section
open scoped Classical
namespace PrimePowerIdealCount
open NumberField QuarticModel PrimeDecomposition73 UniqueFactorizationMonoid

private abbrev R := 𝓞 K
private abbrev Ip := Ideal.span {(73:ℤ)}
private instance : Fact (Nat.Prime 73) := ⟨by decide⟩
local instance : Ip.IsMaximal := Int.ideal_span_isMaximal_of_prime 73

private theorem primes : Prime P₉ ∧ Prime P₆₄ ∧ Prime P₃₄ := by
  have h : Ip ≠ ⊥ := by simp [Ip]
  exact ⟨Ideal.prime_of_mem_primesOver h ((prime_ideals _).mpr (Or.inl rfl)),
    Ideal.prime_of_mem_primesOver h ((prime_ideals _).mpr (Or.inr (Or.inl rfl))),
    Ideal.prime_of_mem_primesOver h ((prime_ideals _).mpr (Or.inr (Or.inr rfl)))⟩

private def product (t : ℕ × ℕ × ℕ) : Ideal R := P₉^t.1 * P₆₄^t.2.1 * P₃₄^t.2.2
private def degree (t : ℕ × ℕ × ℕ) : ℕ := t.1+t.2.1+2*t.2.2

private def exponents (I : Ideal R) : ℕ × ℕ × ℕ :=
  let s := normalizedFactors I
  (s.count P₉,s.count P₆₄,s.count P₃₄)

private def factorList (t : ℕ × ℕ × ℕ) : Multiset (Ideal R) :=
  Multiset.replicate t.1 P₉ + Multiset.replicate t.2.1 P₆₄ + Multiset.replicate t.2.2 P₃₄

private theorem factors_product (t : ℕ × ℕ × ℕ) : normalizedFactors (product t) = factorList t := by
  obtain ⟨ha,hb,hc⟩ := primes
  rw [product,normalizedFactors_mul (mul_ne_zero (pow_ne_zero _ ha.ne_zero)
    (pow_ne_zero _ hb.ne_zero)) (pow_ne_zero _ hc.ne_zero),
    normalizedFactors_mul (pow_ne_zero _ ha.ne_zero) (pow_ne_zero _ hb.ne_zero)]
  simp [normalizedFactors_pow,normalizedFactors_irreducible ha.irreducible,
    normalizedFactors_irreducible hb.irreducible,normalizedFactors_irreducible hc.irreducible,
    normalize_eq, Multiset.nsmul_singleton,factorList]

private theorem exponents_product (t : ℕ × ℕ × ℕ) : exponents (product t) = t := by
  obtain ⟨hab,hac,hbc⟩ := distinct
  rcases t with ⟨a,b,c⟩
  simp [exponents,factors_product,factorList,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc,
    Multiset.count_replicate]

private theorem norm_product (t : ℕ × ℕ × ℕ) : (product t).absNorm = 73^(degree t) := by
  obtain ⟨ha,hb,hc⟩ := norms
  simp only [product,degree,map_mul,map_pow,ha,hb,hc]
  rw [show (5329:ℕ) = 73^2 by decide,← pow_mul,← pow_add,← pow_add]

private theorem factor_above {n : ℕ} {I P : Ideal R} (hI : I.absNorm = 73^n)
    (hP : P ∈ normalizedFactors I) : P = P₉ ∨ P = P₆₄ ∨ P = P₃₄ := by
  have hp := Ideal.isPrime_of_prime (prime_of_normalized_factor _ hP)
  have hmem : (73 : R)^n ∈ I := by simpa [hI] using I.absNorm_mem
  have hinc : I ≤ P := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hP)
  have h73 := hp.mem_of_pow_mem n (hinc hmem)
  apply (prime_ideals _).mp
  refine ⟨hp,(Ideal.liesOver_iff_dvd_map hp.ne_top).mpr ?_⟩
  apply Ideal.dvd_iff_le.mpr
  simpa only [Ideal.map_span,Set.image_singleton,map_ofNat,Ideal.span_singleton_le_iff_mem] using h73

private theorem product_exponents {n : ℕ} {I : Ideal R} (hI : I.absNorm = 73^n) :
    product (exponents I) = I := by
  have h₀ : I ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hI
    exact (pow_ne_zero n (by decide : (73:ℕ) ≠ 0)) hI.symm
  have h : normalizedFactors I = factorList (exponents I) := by
    obtain ⟨hab,hac,hbc⟩ := distinct
    ext P
    by_cases ha : P=P₉
    · subst P; simp [factorList,exponents,Multiset.count_replicate,Ne.symm hab,Ne.symm hac]
    by_cases hb : P=P₆₄
    · subst P; simp [factorList,exponents,Multiset.count_replicate,hab,Ne.symm hbc]
    by_cases hc : P=P₃₄
    · subst P; simp [factorList,exponents,Multiset.count_replicate,hac,hbc]
    have hnone : P ∉ normalizedFactors I := by
      intro hf
      exact (factor_above hI hf).elim ha (fun e => e.elim hb hc)
    simp [factorList,exponents,Multiset.count_replicate,Ne.symm ha,Ne.symm hb,Ne.symm hc,hnone]
  simpa only [factorList,Multiset.prod_add,Multiset.prod_replicate,product,
    Ideal.prod_normalizedFactors_eq_self h₀] using (congrArg Multiset.prod h).symm

/-- Integral ideals of each norm 73^n in the actual ring of integers correspond
bijectively to nonnegative exponent triples a+b+2c=n. -/
def idealsEquivExponents (n : ℕ) :
    {I : Ideal (𝓞 K) // I.absNorm = 73^n} ≃
    {t : ℕ × ℕ × ℕ // t.1+t.2.1+2*t.2.2 = n} where
  toFun I := ⟨exponents I, Nat.pow_right_injective (by decide : 2 ≤ 73)
    ((norm_product _).symm.trans (by rw [product_exponents I.property, I.property]))⟩
  invFun t := ⟨product t, (norm_product _).trans (by rw [show degree t = n from t.property])⟩
  left_inv I := Subtype.ext (product_exponents I.property)
  right_inv t := Subtype.ext (exponents_product t)

private def choices (n : ℕ) := ∑ c ∈ Finset.range (n/2+1), (n-2*c+1)

private def exponentChoices (n : ℕ) :
    {t : ℕ × ℕ × ℕ // t.1 + t.2.1 + 2*t.2.2 = n} ≃
      (Σ c : Fin (n/2+1), Fin (n-2*c.val+1)) where
  toFun := fun ⟨⟨a,b,c⟩, h⟩ => ⟨⟨c, by dsimp at h; omega⟩, ⟨a, by dsimp at h ⊢; omega⟩⟩
  invFun := fun ⟨⟨c,hc⟩,⟨a,ha⟩⟩ => ⟨(a,n-2*c-a,c), by dsimp at *; omega⟩
  left_inv := by
    rintro ⟨⟨a,b,c⟩, h⟩
    change a+b+2*c = n at h
    apply Subtype.ext
    change (a,n-2*c-a,c) = (a,b,c)
    rw [show n-2*c-a = b by omega]
  right_inv := by rintro ⟨⟨c,hc⟩,⟨a,ha⟩⟩; rfl

private theorem count_as_sum (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I.absNorm = 73^n} = choices n := by
  rw [Nat.card_congr ((idealsEquivExponents n).trans (exponentChoices n)), Nat.card_eq_fintype_card,
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun c => n-2*c+1) _

private theorem choices_next (n : ℕ) : choices (n+2) = choices n+n+3 := by
  unfold choices
  rw [show (n+2)/2+1 = (n/2+1)+1 by omega, Finset.sum_range_succ']
  simp only [show n+2-2*0+1 = n+3 by omega]
  have h (c : ℕ) : n+2-2*(c+1)+1 = n-2*c+1 := by omega
  simp only [h]
  omega

/-- The actual mathlib ideal-counting coefficient at every even power of 73. -/
theorem count_even (r : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I.absNorm = 73^(2*r)} = (r+1)^2 := by
  rw [count_as_sum]
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 2*(r+1) = 2*r+2 by omega, choices_next, ih]
    ring

/-- The actual mathlib ideal-counting coefficient at every odd power of 73. -/
theorem count_odd (r : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I.absNorm = 73^(2*r+1)} = (r+1)*(r+2) := by
  rw [count_as_sum]
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 2*(r+1)+1 = (2*r+1)+2 by omega, choices_next, ih]
    ring

end PrimePowerIdealCount
