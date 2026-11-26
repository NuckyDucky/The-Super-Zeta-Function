import GaussianFrobeniusIdentityMinor
import GaussianFrobeniusMinorPowers
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-! Combine the integer-node witness with the lower bound for every
minor at an unramified place of the identity reading. -/

namespace AlpogeSuperZeta

open Finset UniqueFactorizationMonoid

noncomputable section

/-- An element of valuation one at a nonzero maximal ideal has exact
valuation \(e\) after raising it to the power \(e\). -/
theorem pow_notMem_succ_of_notMem_sq {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsMaximal] {a : R} (ha : a ∈ P) (hUnramified : a ∉ P ^ 2)
    (e : ℕ) : a ^ e ∉ P ^ (e + 1) := by
  classical
  have ha₀ : a ≠ 0 := fun h => hUnramified (h ▸ (P ^ 2).zero_mem)
  have hP₀ : P ≠ ⊥ := fun h => ha₀ (by simpa [h] using ha)
  let Q := Ideal.span ({a} : Set R)
  have hQ₀ : Q ≠ ⊥ := by
    change Ideal.span ({a} : Set R) ≠ ⊥
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha₀
  have hCount : (normalizedFactors Q).count P = 1 := by
    apply Ideal.count_normalizedFactors_eq (p := P)
    · rw [pow_one]
      exact P.span_singleton_le_iff_mem.mpr ha
    · exact fun h => hUnramified ((P ^ 2).span_singleton_le_iff_mem.mp h)
  have hPrime := Ideal.prime_of_isPrime hP₀ (inferInstance : P.IsPrime)
  intro h
  have hLe : Q ^ e ≤ P ^ (e + 1) := by
    change Ideal.span ({a} : Set R) ^ e ≤ P ^ (e + 1)
    rw [Ideal.span_singleton_pow]
    exact (P ^ (e + 1)).span_singleton_le_iff_mem.mpr h
  have hBound := Ideal.count_le_of_ideal_ge hLe (pow_ne_zero e hQ₀) P
  rw [hPrime.irreducible.normalizedFactors_pow, normalize_eq, Multiset.count_replicate_self,
    normalizedFactors_pow, Multiset.count_nsmul, hCount, mul_one] at hBound
  exact (Nat.not_succ_le_self e) hBound

/-- At an unramified prime, the integer valuation of a positive
rational integer equals its valuation in the coefficient ring. -/
theorem natCast_notMem_pow_succ_of_factorization {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsMaximal] {p n : ℕ} [CharP (R ⧸ P) p] (hp : p.Prime)
    (hUnramified : (p : R) ∉ P ^ 2) (hn : n ≠ 0) :
    (n : R) ∉ P ^ (n.factorization p + 1) := by
  let e := n.factorization p
  have hFactor : p ^ e ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr (le_refl e)
  obtain ⟨u, hu⟩ := hFactor
  have hu₀ : ¬ p ∣ u := by
    rintro ⟨v, hv⟩
    have hDvd : p ^ (e + 1) ∣ n := ⟨v, by rw [hu, hv, pow_succ, mul_assoc]⟩
    exact (Nat.not_succ_le_self e) ((hp.pow_dvd_iff_le_factorization hn).mp hDvd)
  have huP : (u : R) ∉ P := by
    intro h
    have hZero := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [map_natCast] at hZero
    exact hu₀ ((CharP.cast_eq_zero_iff (R ⧸ P) p u).mp hZero)
  have hpP : (p : R) ∈ P := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_natCast]
    exact (CharP.cast_eq_zero_iff (R ⧸ P) p p).mpr (dvd_refl p)
  have hCast : (n : R) = (p : R) ^ e * (u : R) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using congrArg (fun m : ℕ => (m : R)) hu
  change (n : R) ∉ P ^ (e + 1)
  rw [hCast]
  intro h
  exact pow_notMem_succ_of_notMem_sq P hpP hUnramified e
    ((Ideal.IsMaximal.mem_pow_mul P h).resolve_right huP)

private theorem sqrtIdentity_factorialProduct_factorization {x : ℝ} (hx : 2 ≤ x)
    {p : ℕ} (hp : p.Prime) (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ)) :
    (∏ i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x),
      i.2.val.factorial).factorization p = frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p := by
  have hk : 1 ≤ gaussianSqrtTriangleScale x := by
    have hv := Real.one_le_rpow (show 1 ≤ x by linarith) (by norm_num : 0 ≤ (1 / 2 : ℝ))
    dsimp [gaussianSqrtTriangleScale]
    linarith
  have h := sqrtFrobeniusIdentityMinor_valuation hx hp hLow
  rw [frobeniusTriangleIdentityMinor_factorial hk] at h
  change (Int.natAbsHom (∏ i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x),
    ((-1 : ℤ) ^ i.1.val * (i.2.val.factorial : ℤ)))).factorization p = _ at h
  have hAbs (s r : ℕ) : Int.natAbsHom ((-1 : ℤ) ^ s * (r.factorial : ℤ)) = r.factorial := by
    rw [map_mul, map_pow]
    change ((-1 : ℤ).natAbs) ^ s * ((r.factorial : ℤ).natAbs) = _
    simp
  simpa only [map_prod, hAbs] using h

/-- The explicit factorial witness prevents the common identity ideal
from lying in the next prime power at an unramified prime. -/
theorem sqrtFrobeniusIdentityMinorIdeal_not_le_pow_succ {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsMaximal] {x : ℝ} (hx : 2 ≤ x) {p : ℕ}
    [CharP (R ⧸ P) p] (hp : p.Prime) (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hUnramified : (p : R) ∉ P ^ 2) :
    ¬ sqrtFrobeniusMinorIdeal x (RingHom.id R) ≤
      P ^ (frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p + 1) := by
  classical
  let Rows := FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)
  let n := ∏ i : Rows, i.2.val.factorial
  let sign : R := ∏ i : Rows, (-1 : R) ^ i.1.val
  let e := frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.factorial_ne_zero i.2.val)
  have hSign : IsUnit sign := IsUnit.prod_univ_iff.mpr (fun i => isUnit_neg_one.pow _)
  have hCount : n.factorization p = e := sqrtIdentity_factorialProduct_factorization hx hp hLow
  have hCast := natCast_notMem_pow_succ_of_factorization P hp hUnramified hn
  rw [hCount] at hCast
  intro h
  have hMem : sign * (n : R) ∈ P ^ (e + 1) := by
    have hMember := h (sqrtFrobeniusIdentityMinor_factorial_mem R hx)
    rw [Finset.prod_mul_distrib, ← Nat.cast_prod] at hMember
    exact hMember
  exact hCast ((Ideal.IsMaximal.mul_mem_pow P hMem).resolve_left (P.notMem_of_isUnit hSign))

/-- The common identity minor ideal has the indicated exponent at
every retained unramified prime with identity Frobenius. -/
theorem sqrtFrobeniusIdentityMinorIdeal_exactExponent {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsMaximal] {x : ℝ} (hx : 2 ≤ x) {p : ℕ}
    [CharP (R ⧸ P) p] (hp : p.Prime) (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hUnramified : (p : R) ∉ P ^ 2)
    (hFrob : ∀ a : R, Ideal.Quotient.mk P a = (Ideal.Quotient.mk P a) ^ p) :
    let e := frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p
    sqrtFrobeniusMinorIdeal x (RingHom.id R) ≤ P ^ e ∧
      ¬ sqrtFrobeniusMinorIdeal x (RingHom.id R) ≤ P ^ (e + 1) :=
  ⟨sqrtFrobeniusMinorIdeal_le_pow_of_frobenius P (RingHom.id R) hx hp hLow hFrob,
    sqrtFrobeniusIdentityMinorIdeal_not_le_pow_succ P hx hp hLow hUnramified⟩

/-- The same exact exponent stated as a count of normalized ideal factors. -/
theorem sqrtFrobeniusIdentityMinorIdeal_count {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsMaximal] {x : ℝ} (hx : 2 ≤ x) {p : ℕ}
    [CharP (R ⧸ P) p] (hp : p.Prime) (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hUnramified : (p : R) ∉ P ^ 2)
    (hFrob : ∀ a : R, Ideal.Quotient.mk P a = (Ideal.Quotient.mk P a) ^ p) :
    (normalizedFactors (sqrtFrobeniusMinorIdeal x (RingHom.id R))).count P =
      frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p := by
  classical
  obtain ⟨hLower, hUpper⟩ :=
    sqrtFrobeniusIdentityMinorIdeal_exactExponent P hx hp hLow hUnramified hFrob
  exact Ideal.count_normalizedFactors_eq hLower hUpper

#print axioms pow_notMem_succ_of_notMem_sq
#print axioms natCast_notMem_pow_succ_of_factorization
#print axioms sqrtFrobeniusIdentityMinorIdeal_not_le_pow_succ
#print axioms sqrtFrobeniusIdentityMinorIdeal_exactExponent
#print axioms sqrtFrobeniusIdentityMinorIdeal_count

end

end AlpogeSuperZeta
