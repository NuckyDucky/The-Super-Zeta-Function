import QuarticEulerTower
import RelativeQuarticConductorPrimes
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity

/-! The unweighted Gaussian local factors are those of zeta times beta. -/

namespace QuarticModel

open UniqueFactorizationMonoid
open scoped Classical

private theorem primeAt_monoidPrime {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r^2 = -1) :
    Prime (gaussianPrimeAt r hr) := by
  have hm : (gaussianPrimeAt r hr).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (ZMod.ringHom_surjective (gaussianResidue r hr))
  apply Ideal.prime_of_isPrime _ hm.isPrime
  intro h
  have hp : (p : GaussianInt) ∈ gaussianPrimeAt r hr := by
    change gaussianResidue r hr (p : GaussianInt) = 0
    rw [map_natCast, ZMod.natCast_self]
  rw [h, Ideal.mem_bot] at hp
  exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.mp hp)

private theorem degree_from_absolute_norm {p : ℕ} [Fact p.Prime] {I : Ideal GaussianInt}
    (hI : I ∈ gaussianPrimesAbove p) (d : ℕ) (h : I.absNorm = p^d) :
    I.inertiaDeg ℤ = d := by
  have hi := (mem_gaussianPrimesAbove p).mp hI
  let : I.IsPrime := hi.1
  let : I.LiesOver (Ideal.span {(p : ℤ)}) := hi.2
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le
    ((Ideal.pow_inertiaDeg p I).trans h)

theorem primeAt_degree {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r^2 = -1)
    (h : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p) :
    (gaussianPrimeAt r hr).inertiaDeg ℤ = 1 := by
  apply degree_from_absolute_norm h
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, pow_one]
  exact (Nat.card_congr (gaussianPrimeAtResidueEquiv r hr).toEquiv).trans (by
    rw [Nat.card_eq_fintype_card, ZMod.card])

theorem split_gaussian_primes {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) (hn : (-r)^2 = -1) :
    gaussianPrimesAbove p = {gaussianPrimeAt r hr, gaussianPrimeAt (-r) hn} := by
  have he : gaussianPrimeAt r hr * gaussianPrimeAt (-r) hn = Ideal.span {(p : GaussianInt)} :=
    gaussianPrimeAt_product hp r hr
  have h₁ := primeAt_monoidPrime r hr
  have h₂ := primeAt_monoidPrime (-r) hn
  rw [gaussianPrimesAbove, ← he, normalizedFactors_mul h₁.ne_zero h₂.ne_zero,
    normalizedFactors_irreducible h₁.irreducible, normalizedFactors_irreducible h₂.irreducible,
    normalize_eq, normalize_eq, Multiset.toFinset_add, Multiset.toFinset_singleton,
    Multiset.toFinset_singleton, Finset.singleton_union]

theorem inert_gaussian_primes {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    gaussianPrimesAbove p = {Ideal.span {(p : GaussianInt)}} := by
  have h := GaussianInt.prime_of_nat_prime_of_mod_four_eq_three p hp
  have hh := Ideal.prime_of_isPrime (mt Ideal.span_singleton_eq_bot.mp h.ne_zero)
    ((Ideal.span_singleton_prime h.ne_zero).mpr h)
  rw [gaussianPrimesAbove, normalizedFactors_irreducible hh.irreducible, normalize_eq,
    Multiset.toFinset_singleton]

theorem eq_inert_gaussian_prime {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {I : Ideal GaussianInt} (hI : I ∈ gaussianPrimesAbove p) :
    I = Ideal.span {(p : GaussianInt)} := by
  simpa only [inert_gaussian_primes hp, Finset.mem_singleton] using hI

theorem gaussian_rational_prime_absNorm (p : ℕ) :
    (Ideal.span {(p : GaussianInt)} : Ideal GaussianInt).absNorm = p^2 := by
  have hdim : Module.finrank ℤ GaussianInt = 2 := by
    simpa using Module.finrank_eq_card_basis gaussianIntegralBasis
  rw [Ideal.absNorm_span_natCast, hdim]

theorem inert_gaussian_prime_degree {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    (Ideal.span {(p : GaussianInt)} : Ideal GaussianInt).inertiaDeg ℤ = 2 :=
  degree_from_absolute_norm (by rw [inert_gaussian_primes hp, Finset.mem_singleton]) 2
    (gaussian_rational_prime_absNorm p)

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem two_root : (1 : ZMod 2)^2 = -1 := by decide

private theorem dyadic_gaussian_primes :
    gaussianPrimesAbove 2 = {gaussianPrimeAt (1 : ZMod 2) two_root} := by
  have he : Ideal.span {(2 : GaussianInt)} = (gaussianPrimeAt (1 : ZMod 2) two_root)^2 := by
    rw [gaussianPrimeAt_eq_span 1 two_root ⟨1,1⟩ (by decide) (by decide), pow_two,
      Ideal.span_singleton_mul_span_singleton]
    let u : GaussianIntˣ := ⟨⟨0,1⟩,⟨0,-1⟩,by decide,by decide⟩
    exact Ideal.span_singleton_eq_span_singleton.mpr ⟨u, by decide⟩
  have hp := primeAt_monoidPrime (1 : ZMod 2) two_root
  unfold gaussianPrimesAbove
  change (normalizedFactors (Ideal.span {(2 : GaussianInt)})).toFinset = _
  rw [he, normalizedFactors_pow, normalizedFactors_irreducible hp.irreducible, normalize_eq]
  simp [two_nsmul]

theorem dyadic_gaussian_prime :
    gaussianPrimesAbove 2 = {Ideal.span {(⟨1,1⟩ : GaussianInt)}} := by
  rw [dyadic_gaussian_primes, gaussianPrimeAt_eq_span 1 two_root ⟨1,1⟩ (by decide) (by decide)]

theorem dyadic_gaussian_prime_degree :
    (Ideal.span {(⟨1,1⟩ : GaussianInt)} : Ideal GaussianInt).inertiaDeg ℤ = 1 := by
  rw [← gaussianPrimeAt_eq_span 1 two_root ⟨1,1⟩ (by decide) (by decide)]
  apply primeAt_degree
  rw [dyadic_gaussian_primes, Finset.mem_singleton]

theorem dyadic_gaussian_prime_two_mem {I : Ideal GaussianInt} (hI : I ∈ gaussianPrimesAbove 2) :
    (2 : GaussianInt) ∈ I := by
  have he : I = gaussianPrimeAt (1 : ZMod 2) two_root := by
    simpa only [dyadic_gaussian_primes, Finset.mem_singleton] using hI
  rw [he]
  change gaussianResidue (1 : ZMod 2) two_root 2 = 0
  rw [map_ofNat]
  decide

/-- The actual unweighted Gaussian denominator equals the rational
denominator of zeta times the mod-four Dirichlet factor. -/
theorem gaussian_base_euler_denominator (p : ℕ) [Fact p.Prime] :
    (∏ I ∈ gaussianPrimesAbove p, (1 - (PowerSeries.X : PowerSeries ℂ)^(I.inertiaDeg ℤ))) =
      (1-PowerSeries.X)*(1-(ZMod.χ₄ (p : ZMod 4) : PowerSeries ℂ)*PowerSeries.X) := by
  by_cases hp : p = 2
  · subst p
    have hI : gaussianPrimeAt (1 : ZMod 2) two_root ∈ gaussianPrimesAbove 2 := by
      rw [dyadic_gaussian_primes, Finset.mem_singleton]
    have hd := primeAt_degree 1 two_root hI
    have hχ : ZMod.χ₄ (2 : ZMod 4) = 0 := by decide
    rw [dyadic_gaussian_primes, Finset.prod_singleton, hd]
    change (1 - PowerSeries.X^1) = (1-PowerSeries.X)*(1-(ZMod.χ₄ (2 : ZMod 4) : PowerSeries ℂ)*PowerSeries.X)
    simp [hχ]
  · have hodd := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
    have hcases : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hcases with h₁ | h₃
    · obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p%4 ≠ 3)
      have hr' : r^2 = -1 := by rw [pow_two, ← hr]
      have hn : (-r)^2 = -1 := by simpa only [neg_sq] using hr'
      have hs := split_gaussian_primes hp r hr' hn
      have ha : gaussianPrimeAt r hr' ∈ gaussianPrimesAbove p := by simp [hs]
      have hb : gaussianPrimeAt (-r) hn ∈ gaussianPrimesAbove p := by simp [hs]
      have hne : gaussianPrimeAt r hr' ≠ gaussianPrimeAt (-r) hn :=
        gaussianPrimeAt_distinct hp r hr'
      rw [hs, Finset.prod_insert (by simpa only [Finset.mem_singleton] using hne),
        Finset.prod_singleton, primeAt_degree r hr' ha, primeAt_degree (-r) hn hb,
        ZMod.χ₄_nat_one_mod_four h₁]
      simp
    · have hs := inert_gaussian_primes h₃
      rw [hs, Finset.prod_singleton, inert_gaussian_prime_degree h₃,
        ZMod.χ₄_nat_three_mod_four h₃]
      push_cast
      ring

#print axioms gaussian_base_euler_denominator

end QuarticModel
