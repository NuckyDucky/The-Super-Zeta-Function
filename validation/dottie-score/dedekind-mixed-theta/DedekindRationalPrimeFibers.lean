import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.Ideal.Int

namespace FieldTarget

set_option autoImplicit false

open Ideal IsDedekindDomain NumberField

private theorem primeSpan_ne_bot (p : Nat.Primes) : span ({(p.val : ℤ)} : Set ℤ) ≠ ⊥ := by
  simp [p.property.ne_zero]

private theorem primeSpan_isMaximal (p : Nat.Primes) : (span ({(p.val : ℤ)} : Set ℤ)).IsMaximal := by
  let _ : Fact p.val.Prime := ⟨p.property⟩
  exact Int.ideal_span_isMaximal_of_prime p.val

private theorem primeSpan_injective :
    Function.Injective (fun p : Nat.Primes ↦ span ({(p.val : ℤ)} : Set ℤ)) := by
  intro p q hpq
  apply Subtype.ext
  have h := Int.associated_iff_natAbs.mp (span_singleton_eq_span_singleton.mp hpq)
  simpa using h

private theorem exists_primeSpan (P : HeightOneSpectrum ℤ) :
    ∃ p : Nat.Primes, P.asIdeal = span ({(p.val : ℤ)} : Set ℤ) := by
  let g := Submodule.IsPrincipal.generator P.asIdeal
  have he : span ({g} : Set ℤ) = P.asIdeal := span_singleton_generator P.asIdeal
  have hg : g ≠ 0 := by
    intro h
    rw [h, span_singleton_eq_bot.mpr rfl] at he
    exact P.ne_bot he.symm
  have hp : Prime g := (span_singleton_prime hg).mp (he ▸ P.isPrime)
  exact ⟨⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hp⟩,
    he.symm.trans (span_singleton_eq_span_singleton.mpr (Int.associated_natAbs g))⟩

variable (K : Type*) [Field K] [NumberField K]

/-- Integral primes above the rational prime `p`, enumerated by the finite
fiber of contraction of ideals. -/
abbrev RationalPrimeFiber (p : Nat.Primes) := ↥(IsDedekindDomain.primesOverFinset
  (span ({(p.val : ℤ)} : Set ℤ)) (𝓞 K))

private def rationalPrimeFiberToHeightOne (x : Σ p : Nat.Primes, RationalPrimeFiber K p) :
    HeightOneSpectrum (𝓞 K) := by
  let _ := primeSpan_isMaximal x.1
  have hx := (IsDedekindDomain.mem_primesOverFinset_iff (primeSpan_ne_bot x.1) (𝓞 K)).1 x.2.property
  refine ⟨x.2.val, hx.1, ?_⟩
  intro hbot
  have he := hx.2.over
  rw [hbot, Ideal.under_bot] at he
  exact primeSpan_ne_bot x.1 he

/-- The nonzero prime ideals of a number field partition by the rational
prime below them. -/
noncomputable def rationalPrimeFiberEquiv :
    (Σ p : Nat.Primes, RationalPrimeFiber K p) ≃ HeightOneSpectrum (𝓞 K) := by
  apply Equiv.ofBijective (rationalPrimeFiberToHeightOne K)
  constructor
  · rintro ⟨p, I⟩ ⟨q, J⟩ h
    let _ := primeSpan_isMaximal p
    let _ := primeSpan_isMaximal q
    have hIJ : I.val = J.val := congrArg HeightOneSpectrum.asIdeal h
    have hI := ((IsDedekindDomain.mem_primesOverFinset_iff (primeSpan_ne_bot p) (𝓞 K)).1 I.property).2.over
    have hJ := ((IsDedekindDomain.mem_primesOverFinset_iff (primeSpan_ne_bot q) (𝓞 K)).1 J.property).2.over
    have hpq : p = q := primeSpan_injective (hI.trans ((congrArg (Ideal.under ℤ) hIJ).trans hJ.symm))
    subst q
    exact congrArg (Sigma.mk p) (Subtype.ext hIJ)
  · intro P
    obtain ⟨p, hp⟩ := exists_primeSpan (P.under ℤ)
    let _ := primeSpan_isMaximal p
    have hP := (IsDedekindDomain.mem_primesOverFinset_iff (primeSpan_ne_bot p) (𝓞 K)).2
      (show P.asIdeal ∈ (span ({(p.val : ℤ)} : Set ℤ)).primesOver (𝓞 K) from ⟨P.isPrime, ⟨hp.symm⟩⟩)
    exact ⟨⟨p, ⟨P.asIdeal, hP⟩⟩, by cases P; rfl⟩

@[simp] theorem rationalPrimeFiberEquiv_asIdeal (x : Σ p : Nat.Primes, RationalPrimeFiber K p) :
    (rationalPrimeFiberEquiv K x).asIdeal = x.2.val := rfl

#check @rationalPrimeFiberEquiv
#print axioms rationalPrimeFiberEquiv
#print axioms rationalPrimeFiberEquiv_asIdeal

end FieldTarget
