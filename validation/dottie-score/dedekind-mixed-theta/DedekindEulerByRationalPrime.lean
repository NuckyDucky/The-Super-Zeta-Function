import DedekindRationalPrimeFibers
import DedekindZetaZeroFree.LFunctions.Dedekind.PrimeIdealEulerProduct

namespace FieldTarget

set_option autoImplicit false

open Complex Ideal NumberField
open DedekindZetaZeroFree.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

private theorem primeIdealFactor_in_fiber (s : ℂ) (p : Nat.Primes) (P : RationalPrimeFiber K p) :
    primeIdealFactor K (rationalPrimeFiberEquiv K ⟨p, P⟩) s =
      (1 - ((p.val : ℂ) ^ (-s)) ^ (P.val.inertiaDeg ℤ))⁻¹ := by
  let _ : Fact p.val.Prime := ⟨p.property⟩
  let Q : Ideal ℤ := span {(p.val : ℤ)}
  let _ : Q.IsMaximal := Int.ideal_span_isMaximal_of_prime p.val
  have hQ : Q ≠ ⊥ := by simp [Q, p.property.ne_zero]
  have hP : P.val ∈ Q.primesOver (𝓞 K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hQ (𝓞 K)).1 P.property
  let _ : P.val.IsPrime := hP.1
  let _ : P.val.LiesOver Q := hP.2
  have hn : P.val.absNorm = p.val ^ (P.val.inertiaDeg ℤ) := (Ideal.pow_inertiaDeg p.val P.val).symm
  have hpw (n : ℕ) : (((p.val : ℂ) ^ n) ^ (-s)) = ((p.val : ℂ) ^ (-s)) ^ n := by
    simpa only [Real.rpow_natCast, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.cpow_nat_mul] using
      (Complex.cpow_mul_ofReal_nonneg (Nat.cast_nonneg (α := ℝ) p.val) (n : ℝ) (-s)).symm
  rw [primeIdealFactor, localFactor, inverseNormPower, primeIdealNorm, rationalPrimeFiberEquiv_asIdeal,
    hn, Nat.cast_pow, hpw]

/-- Group the convergent Dedekind Euler product by rational primes, keeping
the residue degree of each actual number-field prime ideal. -/
theorem dedekindZeta_eq_eulerProduct_rationalPrimes (s : ℂ) (hs : 1 < s.re) :
    NumberField.dedekindZeta K s = ∏' p : Nat.Primes,
      ∏ P ∈ IsDedekindDomain.primesOverFinset (span {(p.val : ℤ)}) (𝓞 K),
        (1 - ((p.val : ℂ) ^ (-s)) ^ (P.inertiaDeg ℤ))⁻¹ := by
  let g := fun x : Σ p : Nat.Primes, RationalPrimeFiber K p ↦
    primeIdealFactor K (rationalPrimeFiberEquiv K x) s
  have hZ := dedekindZeta_primeIdeal_eulerProduct_hasProd K hs
  have hg : Multipliable g := ((rationalPrimeFiberEquiv K).multipliable_iff).2 hZ.multipliable
  calc
    _ = ∏' P : IsDedekindDomain.HeightOneSpectrum (𝓞 K), primeIdealFactor K P s := hZ.tprod_eq.symm
    _ = ∏' x, g x := ((rationalPrimeFiberEquiv K).tprod_eq (fun P ↦ primeIdealFactor K P s)).symm
    _ = ∏' p : Nat.Primes, ∏' P : RationalPrimeFiber K p, g ⟨p, P⟩ :=
      Multipliable.tprod_sigma' (fun _ ↦ Multipliable.of_finite) hg
    _ = _ := by
      apply tprod_congr
      intro p
      simp_rw [g, primeIdealFactor_in_fiber K s p]
      rw [tprod_fintype]
      exact Finset.prod_coe_sort (IsDedekindDomain.primesOverFinset (span {(p.val : ℤ)}) (𝓞 K))
        (fun P : Ideal (𝓞 K) ↦ (1 - ((p.val : ℂ) ^ (-s)) ^ (P.inertiaDeg ℤ))⁻¹)

#check @dedekindZeta_eq_eulerProduct_rationalPrimes
#print axioms dedekindZeta_eq_eulerProduct_rationalPrimes

end FieldTarget
