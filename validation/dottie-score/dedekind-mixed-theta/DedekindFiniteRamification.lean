import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Different

namespace FieldTarget

open scoped NumberField
open IsDedekindDomain

/-- The base primes with a ramified prime above them are the contractions of
the finitely many prime divisors of the different. -/
theorem exists_ramified_base_prime_finset (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ p, p ∈ S ↔ ∃ P : HeightOneSpectrum (𝓞 L),
        P.asIdeal.LiesOver p.asIdeal ∧ ¬ Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := by
  classical
  let : Algebra (FractionRing (𝓞 K)) (FractionRing (𝓞 L)) := FractionRing.liftAlgebra _ _
  let d := differentIdeal (𝓞 K) (𝓞 L)
  have hd : d ≠ ⊥ := differentIdeal_ne_bot
  have hfinite : {P : HeightOneSpectrum (𝓞 L) | P.asIdeal ∣ d}.Finite :=
    Ideal.finite_factors hd
  refine ⟨(hfinite.image (HeightOneSpectrum.under (𝓞 K))).toFinset, fun p ↦ ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨P, hdiv, hcontract⟩
    refine ⟨P, ⟨?_⟩, dvd_differentIdeal_iff.mp hdiv⟩
    exact (congrArg HeightOneSpectrum.asIdeal hcontract).symm
  · rintro ⟨P, hover, hram⟩
    exact ⟨P, dvd_differentIdeal_iff.mpr hram, HeightOneSpectrum.ext hover.over.symm⟩

#check @exists_ramified_base_prime_finset
#print axioms exists_ramified_base_prime_finset

end FieldTarget
