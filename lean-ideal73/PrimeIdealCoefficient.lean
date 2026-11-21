import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

/-! The prime-index coefficient of the ideal-counting Dirichlet series. -/

namespace QuarticCoefficient

open NumberField

/-- An ideal of prime index is exactly the kernel of one homomorphism to the prime field. -/
noncomputable def homEquivPrimeIndexIdeal (R : Type*) [CommRing R]
    (p : ℕ) [Fact p.Prime] :
    (R →+* ZMod p) ≃ {I : Ideal R // Nat.card (R ⧸ I) = p} := by
  let kernel (f : R →+* ZMod p) : {I : Ideal R // Nat.card (R ⧸ I) = p} :=
    ⟨RingHom.ker f, (Nat.card_congr (RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective f)).toEquiv).trans (Nat.card_zmod p)⟩
  apply Equiv.ofBijective kernel
  constructor
  · intro f g heq
    have hk : RingHom.ker f = RingHom.ker g := congrArg Subtype.val heq
    ext x
    obtain ⟨z, hz⟩ := ZMod.intCast_surjective (f x)
    have hx : x - (z : R) ∈ RingHom.ker f := by
      simpa [RingHom.mem_ker, sub_eq_zero] using hz.symm
    rw [hk] at hx
    have hg : g x = (z : ZMod p) := by simpa [RingHom.mem_ker, sub_eq_zero] using hx
    exact hz.symm.trans hg.symm
  · rintro ⟨I, hI⟩
    let : Finite (R ⧸ I) := Nat.finite_of_card_ne_zero (hI.trans_ne (Fact.out : p.Prime).ne_zero)
    let := Fintype.ofFinite (R ⧸ I)
    let e := ZMod.ringEquivOfPrime (R ⧸ I) (Fact.out : p.Prime)
      (Nat.card_eq_fintype_card.symm.trans hI)
    refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk I), Subtype.ext ?_⟩
    exact (RingHom.ker_comp_of_injective (Ideal.Quotient.mk I) e.symm.injective).trans
      (Ideal.mk_ker (I := I))

/-- The prime coefficient appearing in Mathlib's `NumberField.dedekindZeta`. -/
theorem primeCoefficient_eq_card_ringHom (K : Type*) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p} = Nat.card (𝓞 K →+* ZMod p) :=
  Nat.card_congr (homEquivPrimeIndexIdeal (𝓞 K) p).symm

#print axioms primeCoefficient_eq_card_ringHom

private def quotientModHomEquiv (R : Type*) [CommRing R] (p : ℕ) :
    (R →+* ZMod p) ≃ ((R ⧸ Ideal.span {(p : R)}) →+* ZMod p) where
  toFun f := Ideal.Quotient.lift _ f (by
    have hk : Ideal.span {(p : R)} ≤ RingHom.ker f :=
      (Ideal.span_singleton_le_iff_mem _).mpr (by simp [RingHom.mem_ker])
    exact fun _ h => hk h)
  invFun f := f.comp (Ideal.Quotient.mk _)
  left_inv _ := rfl
  right_inv _ := Ideal.Quotient.ringHom_ext rfl

private def precomposeEquiv {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (e : R ≃+* S) : (S →+* T) ≃ (R →+* T) where
  toFun f := f.comp e.toRingHom
  invFun f := f.comp e.symm.toRingHom
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp

private def ringHomEquivZModAlgHom {p : ℕ} (A : Type*) [CommRing A] [Algebra (ZMod p) A] :
    (A →+* ZMod p) ≃ (A →ₐ[ZMod p] ZMod p) where
  toFun f := {
    __ := f
    commutes' := fun x => DFunLike.congr_fun
      (Subsingleton.elim (f.comp (algebraMap (ZMod p) A)) (algebraMap (ZMod p) (ZMod p))) x }
  invFun f := f.toRingHom
  left_inv _ := rfl
  right_inv _ := rfl

open Polynomial

/-- At a prime away from the exponent of the order, the *actual* prime coefficient
of the field is the number of distinct roots of the reduced integral minimal polynomial. -/
theorem primeCoefficient_eq_card_roots {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] (θ : 𝓞 K) (hp : ¬ p ∣ RingOfIntegers.exponent θ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = p} =
      Nat.card {x : ZMod p // ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).eval x = 0} := by
  let f := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hf : f ≠ 0 := Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral)
  let e : AdjoinRoot f ≃+* (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) :=
    RingOfIntegers.ZModXQuotSpanEquivQuotSpan hp
  rw [primeCoefficient_eq_card_ringHom]
  apply Nat.card_congr
  exact (quotientModHomEquiv (𝓞 K) p).trans <| (precomposeEquiv e).trans <|
    (ringHomEquivZModAlgHom (AdjoinRoot f)).trans <|
    (AdjoinRoot.equiv (ZMod p) (ZMod p) f hf).trans <|
    Equiv.subtypeEquivRight (fun x => by simp [hf, f])

#print axioms primeCoefficient_eq_card_roots

/-- Eliminating `i` from `θ² = −5045155 + 1027708 i` gives this monic polynomial. -/
noncomputable def sqrtDeltaPolynomial : ℤ[X] := X ^ 4 + 10090310 * X ^ 2 + 26509772707289

private instance : Fact (Nat.Prime 73) := ⟨by decide⟩

/-- With the integral model and the good-prime condition supplied, the coefficient is
two. The roots here describe `θ = √δ` and thus differ from the original branch coordinates. -/
theorem primeCoefficient_73 {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K)
    (hpoly : minpoly ℤ θ = sqrtDeltaPolynomial) (hp : ¬ 73 ∣ RingOfIntegers.exponent θ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = 73} = 2 := by
  rw [primeCoefficient_eq_card_roots θ hp, hpoly]
  have h₁ : (10090310 : ZMod 73) = 31 := by decide
  have h₂ : (26509772707289 : ZMod 73) = 53 := by decide
  have hroots : ∀ x : ZMod 73, x^4 + 31*x^2 + 53 = 0 ↔ x = 9 ∨ x = 64 := by decide
  let e : {x : ZMod 73 // (sqrtDeltaPolynomial.map (Int.castRingHom (ZMod 73))).eval x = 0} ≃
      ↥({9, 64} : Finset (ZMod 73)) :=
    Equiv.subtypeEquivRight (fun x => by simpa [sqrtDeltaPolynomial, h₁, h₂] using hroots x)
  exact (Nat.card_congr e).trans (by rw [Nat.card_eq_fintype_card, Fintype.card_coe]; decide)

#print axioms primeCoefficient_73

end QuarticCoefficient
