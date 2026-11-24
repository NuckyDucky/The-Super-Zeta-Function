import QuarticEulerFactorization
import RelativeQuarticNormCharacter

/-! Compare the actual relative discriminant character with the archived
conductor character at every inert rational prime. -/

namespace QuarticModel

open FieldCoefficientTransfer
open scoped Classical

attribute [local instance] Ideal.Quotient.field

private theorem archivedGaussianSign_natCast (p : ℕ) :
    archivedGaussianSign (p : GaussianInt) = rationalNormSign p := by
  simp [archivedGaussianSign_eq_legendre, rationalNormSign]

private theorem half_square (p : ℕ) (hp : p % 2 = 1) :
    p^2 / 2 = (p+1)*(p/2) := by
  have h : (p : ℤ) = 2 * ((p/2 : ℕ) : ℤ) + 1 := by omega
  have he : p^2 = 2*((p+1)*(p/2))+1 := by
    exact_mod_cast (show (p : ℤ)^2 = 2*((p+1)*((p/2 : ℕ) : ℤ))+1 by nlinarith)
  omega

/-- At a rational prime inert in `ℤ[i]`, the Frobenius in the quadratic
residue field is complex conjugation on the two Gaussian coordinates. -/
private theorem inert_discriminant_norm (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    {F : Type*} [Field F] [CharP F p] (f : GaussianInt →+* F) :
    (f gaussianDiscriminant)^(p+1) = (26509772707289 : F) := by
  let : ExpChar F p := ExpChar.prime (Fact.out : p.Prime)
  let j := f (Zsqrtd.sqrtd : GaussianInt)
  have hj : j^2 = -1 := by
    dsimp only [j]
    rw [← map_pow, show (Zsqrtd.sqrtd : GaussianInt)^2 = -1 by decide, map_neg, map_one]
  have hj4 : j^4 = 1 := by
    rw [show j^4 = (j^2)^2 by ring, hj, neg_sq, one_pow]
  have hjp : j^p = -j := by
    calc
      j^p = j^(4*(p/4)+3) := congrArg (j ^ ·) (by omega)
      _ = -j := by
        rw [pow_add, pow_mul, hj4, one_pow, one_mul, show j^3 = j^2*j by ring, hj, neg_one_mul]
  have hd : gaussianDiscriminant = (-5045155 : GaussianInt) +
      (Zsqrtd.sqrtd : GaussianInt) * 1027708 := by decide
  have hx : f gaussianDiscriminant = (-5045155 : F) + j*1027708 := by
    rw [hd]
    change f (((-5045155 : ℤ) : GaussianInt) +
      Zsqrtd.sqrtd * ((1027708 : ℤ) : GaussianInt)) = _
    rw [map_add, map_mul, map_intCast, map_intCast]
    simp only [j, Int.cast_neg, Int.cast_ofNat]
  have hc : (f gaussianDiscriminant)^p = (-5045155 : F) - j*1027708 := by
    change frobenius F p (f gaussianDiscriminant) = _
    rw [hx, map_add, map_mul]
    have h₁ := map_intCast (frobenius F p) (-5045155)
    have h₂ := map_intCast (frobenius F p) 1027708
    push_cast at h₁ h₂
    rw [h₁, h₂, show frobenius F p j = j^p from rfl, hjp]
    ring
  rw [pow_succ, hc, hx]
  linear_combination -(1027708 : F)^2 * hj

/-- The archived three-symbol sign at `(p)` equals the actual splitting
sign at the unique Gaussian prime above every rational `p ≡ 3 mod 4`. -/
theorem quarticDiscriminantSign_inert (p : ℕ) [Fact p.Prime] (hp : p % 4 = 3)
    (I : ↥(gaussianPrimesAbove p)) :
    quarticDiscriminantSign p I = archivedGaussianSign (p : GaussianInt) := by
  let F := GaussianInt ⧸ I.val
  let : I.val.IsMaximal := gaussianPrimesAbove_isMaximal I.property
  let : Finite F := gaussian_finiteQuotient I.val (gaussianPrimesAbove_ne_bot I.property)
  let : Fintype F := Fintype.ofFinite _
  have hI := eq_inert_gaussian_prime hp I.property
  have hFp : (p : F) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I.val)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI ▸ Ideal.subset_span (Set.mem_singleton _))
  have hchar := CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hFp
  have hp₂ : p ≠ 2 := by omega
  have hF₂ : ringChar F ≠ 2 := hchar.trans_ne hp₂
  let : CharP F p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hFp
  let f : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  let x : F := Ideal.Quotient.mk I.val gaussianDiscriminant
  have hnorm : x^(p+1) = f ((26509772707289 : ℤ) : ZMod p) := by
    rw [map_intCast]
    simpa only [Int.cast_ofNat] using inert_discriminant_norm p hp (Ideal.Quotient.mk I.val)
  have hCard : Fintype.card F = p^2 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (GaussianInt ⧸ I.val) = _
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hI, gaussian_rational_prime_absNorm]
  have hχ : quadraticChar F x = quadraticChar (ZMod p) ((26509772707289 : ℤ) : ZMod p) := by
    apply (quadraticChar_isQuadratic F).eq_of_eq_coe (quadraticChar_isQuadratic (ZMod p)) hF₂
    rw [quadraticChar_eq_pow_of_char_ne_two' hF₂, hCard, half_square p (by omega), pow_mul, hnorm]
    have hz := quadraticChar_eq_pow_of_char_ne_two'
      (show ringChar (ZMod p) ≠ 2 by rwa [ZMod.ringChar_zmod_n]) ((26509772707289 : ℤ) : ZMod p)
    have hf := congrArg f hz
    rw [map_intCast, ZMod.card, map_pow] at hf
    exact hf.symm
  rw [archivedGaussianSign_natCast, ← rationalNormSign_reciprocity p hp₂]
  simpa only [quarticDiscriminantSign, if_neg (Ring.two_ne_zero hF₂), legendreSym] using hχ

/-- The inert-prime factorization with the actual archived Gaussian sign. -/
theorem fieldLocalEulerSeries_mul_archived_inert_denominator (p : ℕ) [Fact p.Prime]
    (hp : p % 4 = 3) :
    let T := (PowerSeries.X : PowerSeries ℂ)
    fieldLocalEulerSeries K p * ((1-T^2)*(1-(archivedGaussianSign (p : GaussianInt) : PowerSeries ℂ)*T^2)) = 1 := by
  let T := (PowerSeries.X : PowerSeries ℂ)
  have hc := fieldLocalEulerSeries_mul_character_denominators p
  have hf (I : ↥(gaussianPrimesAbove p)) : I.val.inertiaDeg ℤ = 2 :=
    (congrArg (fun A : Ideal GaussianInt => A.inertiaDeg ℤ)
      (eq_inert_gaussian_prime hp I.property)).trans (inert_gaussian_prime_degree hp)
  have hCard : Fintype.card ↥(gaussianPrimesAbove p) = 1 := by
    rw [Fintype.card_coe, inert_gaussian_primes hp, Finset.card_singleton]
  simp_rw [quarticDiscriminantSign_inert p hp, hf] at hc
  rw [Finset.prod_const, Finset.card_univ, hCard, pow_one, ZMod.χ₄_nat_three_mod_four hp] at hc
  have hb : (1-T)*(1-((-1 : ℤ) : PowerSeries ℂ)*T) = 1-T^2 := by
    push_cast
    ring
  change fieldLocalEulerSeries K p * (((1-T)*(1-((-1 : ℤ) : PowerSeries ℂ)*T)) *
    (1-(archivedGaussianSign (p : GaussianInt) : PowerSeries ℂ)*T^2)) = 1 at hc
  rw [hb] at hc
  exact hc

#print axioms quarticDiscriminantSign_inert
#print axioms fieldLocalEulerSeries_mul_archived_inert_denominator

end QuarticModel
