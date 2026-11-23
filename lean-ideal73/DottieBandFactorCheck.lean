import DottieBandPrimePowers
import DottieStructuralJacobi

/-! Evaluate prime-power factors with the archived Gaussian character.
Prime witnesses are checked separately, then the arithmetic reduces in Lean. -/

namespace QuarticModel

open Finset PowerSeries
open scoped Classical
open private structuralJacobi structuralJacobi_eq from DottieStructuralJacobi
open private fastJacobiSym.eq from Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
set_option autoImplicit false

/-- The factor associated with a square root k of -1 modulo an odd prime. -/
def dottieBandSplitValue (p r e : ℕ) : ℤ :=
  let s := structuralJacobi (-5045155+1027708*(r : ℤ)) p
  let t := structuralJacobi (-5045155-1027708*(r : ℤ)) p
  ∑ j ∈ range (e+1), s^j*t^(e-j)

private theorem dottie_band_structure_quadratic {p : ℕ} [Fact p.Prime] (a : ℤ)
    (ho : p % 2 = 1) :
    quadraticChar (ZMod p) (a : ZMod p) = structuralJacobi a p := by
  rw [structuralJacobi_eq a p (Fact.out : p.Prime).one_lt ho, ← fastJacobiSym.eq,
    ← jacobiSym.legendreSym.to_jacobiSym,legendreSym]

theorem dottie_band_split_value_correct {p : ℕ} [Fact p.Prime] (r e : ℕ)
    (hp : p % 4 = 1) (hroot : r^2 % p = p-1) :
    archivedLatticeCoeff (p^e) = dottieBandSplitValue p r e := by
  have hp₂ : p ≠ 2 := by omega
  have ho : p % 2 = 1 := by omega
  have hp₁ : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  let k : ZMod p := r
  have hr : k^2 = -1 := by
    change (r : ZMod p)^2 = -1
    rw [← Nat.cast_pow,← ZMod.natCast_mod (r^2) p,hroot,Nat.cast_sub hp₁,
      ZMod.natCast_self,Nat.cast_one,zero_sub]
  have hn : (-k)^2 = -1 := by simpa only [neg_sq] using hr
  have hs : gaussianPrimesAbove p = {gaussianPrimeAt k hr,gaussianPrimeAt (-k) hn} :=
    split_gaussian_primes hp₂ k hr hn
  have hmPos : gaussianPrimeAt k hr ∈ gaussianPrimesAbove p := by simp [hs]
  have hmNeg : gaussianPrimeAt (-k) hn ∈ gaussianPrimesAbove p := by simp [hs]
  have hpos : archivedIdealCharacter (gaussianPrimeAt k hr) =
      structuralJacobi (-5045155+1027708*(r : ℤ)) p := by
    rw [← quarticDiscriminantSign_eq_archivedIdealCharacter p ⟨_,hmPos⟩,
      quarticDiscriminantSign_split hp₂ k hr ⟨_,hmPos⟩ rfl]
    have he := dottie_band_structure_quadratic (-5045155+1027708*(r : ℤ)) ho
    simpa only [Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_natCast,k] using he
  have hneg : archivedIdealCharacter (gaussianPrimeAt (-k) hn) =
      structuralJacobi (-5045155-1027708*(r : ℤ)) p := by
    rw [← quarticDiscriminantSign_eq_archivedIdealCharacter p ⟨_,hmNeg⟩,
      quarticDiscriminantSign_split hp₂ (-k) hn ⟨_,hmNeg⟩ rfl]
    have he := dottie_band_structure_quadratic (-5045155-1027708*(r : ℤ)) ho
    simpa only [Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_ofNat,Int.cast_natCast,k,
      mul_neg,sub_eq_add_neg] using he
  rw [dottie_band_split_prime_power hp₂ k hr hn e,hpos,hneg]
  rfl

def dottieBandInertValue (p e : ℕ) : ℤ :=
  if 2 ∣ e then dottieStructuralRowSign p 0^(e/2) else 0

theorem dottie_band_inert_value_correct {p : ℕ} [Fact p.Prime] (e : ℕ) (hp : p % 4 = 3) :
    archivedLatticeCoeff (p^e) = dottieBandInertValue p e := by
  let I : Ideal GaussianInt := Ideal.span {(p : GaussianInt)}
  have hdeg : I.inertiaDeg ℤ = 2 := inert_gaussian_prime_degree hp
  have hsign : archivedIdealCharacter I = dottieStructuralRowSign p 0 := by
    rw [show I = Ideal.span {(p : GaussianInt)} from rfl,archivedIdealCharacter_span,
      dottieStructuralRowSign_eq,dottieRowSign_eq_archivedGaussianSign]
    congr 1
  have he : signedLocalEulerSeries p = weightedGeometricAtDegree
      (dottieStructuralRowSign p 0 : ℂ) 2 := by
    rw [signedLocalEulerSeries,Finset.prod_coe_sort (gaussianPrimesAbove p)
      (fun J => weightedGeometricAtDegree (archivedIdealCharacter J : ℂ) (J.inertiaDeg ℤ)),
      inert_gaussian_primes hp,Finset.prod_singleton]
    change weightedGeometricAtDegree (archivedIdealCharacter I : ℂ) (I.inertiaDeg ℤ) = _
    rw [hsign,hdeg]
  apply Int.cast_injective (α := ℂ)
  rw [archivedLatticeCoeff_eq_signedIdealNormSum _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero),
    signedIdealNormSum_primePower,he,coeff_weightedGeometricAtDegree _ (by decide : (2 : ℕ) ≠ 0)]
  simp [dottieBandInertValue]

#print axioms dottie_band_split_value_correct
#print axioms dottie_band_inert_value_correct

structure DottieBandFactor where
  prime : ℕ
  exponent : ℕ
  splitRoot : Option ℕ

def DottieBandFactor.evaluate (primeOk : ℕ → Bool) (f : DottieBandFactor) : Option ℤ :=
  if primeOk f.prime && decide (0 < f.exponent ∧ f.exponent ≤ 64) then
    match f.splitRoot with
    | none => if f.prime % 4 = 3 then some (dottieBandInertValue f.prime f.exponent) else none
    | some r =>
      if f.prime % 4 = 1 ∧ r^2 % f.prime = f.prime-1 then
        some (dottieBandSplitValue f.prime r f.exponent)
      else none
  else none

private theorem dottie_band_factor_evaluate_sound {primeOk : ℕ → Bool}
    (hp : ∀ p, primeOk p = true → p.Prime) {f : DottieBandFactor} {c : ℤ}
    (hc : f.evaluate primeOk = some c) :
    0 < f.prime^f.exponent ∧ archivedLatticeCoeff (f.prime^f.exponent) = c := by
  rw [DottieBandFactor.evaluate] at hc
  split at hc
  · rename_i hvalid
    rw [Bool.and_eq_true] at hvalid
    have hPrime := hp f.prime hvalid.1
    let : Fact f.prime.Prime := ⟨hPrime⟩
    refine ⟨pow_pos hPrime.pos _,?_⟩
    cases hr : f.splitRoot with
    | none =>
      rw [hr] at hc
      change (if f.prime % 4 = 3 then some (dottieBandInertValue f.prime f.exponent)
        else none) = some c at hc
      by_cases hm : f.prime % 4 = 3
      · rw [if_pos hm] at hc
        exact (dottie_band_inert_value_correct f.exponent hm).trans (Option.some.inj hc)
      · simp [hm] at hc
    | some root =>
      rw [hr] at hc
      change (if f.prime % 4 = 1 ∧ root^2 % f.prime = f.prime-1 then
        some (dottieBandSplitValue f.prime root f.exponent) else none) = some c at hc
      by_cases hm : f.prime % 4 = 1 ∧ root^2 % f.prime = f.prime-1
      · rw [if_pos hm] at hc
        exact (dottie_band_split_value_correct root f.exponent hm.1 hm.2).trans (Option.some.inj hc)
      · simp [hm] at hc
  · contradiction

def dottieBandFactorProduct (primeOk : ℕ → Bool) : List DottieBandFactor → Option (ℕ × ℤ)
  | [] => some (1,1)
  | f::tail => do
    let c ← f.evaluate primeOk
    let (n,d) ← dottieBandFactorProduct primeOk tail
    let m := f.prime^f.exponent
    if m.Coprime n then some (m*n,c*d) else none

private theorem dottie_band_factor_product_sound {primeOk : ℕ → Bool}
    (hp : ∀ p, primeOk p = true → p.Prime) {factors : List DottieBandFactor} {n : ℕ} {a : ℤ}
    (hc : dottieBandFactorProduct primeOk factors = some (n,a)) :
    0 < n ∧ archivedLatticeCoeff n = a := by
  induction factors generalizing n a with
  | nil =>
    have h := Option.some.inj hc
    cases h
    refine ⟨by decide,?_⟩
    have h1 := signedIdealCoefficients_multiplicative.map_one
    rw [signedIdealCoefficients_eq_archivedLatticeCoeff] at h1
    exact_mod_cast h1
  | cons f fs ih =>
    rw [dottieBandFactorProduct] at hc
    cases hf : f.evaluate primeOk with
    | none => simp [hf] at hc
    | some c =>
      cases ht : dottieBandFactorProduct primeOk fs with
      | none => simp [hf,ht] at hc
      | some pair =>
        obtain ⟨m,d⟩ := pair
        rw [hf,ht] at hc
        change (if (f.prime^f.exponent).Coprime m then some (f.prime^f.exponent*m,c*d)
          else none) = some (n,a) at hc
        split at hc
        · rename_i hcoprime
          have he := Option.some.inj hc
          cases he
          obtain ⟨hpos,hf'⟩ := dottie_band_factor_evaluate_sound hp hf
          obtain ⟨hm,ht'⟩ := ih ht
          exact ⟨Nat.mul_pos hpos hm,by rw [archivedLatticeCoeff_mul_of_coprime hpos hm hcoprime,hf',ht']⟩
        · contradiction

def dottieBandFactoredRowCheck (primeOk : ℕ → Bool) (n twos : ℕ)
    (factors : List DottieBandFactor) (value : ℤ) : Bool :=
  match dottieBandFactorProduct primeOk factors with
  | none => false
  | some (m,c) => decide (twos ≤ 64 ∧ n = 2^twos*m ∧ value = c)

theorem dottie_band_factored_row_check_sound {primeOk : ℕ → Bool}
    (hp : ∀ p, primeOk p = true → p.Prime)
    {n twos : ℕ} {factors : List DottieBandFactor} {value : ℤ}
    (h : dottieBandFactoredRowCheck primeOk n twos factors value = true) :
    archivedLatticeCoeff n = value := by
  rw [dottieBandFactoredRowCheck] at h
  cases he : dottieBandFactorProduct primeOk factors with
  | none => simp [he] at h
  | some pair =>
    obtain ⟨m,v⟩ := pair
    rw [he] at h
    obtain ⟨_,hn,hv⟩ := of_decide_eq_true h
    rw [hn,archivedLatticeCoeff_two_pow_mul,hv]
    exact (dottie_band_factor_product_sound hp he).2

#print axioms dottie_band_factored_row_check_sound

end QuarticModel
