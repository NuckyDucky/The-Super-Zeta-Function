import DedekindGaussianPrimeDegrees

namespace FieldTarget

set_option autoImplicit false

open Ideal NumberField

attribute [local instance] gaussianQuadratic_isCyclotomic

/-- The product over the actual prime ideals of the Gaussian field matches
the two rational Euler denominators at every rational prime. -/
theorem gaussianQuadratic_localEuler_denominator (p : ℕ) [Fact p.Prime] (z : ℂ) :
    (∏ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 GaussianQuadraticField),
      (1 - z ^ (P.inertiaDeg ℤ))) = (1 - z) * (1 - gaussianQuadraticChar (p : ZMod 4) * z) := by
  classical
  let K := GaussianQuadraticField
  let Q : Ideal ℤ := span {(p : ℤ)}
  let S := IsDedekindDomain.primesOverFinset Q (𝓞 K)
  let _ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {4} ℚ GaussianQuadraticField
  have hQ : Q ≠ ⊥ := by simp [Q, (Fact.out : p.Prime).ne_zero]
  have hdeg (P : Ideal (𝓞 K)) (hP : P ∈ S) :
      P.inertiaDeg ℤ = Q.inertiaDegIn (𝓞 K) := by
    have h := (IsDedekindDomain.mem_primesOverFinset_iff hQ (𝓞 K)).1 hP
    let _ : P.IsPrime := h.1
    let _ : P.LiesOver Q := h.2
    exact (inertiaDegIn_eq_inertiaDeg Q P Gal(K/ℚ)).symm
  have hcard : S.card = (primesOver Q (𝓞 K)).ncard := by
    rw [← IsDedekindDomain.coe_primesOverFinset hQ (𝓞 K), Set.ncard_coe_finset]
  have hprod : (∏ P ∈ S, (1 - z ^ (P.inertiaDeg ℤ))) =
      (1 - z ^ (Q.inertiaDegIn (𝓞 K))) ^ S.card := by
    calc
      _ = ∏ _ ∈ S, (1 - z ^ (Q.inertiaDegIn (𝓞 K))) := by
        apply Finset.prod_congr rfl
        intro P hP
        rw [hdeg P hP]
      _ = _ := Finset.prod_const _
  change (∏ P ∈ S, (1 - z ^ (P.inertiaDeg ℤ))) = _
  rw [hprod, hcard]
  change (1 - z ^ ((span {(p : ℤ)}).inertiaDegIn (𝓞 GaussianQuadraticField))) ^
    (primesOver (span {(p : ℤ)}) (𝓞 GaussianQuadraticField)).ncard = _
  by_cases hp : p = 2
  · subst p
    have hchi : gaussianQuadraticChar (2 : ZMod 4) = 0 := by
      change ((ZMod.χ₄ (2 : ZMod 4) : ℤ) : ℂ) = 0
      rw [show ZMod.χ₄ (2 : ZMod 4) = 0 by decide]
      norm_num
    simp [gaussianQuadratic_primesOver_two, gaussianQuadratic_inertiaDegIn_two, hchi]
  · rw [gaussianQuadratic_primesOver_odd p hp, gaussianQuadratic_oddPrime_inertiaDegIn p hp]
    have hodd := (Fact.out : p.Prime).mod_two_eq_one_iff_ne_two.mpr hp
    have hcases : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hcases with h | h
    · have hchi : gaussianQuadraticChar (p : ZMod 4) = 1 := by
        change ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℂ) = 1
        rw [ZMod.χ₄_nat_one_mod_four h]
        norm_num
      simp [h, hchi, pow_two]
    · have hnot : p % 4 ≠ 1 := by omega
      have hchi : gaussianQuadraticChar (p : ZMod 4) = -1 := by
        change ((ZMod.χ₄ (p : ZMod 4) : ℤ) : ℂ) = -1
        rw [ZMod.χ₄_nat_three_mod_four h]
        norm_num
      simp only [hnot, ite_false, pow_one, hchi]
      ring

#check @gaussianQuadratic_localEuler_denominator
#print axioms gaussianQuadratic_localEuler_denominator

end FieldTarget
