import DedekindRationalPrimeFibers
import DedekindZetaZeroFree.RepresentationTheory.FiniteAbelian.RegularCharacterEulerPolynomial
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

namespace FieldTarget

open Ideal NumberField
open DedekindZetaZeroFree.AbelianQuotient

noncomputable local instance (m : ℕ) [NeZero m] : Fintype (DirichletCharacter ℂ m) :=
  Fintype.ofFinite _

private theorem dirichlet_character_euler_determinant (m : ℕ) [NeZero m]
    (g : (ZMod m)ˣ) (z : ℂ) :
    (∏ χ : DirichletCharacter ℂ m, (1 - χ g * z)) =
      (1 - z ^ orderOf g) ^ (Nat.card ((ZMod m)ˣ) / orderOf g) := by
  let e : DirichletCharacter ℂ m ≃ ComplexDual ((ZMod m)ˣ) := MulChar.equivToUnitHom
  calc
    _ = ∏ χ : DirichletCharacter ℂ m, (1 - (e χ g : ℂ) * z) := by
      apply Finset.prod_congr rfl
      intro χ _
      rw [show (e χ g : ℂ) = χ g from MulChar.coe_toUnitHom χ g]
    _ = ∏ ρ : ComplexDual ((ZMod m)ˣ), (1 - (ρ g : ℂ) * z) :=
      Equiv.prod_comp e (fun ρ : ComplexDual ((ZMod m)ˣ) ↦ 1 - (ρ g : ℂ) * z)
    _ = _ := regularCharacterDeterminant g z

/-- At an unramified rational prime the actual cyclotomic Euler denominator
is the product of all modulus-`m` Dirichlet Euler denominators. -/
theorem cyclotomic_localEuler_denominator_of_not_dvd
    (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ m) (z : ℂ) :
    (∏ P ∈ IsDedekindDomain.primesOverFinset (span {(p : ℤ)}) (𝓞 (CyclotomicField m ℚ)),
      (1 - z ^ P.inertiaDeg ℤ)) = ∏ χ : DirichletCharacter ℂ m, (1 - χ (p : ZMod m) * z) := by
  classical
  let K := CyclotomicField m ℚ
  let Q : Ideal ℤ := span {(p : ℤ)}
  let S := IsDedekindDomain.primesOverFinset Q (𝓞 K)
  let _ : IsCyclotomicExtension {m} ℚ K := CyclotomicField.isCyclotomicExtension m ℚ
  let _ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {m} ℚ K
  let g : (ZMod m)ˣ := ZMod.unitOfCoprime p ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hp)
  have hg : (g : ZMod m) = p := ZMod.coe_unitOfCoprime _ _
  have hf : Q.inertiaDegIn (𝓞 K) = orderOf g := by
    rw [IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := m) (p := p) (K := K) hp,
      ← hg, orderOf_units]
  have he : Q.ramificationIdxIn (𝓞 K) = 1 :=
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (m := m) (p := p) (K := K) hp
  have hQ : Q ≠ ⊥ := by simp [Q, (Fact.out : p.Prime).ne_zero]
  have hS : S.card = (primesOver Q (𝓞 K)).ncard := by
    rw [← IsDedekindDomain.coe_primesOverFinset hQ (𝓞 K), Set.ncard_coe_finset]
  have hdeg (P : Ideal (𝓞 K)) (hP : P ∈ S) : P.inertiaDeg ℤ = orderOf g := by
    have h := (IsDedekindDomain.mem_primesOverFinset_iff hQ (𝓞 K)).1 hP
    let _ : P.IsPrime := h.1
    let _ : P.LiesOver Q := h.2
    exact (inertiaDegIn_eq_inertiaDeg Q P Gal(K/ℚ)).symm.trans hf
  have hcardProd := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn Q (𝓞 K) Gal(K/ℚ)
  rw [he, hf, one_mul, IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K,
    IsCyclotomicExtension.Rat.finrank (k := m) K, ← hS] at hcardProd
  have hpos : 0 < orderOf g := dualEvaluation_orderOf_pos g
  have hcard : S.card = Nat.card ((ZMod m)ˣ) / orderOf g := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, ← hcardProd, Nat.mul_div_cancel _ hpos]
  change (∏ P ∈ S, (1 - z ^ P.inertiaDeg ℤ)) = _
  rw [← hg, dirichlet_character_euler_determinant m g z, ← hcard]
  simpa only [Finset.prod_const] using
    (Finset.prod_congr rfl (fun P hP ↦
      congrArg (fun d : ℕ ↦ 1 - z ^ d) (hdeg P hP)) :
        (∏ P ∈ S, (1 - z ^ P.inertiaDeg ℤ)) = ∏ _P ∈ S, (1 - z ^ orderOf g))

#check @cyclotomic_localEuler_denominator_of_not_dvd
#print axioms cyclotomic_localEuler_denominator_of_not_dvd

end FieldTarget
