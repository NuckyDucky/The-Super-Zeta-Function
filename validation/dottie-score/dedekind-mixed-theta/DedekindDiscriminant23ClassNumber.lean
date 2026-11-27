import DedekindDiscriminant23ClassRepresentatives
import Mathlib.Tactic.IntervalCases

namespace FieldTarget

open NumberField
open scoped NumberField nonZeroDivisors

local notation "F" => (discriminant23QuadraticSubfield : Type)
local notation "ω" => discriminant23Omega
local notation "P" => discriminant23NormTwoIdeal

noncomputable section

private def primeTwoConjugate : Ideal (𝓞 F) :=
  discriminant23ResidueIdeal 2 1 (by decide +kernel)

private def primeThree : Ideal (𝓞 F) :=
  discriminant23ResidueIdeal 3 0 (by decide +kernel)

private def primeThreeConjugate : Ideal (𝓞 F) :=
  discriminant23ResidueIdeal 3 1 (by decide +kernel)

private theorem primeTwoConjugate_norm : primeTwoConjugate.absNorm = 2 :=
  discriminant23ResidueIdeal_absNorm _ _

private theorem primeThree_norm : primeThree.absNorm = 3 :=
  discriminant23ResidueIdeal_absNorm _ _

private theorem primeThreeConjugate_norm : primeThreeConjugate.absNorm = 3 :=
  discriminant23ResidueIdeal_absNorm _ _

private theorem residue_mem_iff {p : ℕ} (r : ZMod p) (hr : r ^ 2 - r + 6 = 0) (m n : ℤ) :
    (m : 𝓞 F) + n * ω ∈ discriminant23ResidueIdeal p r hr ↔ (m : ZMod p) + (n : ZMod p) * r = 0 := by
  change discriminant23ResidueHom r hr ((m : 𝓞 F) + n * ω) = 0 ↔ _
  rw [discriminant23ResidueHom_apply]

private theorem mem_primeTwo_omega : ω ∈ P := by
  simpa using (discriminant23NormTwoIdeal_mem 0 1).mpr (dvd_zero 2)

private theorem primeTwo_ne_conjugate : P ≠ primeTwoConjugate := by
  intro h
  have hm : ω ∈ primeTwoConjugate := h ▸ mem_primeTwo_omega
  have hnot := (residue_mem_iff (1 : ZMod 2) (by decide +kernel) 0 1).mp
  have h1 : (0 : ZMod 2) + (1 : ZMod 2) * 1 = 0 := hnot (by simpa [primeTwoConjugate] using hm)
  simp at h1

private theorem ideal_eq_of_le_eq_positive_norm {I J : Ideal (𝓞 F)}
    (hle : I ≤ J) (hN : I.absNorm = J.absNorm) (hp : 0 < J.absNorm) : I = J := by
  obtain ⟨D, hD⟩ := Ideal.dvd_iff_le.mpr hle
  have hd := congrArg Ideal.absNorm hD
  rw [map_mul, hN] at hd
  have hd' : J.absNorm * D.absNorm = J.absNorm * 1 := by simpa only [mul_one] using hd.symm
  have hd1 : D.absNorm = 1 := Nat.eq_of_mul_eq_mul_left hp hd'
  rw [Ideal.absNorm_eq_one_iff.mp hd1, ← Ideal.one_eq_top, mul_one] at hD
  exact hD

private theorem prime_product_of_membership {I J : Ideal (𝓞 F)} (hI : I.absNorm.Prime)
    (hJ : J.absNorm.Prime) (hne : I ≠ J) {x : 𝓞 F} (hxI : x ∈ I) (hxJ : x ∈ J)
    (hn : (Algebra.norm ℤ x).natAbs = I.absNorm * J.absNorm) :
    I * J = Ideal.span ({x} : Set (𝓞 F)) := by
  have hIp : I.IsPrime := Ideal.isPrime_of_irreducible_absNorm
    ((Nat.irreducible_iff_prime).mpr (Nat.prime_iff.mp hI))
  have hJp : J.IsPrime := Ideal.isPrime_of_irreducible_absNorm
    ((Nat.irreducible_iff_prime).mpr (Nat.prime_iff.mp hJ))
  let : I.IsMaximal := hIp.isMaximal (by
    intro h
    rw [h, Ideal.absNorm_bot] at hI
    exact hI.ne_zero rfl)
  let : J.IsMaximal := hJp.isMaximal (by
    intro h
    rw [h, Ideal.absNorm_bot] at hJ
    exact hJ.ne_zero rfl)
  have hle : Ideal.span ({x} : Set (𝓞 F)) ≤ I * J := by
    rw [Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_of_isMaximal hne)]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ⟨hxI, hxJ⟩)
  exact (ideal_eq_of_le_eq_positive_norm hle (by rw [Ideal.absNorm_span_singleton, hn, map_mul])
    (by rw [map_mul]; exact Nat.mul_pos hI.pos hJ.pos)).symm

private theorem norm_two_product : P * primeTwoConjugate = Ideal.span ({2} : Set (𝓞 F)) := by
  apply prime_product_of_membership
    (by rw [discriminant23NormTwoIdeal_absNorm]; decide +kernel)
    (by rw [primeTwoConjugate_norm]; decide +kernel) primeTwo_ne_conjugate
  · simpa [discriminant23NormTwoIdeal_absNorm] using Ideal.absNorm_mem P
  · simpa [primeTwoConjugate_norm] using Ideal.absNorm_mem primeTwoConjugate
  · have h := discriminant23_quadratic_norm 2 0
    norm_num at h
    norm_num [h, discriminant23NormTwoIdeal_absNorm, primeTwoConjugate_norm]

private theorem norm_omega_product : P * primeThree = Ideal.span ({ω} : Set (𝓞 F)) := by
  apply prime_product_of_membership
    (by rw [discriminant23NormTwoIdeal_absNorm]; decide +kernel)
    (by rw [primeThree_norm]; decide +kernel)
    (by intro h; have he := congrArg Ideal.absNorm h; norm_num [discriminant23NormTwoIdeal_absNorm, primeThree_norm] at he)
    mem_primeTwo_omega
  · simpa [primeThree] using (residue_mem_iff (0 : ZMod 3) (by decide +kernel) 0 1).mpr (by decide +kernel)
  · have h := discriminant23_quadratic_norm 0 1
    norm_num at h
    norm_num [h, discriminant23NormTwoIdeal_absNorm, primeThree_norm]

private theorem norm_other_omega_product :
    primeTwoConjugate * primeThreeConjugate = Ideal.span ({ω - 1} : Set (𝓞 F)) := by
  apply prime_product_of_membership
    (by rw [primeTwoConjugate_norm]; decide +kernel)
    (by rw [primeThreeConjugate_norm]; decide +kernel)
    (by intro h; have he := congrArg Ideal.absNorm h; norm_num [primeTwoConjugate_norm, primeThreeConjugate_norm] at he)
  · simpa [primeTwoConjugate, sub_eq_add_neg, add_comm] using
      (residue_mem_iff (1 : ZMod 2) (by decide +kernel) (-1) 1).mpr (by decide +kernel)
  · simpa [primeThreeConjugate, sub_eq_add_neg, add_comm] using
      (residue_mem_iff (1 : ZMod 3) (by decide +kernel) (-1) 1).mpr (by decide +kernel)
  · have h : Algebra.norm ℤ (ω - 1) = 6 := by
      simpa [sub_eq_add_neg, add_comm] using discriminant23_quadratic_norm (-1) 1
    norm_num [h, primeTwoConjugate_norm, primeThreeConjugate_norm]

private def idealWithNonzeroNorm (J : Ideal (𝓞 F)) (hJ : J.absNorm ≠ 0) : (Ideal (𝓞 F))⁰ :=
  ⟨J, mem_nonZeroDivisors_of_ne_zero (fun h ↦ hJ (by simp [h]))⟩

def discriminant23NormTwoClass : ClassGroup (𝓞 F) :=
  ClassGroup.mk0 (idealWithNonzeroNorm P (by rw [discriminant23NormTwoIdeal_absNorm]; decide))

local notation "classTwo" => discriminant23NormTwoClass

private theorem class_inverse_of_product {I J : (Ideal (𝓞 F))⁰} {x : 𝓞 F}
    (h : (I : Ideal (𝓞 F)) * (J : Ideal (𝓞 F)) = Ideal.span {x}) :
    ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ := by
  have hx : x ≠ 0 := by
    intro h0
    apply mul_ne_zero (nonZeroDivisors.coe_ne_zero I) (nonZeroDivisors.coe_ne_zero J)
    simpa [h0] using h
  exact ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨x, hx, h⟩

theorem discriminant23_class_candidates (C : ClassGroup (𝓞 F)) :
    C = 1 ∨ C = classTwo ∨ C = classTwo⁻¹ := by
  obtain ⟨I, hI, hn⟩ := discriminant23_class_small_representative C
  have h0 := Ideal.absNorm_ne_zero_of_nonZeroDivisors I
  let I2 := idealWithNonzeroNorm P (by rw [discriminant23NormTwoIdeal_absNorm]; decide)
  let I2' := idealWithNonzeroNorm primeTwoConjugate (by rw [primeTwoConjugate_norm]; decide)
  let I3 := idealWithNonzeroNorm primeThree (by rw [primeThree_norm]; decide)
  let I3' := idealWithNonzeroNorm primeThreeConjugate (by rw [primeThreeConjugate_norm]; decide)
  have htwo : ClassGroup.mk0 I2' = classTwo⁻¹ := by
    apply class_inverse_of_product (I := I2') (J := I2)
    simpa only [I2, I2', idealWithNonzeroNorm, mul_comm] using norm_two_product
  have hthree : ClassGroup.mk0 I3 = classTwo⁻¹ := by
    apply class_inverse_of_product (I := I3) (J := I2)
    simpa only [I3, I2, idealWithNonzeroNorm, mul_comm] using norm_omega_product
  have hthree' : ClassGroup.mk0 I3' = classTwo := by
    have h := class_inverse_of_product (I := I3') (J := I2') (x := ω - 1)
      (by simpa only [I3', I2', idealWithNonzeroNorm, mul_comm] using norm_other_omega_product)
    simpa only [htwo, inv_inv] using h
  have hs : (I : Ideal (𝓞 F)).absNorm = 1 ∨ (I : Ideal (𝓞 F)).absNorm = 2 ∨
      (I : Ideal (𝓞 F)).absNorm = 3 := by omega
  rcases hs with hs | hs | hs
  · left
    rw [← hI]
    have he : I = 1 := Subtype.ext (by
      rw [Submonoid.coe_one, Ideal.one_eq_top]
      exact Ideal.absNorm_eq_one_iff.mp hs)
    rw [he, map_one]
  · let : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
    obtain ⟨e, he, _, hJ⟩ := discriminant23_small_prime_ideal (p := 2) (by decide) _ hs
    rcases he with rfl | rfl
    · have heq : I = I2 := Subtype.ext hJ
      exact Or.inr (Or.inl ((hI.symm.trans (congrArg ClassGroup.mk0 heq))))
    · have heq : I = I2' := Subtype.ext hJ
      rw [← hI, heq, htwo]
      exact Or.inr (Or.inr rfl)
  · let : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
    obtain ⟨e, he, _, hJ⟩ := discriminant23_small_prime_ideal (p := 3) (by decide) _ hs
    rcases he with rfl | rfl
    · have heq : I = I3 := Subtype.ext hJ
      rw [← hI, heq, hthree]
      exact Or.inr (Or.inr rfl)
    · have heq : I = I3' := Subtype.ext hJ
      rw [← hI, heq, hthree']
      exact Or.inr (Or.inl rfl)

private theorem small_norm_integer {x : 𝓞 F} (hx : (Algebra.norm ℤ x).natAbs ≤ 4) :
    ∃ m : ℤ, x = (m : 𝓞 F) ∧ (Algebra.norm ℤ x).natAbs = m.natAbs ^ 2 := by
  obtain ⟨m, n, he⟩ : ∃ m n : ℤ, x = (m : 𝓞 F) + n * ω :=
    ⟨_, _, discriminant23Integers_coordinates x⟩
  have hg : m ^ 2 + m * n + 6 * n ^ 2 ≤ 4 := by
    rw [he, discriminant23_quadratic_norm] at hx
    have ha := (Int.natCast_natAbs (m ^ 2 + m * n + 6 * n ^ 2))
    have hp : ((m ^ 2 + m * n + 6 * n ^ 2).natAbs : ℤ) ≤ 4 := by exact_mod_cast hx
    rw [ha] at hp
    exact (le_abs_self _).trans hp
  have hn : n = 0 := by
    by_contra h
    have hs := sq_pos_of_ne_zero h
    have hn : 1 ≤ n ^ 2 := by omega
    nlinarith only [hn, hg, sq_nonneg (2 * m + n)]
  subst n
  have he' : x = (m : 𝓞 F) := by simpa using he
  refine ⟨m, he', ?_⟩
  rw [he, discriminant23_quadratic_norm]
  simp [Int.natAbs_pow]

private theorem classTwo_ne_one : classTwo ≠ 1 := by
  intro h
  have hp := (ClassGroup.mk0_eq_one_iff (idealWithNonzeroNorm P
    (by rw [discriminant23NormTwoIdeal_absNorm]; decide)).property).mp h
  let : discriminant23NormTwoIdeal.IsPrincipal := hp
  obtain ⟨x, hx⟩ := Submodule.IsPrincipal.principal P
  have hn : (Algebra.norm ℤ x).natAbs = 2 := by
    have hh := congrArg Ideal.absNorm hx
    rwa [discriminant23NormTwoIdeal_absNorm, Ideal.absNorm_span_singleton, eq_comm] at hh
  obtain ⟨m, _, hm⟩ := small_norm_integer (by rw [hn]; decide)
  have hsq : m.natAbs ^ 2 = 2 := hm.symm.trans hn
  have hb : m.natAbs ≤ 2 := by
    by_contra! hh
    have hs := Nat.mul_le_mul (show 3 ≤ m.natAbs by omega) (show 3 ≤ m.natAbs by omega)
    nlinarith only [hs, hsq]
  interval_cases h : m.natAbs <;> norm_num [h] at hsq

private theorem classTwo_ne_inv : classTwo ≠ classTwo⁻¹ := by
  intro h
  obtain ⟨x, _, hx⟩ := ClassGroup.mk0_eq_mk0_inv_iff.mp h
  have hP : P * P = Ideal.span {x} := hx
  have hnorm : (Algebra.norm ℤ x).natAbs = 4 := by
    have h := congrArg Ideal.absNorm hP
    rw [map_mul, discriminant23NormTwoIdeal_absNorm, Ideal.absNorm_span_singleton] at h
    exact h.symm
  obtain ⟨m, hx', hm⟩ := small_norm_integer (le_of_eq hnorm)
  have hn : m.natAbs = 2 := by
    apply Nat.pow_left_injective (n := 2) (by decide)
    exact hm.symm.trans hnorm
  have hi : m = 2 ∨ m = -2 := by omega
  have hspan : Ideal.span ({x} : Set (𝓞 F)) = Ideal.span ({2} : Set (𝓞 F)) := by
    rcases hi with hm | hm
    · simp [hx', hm]
    · simp [hx', hm, Ideal.span_singleton_neg]
  have hprod : P * P = P * primeTwoConjugate := hP.trans (hspan.trans norm_two_product.symm)
  have hp0 : P ≠ 0 := nonZeroDivisors.coe_ne_zero
    (idealWithNonzeroNorm P (by rw [discriminant23NormTwoIdeal_absNorm]; decide))
  exact primeTwo_ne_conjugate (mul_left_cancel₀ hp0 hprod)

theorem discriminant23_class_number : NumberField.classNumber F = 3 := by
  classical
  have hinv : classTwo⁻¹ ≠ 1 := fun h ↦ classTwo_ne_one (inv_eq_one.mp h)
  let s : Finset (ClassGroup (𝓞 F)) := {1, classTwo, classTwo⁻¹}
  have hs : Finset.univ = s := by
    ext C
    simp only [Finset.mem_univ, true_iff, s, Finset.mem_insert, Finset.mem_singleton]
    exact discriminant23_class_candidates C
  change Finset.univ.card = 3
  rw [hs]
  simp [s, classTwo_ne_one.symm, classTwo_ne_inv, hinv.symm]

theorem discriminant23_class_group_cyclic : IsCyclic (ClassGroup (𝓞 F)) := by
  let : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
  apply isCyclic_of_prime_card (p := 3)
  rw [Nat.card_eq_fintype_card]
  exact discriminant23_class_number

#check @discriminant23_class_number
#check @discriminant23_class_candidates
#print axioms discriminant23_class_number
#print axioms discriminant23_class_group_cyclic

end
end FieldTarget
