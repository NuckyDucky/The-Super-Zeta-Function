import DedekindDiscriminant23NormForms
import Mathlib.NumberTheory.NumberField.ClassNumber

namespace FieldTarget

open NumberField
open scoped NumberField nonZeroDivisors

local notation "F" => (discriminant23QuadraticSubfield : Type)
local notation "ω" => discriminant23Omega

theorem discriminant23_class_small_representative (C : ClassGroup (𝓞 F)) :
    ∃ I : (Ideal (𝓞 F))⁰, ClassGroup.mk0 I = C ∧ (I : Ideal (𝓞 F)).absNorm ≤ 3 := by
  let : IsTotallyComplex F := discriminant23_quadratic_totallyComplex
  have hdeg := discriminant23QuadraticSubfield_finrank
  have hc : InfinitePlace.nrComplexPlaces F = 1 := by
    have h := IsTotallyComplex.finrank F
    omega
  have hs : Real.sqrt 23 < 5 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 23 by norm_num)
    nlinarith only [h, Real.sqrt_nonneg 23]
  have hM : (4 / Real.pi) * (2 / 4 * Real.sqrt 23) < 4 := by
    rw [show (4 / Real.pi) * (2 / 4 * Real.sqrt 23) = 2 * Real.sqrt 23 / Real.pi by ring]
    apply (div_lt_iff₀ Real.pi_pos).mpr
    linarith only [hs, Real.pi_gt_d2]
  obtain ⟨I, hI, hN⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  rw [hc, hdeg, discriminant23_quadratic_discriminant] at hN
  norm_num [Nat.factorial] at hN
  have hN' : ((I : Ideal (𝓞 F)).absNorm : ℝ) < 4 := hN.trans_lt (by norm_num at hM ⊢; exact hM)
  have hNat : (I : Ideal (𝓞 F)).absNorm < 4 := by exact_mod_cast hN'
  exact ⟨I, hI, by omega⟩

private theorem residue_ideal_le {p : ℕ} {J : Ideal (𝓞 F)} {e : ℤ}
    (he : (e : ZMod p) ^ 2 - (e : ZMod p) + 6 = 0) (hp : (p : 𝓞 F) ∈ J)
    (hω : ω - (e : 𝓞 F) ∈ J) : discriminant23ResidueIdeal p (e : ZMod p) he ≤ J := by
  intro x hx
  obtain ⟨m, n, rfl⟩ : ∃ m n : ℤ, x = (m : 𝓞 F) + n * ω :=
    ⟨_, _, discriminant23Integers_coordinates x⟩
  have hmod : ((m + n * e : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [← discriminant23ResidueHom_apply he]
    exact hx
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hmod
  have hk' : (m : 𝓞 F) + (n : 𝓞 F) * e = (p : 𝓞 F) * k := by
    exact_mod_cast hk
  have hdec : (m : 𝓞 F) + n * ω = (p : 𝓞 F) * k + n * (ω - e) := by
    linear_combination hk'
  rw [hdec]
  exact J.add_mem (J.mul_mem_right _ hp) (J.mul_mem_left _ hω)

/-- Both possible residues of `ω` are explicit when the norm is a prime dividing six. -/
theorem discriminant23_small_prime_ideal {p : ℕ} [Fact p.Prime] (hp : p ∣ 6)
    (J : Ideal (𝓞 F)) (hJ : J.absNorm = p) :
    ∃ e : ℤ, (e = 0 ∨ e = 1) ∧
      ∃ he : (e : ZMod p) ^ 2 - (e : ZMod p) + 6 = 0,
        J = discriminant23ResidueIdeal p (e : ZMod p) he := by
  have hprime : Nat.Prime p := Fact.out
  let : NeZero p := ⟨hprime.ne_zero⟩
  have hJp : J.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by
    rw [hJ, Nat.irreducible_iff_prime, ← Nat.prime_iff]
    exact hprime)
  have hpJ : (p : 𝓞 F) ∈ J := hJ ▸ Ideal.absNorm_mem J
  have h6J : (6 : 𝓞 F) ∈ J := by
    obtain ⟨k, hk⟩ := hp
    have hs : (6 : 𝓞 F) = (p : 𝓞 F) * (k : 𝓞 F) := by exact_mod_cast hk
    rw [hs]
    exact J.mul_mem_right _ hpJ
  have hm : ω * (ω - 1) ∈ J := by
    rw [mul_sub, mul_one, ← pow_two, discriminant23Omega_sq,
      show ω - 6 - ω = -(6 : 𝓞 F) by ring]
    exact J.neg_mem h6J
  have h6mod : (6 : ZMod p) = 0 := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd 6 p).mpr (by exact_mod_cast hp)
  have hmatch (e : ℤ) (he : (e : ZMod p) ^ 2 - (e : ZMod p) + 6 = 0)
      (heJ : ω - (e : 𝓞 F) ∈ J) : J = discriminant23ResidueIdeal p (e : ZMod p) he := by
    have hnp : (discriminant23ResidueIdeal p (e : ZMod p) he) ≠ ⊥ := by
      intro h
      have hN := discriminant23ResidueIdeal_absNorm (e : ZMod p) he
      rw [h, Ideal.absNorm_bot] at hN
      exact hprime.ne_zero hN.symm
    have hmax := (discriminant23ResidueIdeal_isPrime (e : ZMod p) he).isMaximal hnp
    exact (hmax.eq_of_le hJp.ne_top (residue_ideal_le he hpJ heJ)).symm
  rcases hJp.mem_or_mem hm with h0 | h1
  · refine ⟨0, Or.inl rfl, ?_, ?_⟩
    · simpa using h6mod
    · exact hmatch 0 _ (by simpa using h0)
  · refine ⟨1, Or.inr rfl, ?_, ?_⟩
    · simpa using h6mod
    · exact hmatch 1 _ (by simpa using h1)

#check @discriminant23_class_small_representative
#check @discriminant23_small_prime_ideal
#print axioms discriminant23_class_small_representative
#print axioms discriminant23_small_prime_ideal

end FieldTarget
