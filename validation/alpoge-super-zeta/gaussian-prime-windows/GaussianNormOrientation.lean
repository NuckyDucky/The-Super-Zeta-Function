import ArchivedGaussianIdealCharacter
import RelativeQuarticSplitSign
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.GCD.BigOperators

/-! The archived conductor reading cannot factor through the rational norm,
even after restricting to norms coprime to any prescribed modulus. -/

namespace QuarticModel

open scoped Classical

private abbrev D : ℕ := 26509772707289

private theorem sign_modEq (z w : GaussianInt)
    (hre : z.re ≡ w.re [ZMOD (D : ℤ)]) (him : z.im ≡ w.im [ZMOD (D : ℤ)]) :
    archivedGaussianSign z = archivedGaussianSign w := by
  rw [archivedGaussianSign_eq_norm_projection, archivedGaussianSign_eq_norm_projection]
  exact jacobiSym.mod_left' ((hre.mul_left (-5045155)).add (him.mul_left 1027708))

theorem archivedGaussianSigns_at_norm_73 :
    archivedGaussianSign (⟨3, 8⟩ : GaussianInt) = -1 ∧
      archivedGaussianSign (⟨3, -8⟩ : GaussianInt) = 1 := by
  rw [archivedGaussianSign_eq_norm_projection, archivedGaussianSign_eq_norm_projection]
  norm_num

/-- At every rational modulus, there is a conjugate pair of Gaussian
representatives with the same coprime norm and opposite archived signs. -/
theorem exists_opposite_archived_signs_coprime_norm (M : ℕ) (hM : M ≠ 0) :
    ∃ x y : ℕ, (x ^ 2 + y ^ 2).Coprime M ∧
      archivedGaussianSign (⟨x, y⟩ : GaussianInt) = -1 ∧
      archivedGaussianSign (⟨x, -(y : ℤ)⟩ : GaussianInt) = 1 := by
  let S := M.primeFactors.filter (fun q => ¬ q ∣ D)
  let B := ∏ q ∈ S, q
  have hDB : D.Coprime B := by
    apply Nat.coprime_prod_right_iff.mpr
    intro q hq
    have hs := Finset.mem_filter.mp hq
    exact ((Nat.prime_of_mem_primeFactors hs.1).coprime_iff_not_dvd.mpr hs.2).symm
  let x := Nat.chineseRemainder hDB 3 1
  let y := Nat.chineseRemainder hDB 8 0
  have hND : x.val ^ 2 + y.val ^ 2 ≡ 73 [MOD D] := by
    simpa using (x.property.1.pow 2).add (y.property.1.pow 2)
  have hNB : x.val ^ 2 + y.val ^ 2 ≡ 1 [MOD B] := by
    simpa using (x.property.2.pow 2).add (y.property.2.pow 2)
  have hcop : M.Coprime (x.val ^ 2 + y.val ^ 2) := by
    apply Nat.coprime_of_dvd
    intro q hq hqM hqN
    have hz := Nat.modEq_zero_iff_dvd.mpr hqN
    by_cases hqD : q ∣ D
    · have hq73 := Nat.modEq_zero_iff_dvd.mp ((hND.of_dvd hqD).symm.trans hz)
      have h73D : (73 : ℕ).Coprime D := by decide +kernel
      exact ((Nat.Prime.not_coprime_iff_dvd).2 ⟨q, hq, hq73, hqD⟩) h73D
    · have hqmem : q ∈ S := Finset.mem_filter.mpr ⟨hq.mem_primeFactors hqM hM, hqD⟩
      have hqB : q ∣ B := Finset.dvd_prod_of_mem (fun q : ℕ => q) hqmem
      have hq1 := Nat.modEq_zero_iff_dvd.mp ((hNB.of_dvd hqB).symm.trans hz)
      exact hq.ne_one (Nat.dvd_one.mp hq1)
  have hx : (x.val : ℤ) ≡ 3 [ZMOD (D : ℤ)] := Int.natCast_modEq_iff.mpr x.property.1
  have hy : (y.val : ℤ) ≡ 8 [ZMOD (D : ℤ)] := Int.natCast_modEq_iff.mpr y.property.1
  obtain ⟨hpos, hneg⟩ := archivedGaussianSigns_at_norm_73
  exact ⟨x.val, y.val, hcop.symm,
    (sign_modEq ⟨x.val, y.val⟩ ⟨3, 8⟩ hx hy).trans hpos,
    (sign_modEq ⟨x.val, -(y.val : ℤ)⟩ ⟨3, -8⟩ hx hy.neg).trans hneg⟩

/-- Any rational-norm formula for the actual conductor signs fails on
some representatives prime to the proposed modulus. -/
theorem archivedGaussianSign_not_of_norm (M : ℕ) (hM : M ≠ 0) :
    ¬ ∃ F : ℕ → ℤ, ∀ z : GaussianInt, z.norm.natAbs.Coprime M →
      archivedGaussianSign z = F z.norm.natAbs := by
  rintro ⟨F, hF⟩
  obtain ⟨x, y, hcop, hpos, hneg⟩ := exists_opposite_archived_signs_coprime_norm M hM
  let z : GaussianInt := ⟨x, y⟩
  let w : GaussianInt := ⟨x, -(y : ℤ)⟩
  have hz : z.norm.natAbs = x ^ 2 + y ^ 2 := by simp [z, GaussianInt.natAbs_norm_eq, pow_two]
  have hw : w.norm.natAbs = x ^ 2 + y ^ 2 := by simp [w, GaussianInt.natAbs_norm_eq, pow_two]
  have hp := hF z (hz.symm ▸ hcop)
  have hn := hF w (hw.symm ▸ hcop)
  change archivedGaussianSign z = _ at hpos
  change archivedGaussianSign w = _ at hneg
  rw [hz, hpos] at hp
  rw [hw, hneg] at hn
  linarith

#print axioms archivedGaussianSigns_at_norm_73
#print axioms exists_opposite_archived_signs_coprime_norm
#check archivedGaussianSign_not_of_norm
#print axioms archivedGaussianSign_not_of_norm

end QuarticModel
