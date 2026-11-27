import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Tactic.Linarith

namespace FieldTarget

open Polynomial

private theorem cubic_root_bounds (x : ℝ) (hx : x ^ 3 - x - 1 = 0) :
    1 < x ∧ x < 2 := by
  constructor
  · by_contra! hle
    by_cases hneg : x ≤ -1
    · have hxy := mul_nonneg_of_nonpos_of_nonpos (show x - 1 ≤ 0 by linarith)
        (show x + 1 ≤ 0 by linarith)
      have hprod := mul_nonneg (show 0 ≤ -x by linarith)
        (show 0 ≤ x ^ 2 - 1 by nlinarith only [hxy])
      nlinarith only [hprod, hx]
    · have hgt : -1 < x := lt_of_not_ge hneg
      by_cases hzero : x ≤ 0
      · have hcube := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hzero
        nlinarith only [hgt, hcube, hx]
      · have hxy := mul_nonneg (sub_nonneg.mpr hle) (show 0 ≤ 1 + x by linarith)
        have hprod := mul_nonneg (show 0 ≤ x by linarith [lt_of_not_ge hzero])
          (show 0 ≤ 1 - x ^ 2 by nlinarith only [hxy])
        nlinarith only [hprod, hx]
  · by_contra! hge
    have hprod := mul_nonneg (sub_nonneg.mpr hge)
      (show 0 ≤ x ^ 2 + 2 * x + 3 by nlinarith [sq_nonneg x])
    nlinarith only [hprod, hx]

private theorem cubic_real_roots_eq {x y : ℝ} (hx : x ^ 3 - x - 1 = 0)
    (hy : y ^ 3 - y - 1 = 0) : x = y := by
  have hxl := (cubic_root_bounds x hx).1
  have hyl := (cubic_root_bounds y hy).1
  have hprod : (x - y) * (x ^ 2 + x * y + y ^ 2 - 1) = 0 := by nlinarith only [hx, hy]
  have hsq := mul_pos (show 0 < x - 1 by linarith) (show 0 < x + 1 by linarith)
  have hquad : 0 < x ^ 2 + x * y + y ^ 2 - 1 := by
    nlinarith only [hsq, mul_nonneg (by linarith : 0 ≤ x) (by linarith : 0 ≤ y), sq_nonneg y]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hquad.ne')

/-- The cubic whose splitting field is the discriminant-23 example. -/
noncomputable def discriminant23Cubic : ℚ[X] := X ^ 3 - X - 1

private theorem cubic_degree : discriminant23Cubic.natDegree = 3 := by
  unfold discriminant23Cubic
  have h₁ : ((X : ℚ[X]) ^ 3 - X).natDegree = 3 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simp), natDegree_X_pow]
  rw [natDegree_sub_eq_left_of_natDegree_lt (by simp [h₁]), h₁]

private theorem cubic_monic_int : ((X : ℤ[X]) ^ 3 - X - 1).Monic := by
  have h₁ : ((X : ℤ[X]) ^ 3 - X).Monic := (monic_X.pow _).sub_of_left (by simp)
  have h₂ : ((X : ℤ[X]) ^ 3 - X).degree = 3 := by
    rw [degree_sub_eq_left_of_degree_lt (by simp), degree_X_pow]
    norm_num
  exact h₁.sub_of_left (by simp [h₂])

theorem discriminant23Cubic_irreducible : Irreducible discriminant23Cubic := by
  apply irreducible_of_degree_le_three_of_not_isRoot (by simp [cubic_degree])
  intro x hx
  have hxq : x ^ 3 - x - 1 = 0 := by
    simpa [IsRoot, discriminant23Cubic] using hx
  have hxz : aeval x ((X : ℤ[X]) ^ 3 - X - 1) = 0 := by simpa using hxq
  obtain ⟨z, hz⟩ := isInteger_of_is_root_of_monic cubic_monic_int hxz
  have hxr : (x : ℝ) ^ 3 - (x : ℝ) - 1 = 0 := by exact_mod_cast hxq
  obtain ⟨hl, hu⟩ := cubic_root_bounds _ hxr
  have hcast : (z : ℚ) = x := by simpa using hz
  rw [← hcast] at hl hu
  have hz1 : (1 : ℤ) < z := by exact_mod_cast hl
  have hz2 : z < (2 : ℤ) := by exact_mod_cast hu
  omega

private theorem cubic_complex_card : Fintype.card (discriminant23Cubic.rootSet ℂ) = 3 := by
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup, ← Splits.natDegree_eq_card_roots, natDegree_map, cubic_degree]
  · exact IsAlgClosed.splits _
  · exact nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr discriminant23Cubic_irreducible.separable)

private theorem cubic_real_card_le : Fintype.card (discriminant23Cubic.rootSet ℝ) ≤ 1 := by
  apply Fintype.card_le_one_iff.mpr
  intro x y
  apply Subtype.ext
  have hx := (mem_rootSet_of_ne discriminant23Cubic_irreducible.ne_zero).mp x.property
  have hy := (mem_rootSet_of_ne discriminant23Cubic_irreducible.ne_zero).mp y.property
  exact cubic_real_roots_eq (by simpa [discriminant23Cubic] using hx)
    (by simpa [discriminant23Cubic] using hy)

abbrev Discriminant23GaloisField := discriminant23Cubic.SplittingField

instance discriminant23_numberField : NumberField Discriminant23GaloisField where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

instance discriminant23_isGalois : IsGalois ℚ Discriminant23GaloisField :=
  IsGalois.of_separable_splitting_field discriminant23Cubic_irreducible.separable

theorem discriminant23_galois_group :
    Nonempty ((Discriminant23GaloisField ≃ₐ[ℚ] Discriminant23GaloisField) ≃*
      Equiv.Perm (Fin 3)) := by
  have hreal := cubic_real_card_le
  have h := Gal.galActionHom_bijective_of_prime_degree' discriminant23Cubic_irreducible
    (by rw [cubic_degree]; decide +kernel)
    (by rw [cubic_complex_card]; omega)
    (by rw [cubic_complex_card]; omega)
  let e := Fintype.equivFinOfCardEq cubic_complex_card
  let c : Equiv.Perm (discriminant23Cubic.rootSet ℂ) ≃* Equiv.Perm (Fin 3) :=
    { e.permCongr with
      map_mul' := fun f g ↦ by
        apply Equiv.ext
        intro x
        change e (f (g (e.symm x))) = e (f (e.symm (e (g (e.symm x)))))
        rw [Equiv.symm_apply_apply] }
  exact ⟨(MulEquiv.ofBijective _ h).trans c⟩

theorem discriminant23_galois_nonabelian : ¬ IsAbelianGalois ℚ Discriminant23GaloisField := by
  intro hA
  let : IsAbelianGalois ℚ Discriminant23GaloisField := hA
  obtain ⟨e⟩ := discriminant23_galois_group
  have hnc : Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠
      Equiv.swap 1 2 * Equiv.swap 0 1 := by decide +kernel
  apply hnc
  obtain ⟨a, ha⟩ := e.surjective (Equiv.swap (0 : Fin 3) 1)
  obtain ⟨b, hb⟩ := e.surjective (Equiv.swap (1 : Fin 3) 2)
  simpa only [map_mul, ha, hb] using congrArg e (mul_comm' a b)

#check discriminant23_galois_group
#print axioms discriminant23_galois_group
#print axioms discriminant23_galois_nonabelian

end FieldTarget
