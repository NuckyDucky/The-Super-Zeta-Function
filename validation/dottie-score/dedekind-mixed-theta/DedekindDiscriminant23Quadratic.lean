import DedekindDiscriminant23Field
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.LinearCombination

namespace FieldTarget

open Polynomial

local notation "L" => Discriminant23GaloisField

private theorem cubic_roots_in_L_card : Fintype.card (discriminant23Cubic.rootSet L) = 3 := by
  classical
  have hdeg : discriminant23Cubic.natDegree = 3 := by
    unfold discriminant23Cubic
    have h : ((X : ℚ[X]) ^ 3 - X).natDegree = 3 := by
      rw [natDegree_sub_eq_left_of_natDegree_lt (by simp), natDegree_X_pow]
    rw [natDegree_sub_eq_left_of_natDegree_lt (by simp [h]), h]
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup, ← Splits.natDegree_eq_card_roots, natDegree_map, hdeg]
  · exact SplittingField.splits discriminant23Cubic
  · exact nodup_roots ((separable_map (algebraMap ℚ L)).mpr discriminant23Cubic_irreducible.separable)

/-- The Vandermonde product of the cubic roots gives a square root of `-23`
in the actual splitting field. -/
theorem exists_discriminant23_square_root : ∃ v : L, v ^ 2 = -23 := by
  classical
  let : Nontrivial (discriminant23Cubic.rootSet L) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by rw [cubic_roots_in_L_card]; decide)
  obtain ⟨a, b, hab⟩ := exists_pair_ne (α := discriminant23Cubic.rootSet L)
  have ha : (a.val : L) ^ 3 - a.val - 1 = 0 := by
    simpa [discriminant23Cubic] using aeval_eq_zero_of_mem_rootSet a.property
  have hb : (b.val : L) ^ 3 - b.val - 1 = 0 := by
    simpa [discriminant23Cubic] using aeval_eq_zero_of_mem_rootSet b.property
  have hne : (a.val : L) - b.val ≠ 0 := sub_ne_zero.mpr fun h ↦ hab (Subtype.ext h)
  have hprod : (a.val - b.val) * (a.val ^ 2 + a.val * b.val + b.val ^ 2 - 1) = 0 := by
    linear_combination ha - hb
  have hsum : a.val ^ 2 + a.val * b.val + b.val ^ 2 = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hne)
  let c : L := -a.val - b.val
  have h1 : (a.val - b.val) * (a.val - c) = 3 * a.val ^ 2 - 1 := by
    dsimp [c]
    linear_combination -hsum
  have h2 : (b.val - c) ^ 2 = 4 - 3 * a.val ^ 2 := by
    dsimp [c]
    linear_combination 4 * hsum
  refine ⟨(a.val - b.val) * (a.val - c) * (b.val - c), ?_⟩
  rw [mul_pow, h1, h2]
  calc
    (3 * a.val ^ 2 - 1) ^ 2 * (4 - 3 * a.val ^ 2) =
        4 - 27 * (a.val ^ 3 - a.val) ^ 2 := by ring
    _ = -23 := by rw [sub_eq_zero.mp ha]; norm_num

noncomputable def discriminant23Quadratic : ℚ[X] := X ^ 2 + C 23

theorem discriminant23Quadratic_natDegree : discriminant23Quadratic.natDegree = 2 := by
  unfold discriminant23Quadratic
  rw [natDegree_add_eq_left_of_natDegree_lt (by simp), natDegree_X_pow]

theorem discriminant23Quadratic_irreducible : Irreducible discriminant23Quadratic := by
  apply irreducible_of_degree_le_three_of_not_isRoot (by simp [discriminant23Quadratic_natDegree])
  intro x hx
  have h : x ^ 2 + 23 = 0 := by simpa [IsRoot, discriminant23Quadratic] using hx
  nlinarith [sq_nonneg x]

instance discriminant23Quadratic_irreducible_fact : Fact (Irreducible discriminant23Quadratic) :=
  ⟨discriminant23Quadratic_irreducible⟩

abbrev Discriminant23QuadraticField := AdjoinRoot discriminant23Quadratic

noncomputable def discriminant23QuadraticEmbedding : Discriminant23QuadraticField →ₐ[ℚ] L := by
  classical
  let v := Classical.choose exists_discriminant23_square_root
  have hv : v ^ 2 = -23 := Classical.choose_spec exists_discriminant23_square_root
  refine AdjoinRoot.liftAlgHom _ (Algebra.ofId ℚ L) v ?_
  simp [discriminant23Quadratic, hv]

noncomputable def discriminant23QuadraticSubfield : IntermediateField ℚ L :=
  discriminant23QuadraticEmbedding.fieldRange

noncomputable def discriminant23QuadraticEquiv :
    Discriminant23QuadraticField ≃ₐ[ℚ] discriminant23QuadraticSubfield :=
  AlgEquiv.ofBijective discriminant23QuadraticEmbedding.rangeRestrict
    ⟨RingHom.injective _, AlgHom.rangeRestrict_surjective _⟩

theorem discriminant23QuadraticSubfield_finrank :
    Module.finrank ℚ discriminant23QuadraticSubfield = 2 := by
  rw [← discriminant23QuadraticEquiv.toLinearEquiv.finrank_eq]
  exact finrank_quotient_span_eq_natDegree.trans discriminant23Quadratic_natDegree

theorem discriminant23_galois_field_finrank : Module.finrank ℚ L = 6 := by
  obtain ⟨e⟩ := discriminant23_galois_group
  rw [← IsGalois.card_aut_eq_finrank, Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card,
    Fintype.card_perm, Fintype.card_fin]
  decide +kernel

theorem discriminant23_relative_finrank :
    Module.finrank discriminant23QuadraticSubfield L = 3 := by
  have h := Module.finrank_mul_finrank ℚ discriminant23QuadraticSubfield L
  rw [discriminant23QuadraticSubfield_finrank, discriminant23_galois_field_finrank] at h
  omega

theorem discriminant23_relative_galois_cyclic :
    IsCyclic (L ≃ₐ[discriminant23QuadraticSubfield] L) := by
  let : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
  apply isCyclic_of_prime_card (p := 3)
  rw [IsGalois.card_aut_eq_finrank, discriminant23_relative_finrank]

#check @exists_discriminant23_square_root
#check @discriminant23QuadraticEquiv
#check @discriminant23_relative_galois_cyclic
#print axioms exists_discriminant23_square_root
#print axioms discriminant23QuadraticEquiv
#print axioms discriminant23_relative_galois_cyclic

end FieldTarget
