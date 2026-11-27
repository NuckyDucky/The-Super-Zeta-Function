import DedekindCyclicEulerCoefficients
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.NumberTheory.Divisors

namespace FieldTarget

open scoped NumberField BigOperators Classical
open IsDedekindDomain

private theorem weighted_degree_multiplicity
    {α : Type*} [Fintype α] (degree : α → ℕ) (weight : α → ℤ) (total : ℤ)
    (hpositive : ∀ i, degree i ≠ 0)
    (hcoeff : ∀ n ≠ 0,
      (∑ i, if degree i ∣ n then (degree i : ℤ) * weight i else 0) = total) (d : ℕ) :
    (∑ i, if degree i = d then weight i else 0) = if d = 1 then total else 0 := by
  classical
  let c : ℕ → ℤ := fun j ↦ ∑ i, if degree i = j then weight i else 0
  change c d = _
  have hsum (n : ℕ) (hn : n ≠ 0) : (∑ j ∈ n.divisors, (j : ℤ) * c j) = total := by
    simp only [c, Finset.mul_sum, mul_ite, mul_zero]
    rw [Finset.sum_comm, ← hcoeff n hn]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.sum_ite_eq, Nat.mem_divisors]
    simp only [and_iff_left hn]
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d = 0
    · subst d
      simp [c, hpositive]
    by_cases hd1 : d = 1
    · subst d
      simpa using hsum 1 (by decide)
    have hsplit := Finset.sum_erase_add d.divisors (fun j ↦ (j : ℤ) * c j)
      (Nat.mem_divisors_self d hd)
    have hrest : (∑ j ∈ d.divisors.erase d, (j : ℤ) * c j) = total := by
      rw [Finset.sum_eq_single 1]
      · simp [ih 1 (by omega : 1 < d)]
      · intro j hj hj1
        have hlt : j < d := lt_of_le_of_ne
          (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) (Nat.dvd_of_mem_divisors
            (Finset.mem_erase.mp hj).2)) (Finset.mem_erase.mp hj).1
        simp [ih j hlt, hj1]
      · intro h
        exact (h (by simp [hd, Ne.symm hd1])).elim
    rw [hrest, hsum d hd] at hsplit
    have hzero : (d : ℤ) * c d = 0 := add_left_cancel (hsplit.trans (add_zero total).symm)
    simp only [hd1, ite_false]
    exact (mul_eq_zero.mp hzero).resolve_left (by exact_mod_cast hd)

private theorem zpow_finset_sum {α A : Type*} [CommGroup A] (s : Finset α)
    (a : A) (e : α → ℤ) : a ^ (∑ i ∈ s, e i) = ∏ i ∈ s, a ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

private theorem weighted_product_of_degree_coefficients
    {α A : Type*} [Fintype α] [CommGroup A]
    (degree : α → ℕ) (weight : α → ℤ) (total : ℤ)
    (hpositive : ∀ i, degree i ≠ 0)
    (hcoeff : ∀ n ≠ 0,
      (∑ i, if degree i ∣ n then (degree i : ℤ) * weight i else 0) = total)
    (u : ℕ → A) : (∏ i, u (degree i) ^ weight i) = u 1 ^ total := by
  classical
  let D := insert 1 (Finset.univ.image degree)
  calc
    _ = ∏ j ∈ D, ∏ i ∈ Finset.univ with degree i = j, u (degree i) ^ weight i := by
      symm
      apply Finset.prod_fiberwise_of_maps_to
      intro i hi
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem degree hi)
    _ = ∏ j ∈ D, u j ^ (∑ i, if degree i = j then weight i else 0) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [← Finset.sum_filter, zpow_finset_sum]
      exact Finset.prod_congr rfl (fun i hi ↦ by rw [(Finset.mem_filter.mp hi).2])
    _ = _ := by
      simp_rw [weighted_degree_multiplicity degree weight total hpositive hcoeff]
      rw [Finset.prod_eq_single 1]
      · rw [ite_eq_left rfl]
      · intro j _ hj
        simp [hj]
      · exact fun h ↦ (h (Finset.mem_insert_self ..)).elim

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- At an unramified prime, the same cyclic fixed-field weights recover the
base Euler factor with multiplicity the order of the Galois group.
The function `u` assigns an invertible factor to each residue degree. -/
theorem exists_weighted_unramified_local_factor_product :
    ∃ a : CyclicSubgroups Gal(L/K) → ℤ,
      ∀ (p : HeightOneSpectrum (𝓞 K)) (P : HeightOneSpectrum (𝓞 L)),
        P.asIdeal.LiesOver p.asIdeal → Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal →
        ∀ {A : Type} [CommGroup A] (u : ℕ → A),
          (∏ H : CyclicSubgroups Gal(L/K),
            (∏ Q : p.asIdeal.primesOver (𝓞 (IntermediateField.fixedField H.val)),
              u (Q.val.inertiaDeg (𝓞 K))) ^ a H) =
              u 1 ^ (Nat.card Gal(L/K) : ℤ) := by
  classical
  obtain ⟨a, ha⟩ := exists_weighted_unramified_prime_power_match (K := K) (L := L)
  refine ⟨a, ?_⟩
  intro p P hP hu A _ u
  let I := Σ H : CyclicSubgroups Gal(L/K),
    p.asIdeal.primesOver (𝓞 (IntermediateField.fixedField H.val))
  let degree : I → ℕ := fun i ↦ i.2.val.inertiaDeg (𝓞 K)
  let weight : I → ℤ := fun i ↦ a i.1
  have hpositive (i : I) : degree i ≠ 0 :=
    (i.2.val.inertiaDeg_pos (𝓞 K)).ne'
  have hcoeff (n : ℕ) (_ : n ≠ 0) :
      (∑ i : I, if degree i ∣ n then (degree i : ℤ) * weight i else 0) =
        (Nat.card Gal(L/K) : ℤ) := by
    rw [Fintype.sum_sigma, ← ha p P hP hu n]
    apply Finset.sum_congr rfl
    intro H _
    rw [primePowerResidueCount, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Q _
    dsimp [degree, weight]
    by_cases h : Q.val.inertiaDeg (𝓞 K) ∣ n <;> simp [h, mul_comm]
  have hprod := weighted_product_of_degree_coefficients degree weight _ hpositive hcoeff u
  change (∏ i : (Σ H : CyclicSubgroups Gal(L/K),
    p.asIdeal.primesOver (𝓞 (IntermediateField.fixedField H.val))),
      u (i.2.val.inertiaDeg (𝓞 K)) ^ a i.1) = _ at hprod
  rw [Fintype.prod_sigma] at hprod
  simpa only [Finset.prod_zpow] using hprod

#check @exists_weighted_unramified_local_factor_product
#print axioms exists_weighted_unramified_local_factor_product

end FieldTarget
