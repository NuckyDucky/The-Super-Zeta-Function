import GaussianFrobeniusJetSeparation
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.FieldTheory.Finite.Basic

/-! A single integral Hermite polynomial gives the Frobenius power for every
prime in the same dyadic interval. -/

namespace AlpogeSuperZeta

open Finset Polynomial

noncomputable section

/-- A denominator for the consecutive-node Hermite interpolant. -/
def hermitePrimeScale (m : ℕ) : ℤ := ((m - 1).factorial : ℤ) ^ 2

private def hermiteNodeProduct (m j : ℕ) : ℤ[X] :=
  ∏ i ∈ (range m).erase j, (X - C (i : ℤ))

private def hermiteTerm (m j : ℕ) : ℤ[X] :=
  C (((m - 1).choose j : ℤ) ^ 2) * ((X - C (j : ℤ)) * hermiteNodeProduct m j ^ 2)

/-- At the nodes \(0,\ldots,m-1\) this polynomial takes the value
\(((m-1)!)^2 j\) and its derivative is zero. -/
def hermitePrimePolynomial (m : ℕ) : ℤ[X] :=
  C (hermitePrimeScale m) * X - ∑ j ∈ range m, hermiteTerm m j

private theorem consecutive_integer_product (m j : ℕ) (hj : j < m) :
    (∏ i ∈ (range m).erase j, ((j : ℤ) - (i : ℤ))) =
      (-1 : ℤ) ^ (m - 1 - j) * (j.factorial : ℤ) * ((m - 1 - j).factorial : ℤ) := by
  have hset : (range m).erase j = range j ∪ Ico (j + 1) m := by
    ext i
    simp only [mem_erase, mem_range, mem_union, mem_Ico]
    omega
  have hdisj : Disjoint (range j) (Ico (j + 1) m) := by
    refine disjoint_left.mpr fun i hl hr => ?_
    have h₁ := mem_range.mp hl
    have h₂ := (mem_Ico.mp hr).1
    omega
  have hleft : (∏ i ∈ range j, ((j : ℤ) - (i : ℤ))) = (j.factorial : ℤ) := by
    calc
      _ = ∏ i ∈ range j, ((j - 1 - i + 1 : ℕ) : ℤ) := by
        apply prod_congr rfl
        intro i hi
        have hi' := mem_range.mp hi
        have he : j - 1 - i + 1 = j - i := by omega
        rw [he, Nat.cast_sub hi'.le]
      _ = ∏ i ∈ range j, ((i + 1 : ℕ) : ℤ) :=
        prod_range_reflect (fun i : ℕ => ((i + 1 : ℕ) : ℤ)) j
      _ = _ := by rw [← Nat.cast_prod, Nat.factorial_eq_prod_range_add_one]
  have hright : (∏ i ∈ Ico (j + 1) m, ((j : ℤ) - (i : ℤ))) =
      (-1 : ℤ) ^ (m - 1 - j) * ((m - 1 - j).factorial : ℤ) := by
    rw [prod_Ico_eq_prod_range, show m - (j + 1) = m - 1 - j by omega]
    calc
      _ = ∏ i ∈ range (m - 1 - j), (-1 : ℤ) * ((i + 1 : ℕ) : ℤ) := by
        apply prod_congr rfl
        intro i _
        push_cast
        ring
      _ = _ := by rw [prod_mul_distrib, prod_const, card_range, ← Nat.cast_prod,
        Nat.factorial_eq_prod_range_add_one]
  rw [hset, prod_union hdisj, hleft, hright]
  ring

private theorem hermiteTerm_at_node {m j r : ℕ} (hj : j < m) (hr : r < m) :
    (hermiteTerm m j).eval (r : ℤ) = 0 ∧
      (hermiteTerm m j).derivative.eval (r : ℤ) = if r = j then hermitePrimeScale m else 0 := by
  by_cases h : r = j
  · subst r
    have hprod : (hermiteNodeProduct m j).eval (j : ℤ) =
        (-1 : ℤ) ^ (m - 1 - j) * (j.factorial : ℤ) * ((m - 1 - j).factorial : ℤ) := by
      simpa only [hermiteNodeProduct, eval_prod, eval_sub, eval_X, eval_C] using
        consecutive_integer_product m j hj
    have hsign : (((-1 : ℤ) ^ (m - 1 - j)) ^ 2) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    have hchoose := congrArg (fun n : ℕ => (n : ℤ))
      (Nat.choose_mul_factorial_mul_factorial (show j ≤ m - 1 by omega))
    push_cast at hchoose
    refine ⟨by simp [hermiteTerm], ?_⟩
    simp only [hermiteTerm, derivative_mul, derivative_C, zero_mul, zero_add,
      derivative_X_sub_C, one_mul, eval_mul, eval_C, eval_add, eval_pow, eval_sub,
      eval_X, sub_self, hprod, hermitePrimeScale, add_zero, if_true]
    calc
      _ = (((m - 1).choose j : ℤ) * (j.factorial : ℤ) * ((m - 1 - j).factorial : ℤ)) ^ 2 *
        (((-1 : ℤ) ^ (m - 1 - j)) ^ 2) := by ring
      _ = _ := by rw [hchoose, hsign, mul_one]
  · have hprod : (hermiteNodeProduct m j).eval (r : ℤ) = 0 := by
      simp only [hermiteNodeProduct, eval_prod, eval_sub, eval_X, eval_C]
      exact prod_eq_zero (mem_erase.mpr ⟨h, mem_range.mpr hr⟩) (sub_self _)
    constructor
    · simp [hermiteTerm, hprod]
    · simp [hermiteTerm, derivative_mul, derivative_pow, hprod, h]

theorem hermitePrimePolynomial_at_node {m r : ℕ} (hr : r < m) :
    (hermitePrimePolynomial m).eval (r : ℤ) = hermitePrimeScale m * (r : ℤ) ∧
      (hermitePrimePolynomial m).derivative.eval (r : ℤ) = 0 := by
  have he (j : ℕ) (hj : j ∈ range m) := hermiteTerm_at_node (mem_range.mp hj) hr
  constructor
  · unfold hermitePrimePolynomial
    simp only [eval_sub, eval_mul, eval_C, eval_X, eval_finsetSum]
    rw [sum_eq_zero (fun j hj => (he j hj).1), sub_zero]
  · unfold hermitePrimePolynomial
    simp only [derivative_sub, derivative_mul, derivative_C, derivative_X, zero_mul, zero_add,
      mul_one, derivative_sum, eval_sub, eval_C, eval_finsetSum]
    have hsum : (∑ j ∈ range m, (hermiteTerm m j).derivative.eval (r : ℤ)) =
        hermitePrimeScale m := by
      rw [sum_eq_single r]
      · simpa using (he r (mem_range.mpr hr)).2
      · intro j hj hne
        simpa [Ne.symm hne] using (he j hj).2
      · exact fun h => (h (mem_range.mpr hr)).elim
    rw [hsum, sub_self]

theorem hermitePrimePolynomial_degree {m : ℕ} (hm : 0 < m) :
    (hermitePrimePolynomial m).natDegree < 2 * m := by
  have hTerm (j : ℕ) (hj : j ∈ range m) : (hermiteTerm m j).natDegree ≤ 2 * m - 1 := by
    have hP : (hermiteNodeProduct m j).natDegree ≤ m - 1 := by
      unfold hermiteNodeProduct
      calc
        _ ≤ ∑ i ∈ (range m).erase j, (X - C (i : ℤ)).natDegree := natDegree_prod_le _ _
        _ = m - 1 := by
          have hsum : (∑ i ∈ (range m).erase j, (X - C (i : ℤ)).natDegree) =
              ((range m).erase j).card * 1 :=
            sum_const_nat (fun i _ => natDegree_X_sub_C (i : ℤ))
          rw [hsum, mul_one, card_erase_of_mem hj, card_range]
    unfold hermiteTerm
    refine (natDegree_C_mul_le _ _).trans (natDegree_mul_le.trans ?_)
    rw [natDegree_X_sub_C]
    have hpow : (hermiteNodeProduct m j ^ 2).natDegree ≤ 2 * (m - 1) :=
      natDegree_pow_le.trans (Nat.mul_le_mul_left 2 hP)
    omega
  unfold hermitePrimePolynomial
  have hMain : (C (hermitePrimeScale m) * X).natDegree ≤ 2 * m - 1 :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_le.trans (by omega))
  have hBound := natDegree_sub_le_of_le hMain (natDegree_sum_le_of_forall_le _ _ hTerm)
  rw [max_self] at hBound
  exact hBound.trans_lt (by omega)

private theorem polynomial_eq_zero_of_double_nodes {K ι : Type*} [Field K] [Fintype ι]
    (a : ι → K) (ha : Function.Injective a) (P : K[X]) (hdeg : P.natDegree < 2 * Fintype.card ι)
    (hval : ∀ i, P.eval (a i) = 0) (hder : ∀ i, P.derivative.eval (a i) = 0) : P = 0 := by
  classical
  by_contra hn
  have hmult (i : ι) : 2 ≤ P.rootMultiplicity (a i) := by
    have hdiv : (X : K[X]) ^ 2 ∣ P.taylor (a i) := by
      apply X_pow_dvd_iff.mpr
      intro j hj
      interval_cases j
      · rw [taylor_coeff_zero, hval i]
      · rw [taylor_coeff_one, hder i]
    obtain ⟨Q, hQ⟩ := hdiv
    have hs := congrArg (taylor (-(a i))) hQ
    rw [taylor_taylor, neg_add_cancel, taylor_zero, taylor_mul, taylor_pow, taylor_X,
      C_neg, ← sub_eq_add_neg] at hs
    exact (le_rootMultiplicity_iff hn).mpr ⟨Q.taylor (-(a i)), hs⟩
  let S : Finset K := univ.image a
  have hcard : S.card = Fintype.card ι := by
    change (univ.image a).card = _
    rw [card_image_of_injective univ ha, card_univ]
  have hcount : 2 • S.val ≤ P.roots := by
    apply Multiset.le_iff_count.mpr
    intro v
    rw [Multiset.count_nsmul, count_roots]
    by_cases hv : v ∈ S
    · obtain ⟨i, _, rfl⟩ := mem_image.mp hv
      rw [Multiset.count_eq_one_of_mem S.nodup (show a i ∈ S.val from hv)]
      simpa using hmult i
    · rw [Multiset.count_eq_zero.mpr (show v ∉ S.val from hv), mul_zero]
      exact Nat.zero_le _
  have hc := (Multiset.card_le_card hcount).trans (card_roots' P)
  rw [Multiset.card_nsmul] at hc
  change 2 * S.card ≤ P.natDegree at hc
  rw [hcard] at hc
  exact (not_le_of_gt hdeg) hc

/-- One polynomial works for every prime in \([m,2m)\),
with coefficients read in its characteristic. -/
theorem hermitePrimePolynomial_mod_prime {K : Type*} [Field K] {m p : ℕ}
    [CharP K p] (hp : p.Prime) (hm : m ≤ p) (hpm : p < 2 * m) :
    (hermitePrimePolynomial m).map (Int.castRingHom K) =
      C ((hermitePrimeScale m : ℤ) : K) * X ^ p := by
  let f := Int.castRingHom K
  let A := (hermitePrimePolynomial m).map f
  let B : K[X] := C ((hermitePrimeScale m : ℤ) : K) * X ^ p
  let g := ZMod.castHom (dvd_refl p) K
  let : Fact p.Prime := ⟨hp⟩
  have hNatPow (n : ℕ) : (n : K) ^ p = (n : K) := by
    simpa only [map_pow, map_natCast] using congrArg g (ZMod.pow_card (n : ZMod p))
  have hinj : Function.Injective (fun i : Fin m => (i.val : K)) := by
    intro i j hij
    have he : (i.val : ZMod p) = (j.val : ZMod p) :=
      g.injective (by simpa only [map_natCast] using hij)
    apply Fin.ext
    simpa only [ZMod.val_natCast_of_lt (i.isLt.trans_le hm),
      ZMod.val_natCast_of_lt (j.isLt.trans_le hm)] using congrArg ZMod.val he
  apply sub_eq_zero.mp
  change A - B = 0
  apply polynomial_eq_zero_of_double_nodes (fun i : Fin m => (i.val : K)) hinj
  · rw [Fintype.card_fin]
    refine (natDegree_sub_le _ _).trans_lt (max_lt ?_ ?_)
    · exact natDegree_map_le.trans_lt (hermitePrimePolynomial_degree (by omega))
    · exact (natDegree_C_mul_le _ _).trans_lt ((natDegree_X_pow p).le.trans_lt hpm)
  · intro i
    have hv := (hermitePrimePolynomial_at_node i.isLt).1
    have hr : (i.val : K) = f (i.val : ℤ) := by simp [f]
    have hA : A.eval (i.val : K) = (hermitePrimeScale m : K) * (i.val : K) := by
      rw [hr, show A = _ from rfl, eval_map_apply, hv, map_mul]
      rfl
    simp only [eval_sub, B, eval_mul, eval_C, eval_pow, eval_X, hNatPow, hA, sub_self]
  · intro i
    have hd := (hermitePrimePolynomial_at_node i.isLt).2
    have hr : (i.val : K) = f (i.val : ℤ) := by simp [f]
    have hA : A.derivative.eval (i.val : K) = 0 := by
      dsimp only [A]
      rw [hr, derivative_map, eval_map_apply, hd, map_zero]
    simp [B, derivative_mul, derivative_X_pow, hA]

theorem hermitePrimePolynomial_X_sq_dvd {m : ℕ} (hm : 0 < m) :
    (X : ℤ[X]) ^ 2 ∣ hermitePrimePolynomial m := by
  have ⟨hv, hd⟩ := hermitePrimePolynomial_at_node (r := 0) hm
  apply X_pow_dvd_iff.mpr
  intro j hj
  interval_cases j
  · simpa using (taylor_coeff_zero (r := (0 : ℤ)) (f := hermitePrimePolynomial m)).trans (by simpa using hv)
  · simpa using (taylor_coeff_one (r := (0 : ℤ)) (f := hermitePrimePolynomial m)).trans (by simpa using hd)

#print axioms hermitePrimePolynomial_at_node
#print axioms hermitePrimePolynomial_degree
#print axioms hermitePrimePolynomial_mod_prime
#print axioms hermitePrimePolynomial_X_sq_dvd

end
end AlpogeSuperZeta
