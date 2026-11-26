import GaussianFrobeniusJetScaffold
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

/-! Separation of the triangular rows by residue readings. The
derivative orders are Hasse coefficients from the first coordinate. -/

namespace AlpogeSuperZeta

open Finset Polynomial

noncomputable section

private theorem polynomial_eq_zero_of_eval_family {K ι : Type*} [CommRing K] [IsDomain K]
    [Fintype ι] (a : ι → K) (ha : Function.Injective a) {P : Polynomial K}
    (hDeg : P.natDegree < Fintype.card ι) (h : ∀ i, P.eval (a i) = 0) : P = 0 := by
  classical
  by_contra hP
  let Z : Finset K := univ.image a
  have hCard : Z.card = Fintype.card ι := by
    rw [card_image_of_injective univ ha, card_univ]
  have hRoots : Z.val ⊆ P.roots := by
    intro y hy
    have hy' : y ∈ Z := hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hy'
    exact (Polynomial.mem_roots hP).2 (h i)
  have hBound := Polynomial.card_le_degree_of_subset_roots hRoots
  rw [hCard] at hBound
  exact (not_le_of_gt hDeg) hBound

private theorem polynomial_eq_zero_of_all_taylor_coeffs {K : Type*} [Field K] [Fintype K]
    {P : Polynomial K} {J : ℕ} (hDeg : P.natDegree < Fintype.card K * J)
    (h : ∀ a j, j < J → (P.taylor a).coeff j = 0) : P = 0 := by
  classical
  by_contra hP
  have hMult (a : K) : J ≤ P.rootMultiplicity a := by
    have hd : (Polynomial.X : Polynomial K) ^ J ∣ P.taylor a := Polynomial.X_pow_dvd_iff.2 (h a)
    obtain ⟨Q, hQ⟩ := hd
    have hQ' := congrArg (Polynomial.taylor (-a)) hQ
    rw [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero,
      Polynomial.taylor_mul, Polynomial.taylor_pow, Polynomial.taylor_X, Polynomial.C_neg,
      ← sub_eq_add_neg] at hQ'
    exact (Polynomial.le_rootMultiplicity_iff hP).2 ⟨Q.taylor (-a), hQ'⟩
  have hCount : J • (univ : Finset K).val ≤ P.roots := by
    apply Multiset.le_iff_count.mpr
    intro a
    rw [Multiset.count_nsmul, Polynomial.count_roots]
    simpa using hMult a
  have hc := (Multiset.card_le_card hCount).trans (Polynomial.card_roots' P)
  rw [Multiset.card_nsmul] at hc
  change J * (univ : Finset K).card ≤ P.natDegree at hc
  rw [card_univ, mul_comm] at hc
  exact (not_le_of_gt hDeg) hc

private theorem taylor_monomial_coeff {K : Type*} [CommRing K] (a c : K) (r j : ℕ) :
    ((Polynomial.monomial r c).taylor a).coeff j = c * monomialJet r j a := by
  rw [Polynomial.taylor_coeff, Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  simp only [monomialJet]
  ring

private def rowPolynomial {K Rows : Type*} [CommRing K] [Fintype Rows]
    (degree : Rows → ℕ × ℕ) (c : Rows → K) : Polynomial (Polynomial K) :=
  ∑ i, Polynomial.monomial (degree i).1 (Polynomial.monomial (degree i).2 (c i))

private theorem rowPolynomial_coeff_coeff {K Rows : Type*} [CommRing K] [Fintype Rows]
    (degree : Rows → ℕ × ℕ) (hd : Function.Injective degree) (c : Rows → K) (i : Rows) :
    (((rowPolynomial degree c).coeff (degree i).1).coeff (degree i).2) = c i := by
  classical
  simp only [rowPolynomial, Polynomial.finsetSum_coeff]
  rw [sum_eq_single i]
  · simp
  · intro l _ hl
    rw [Polynomial.coeff_monomial]
    by_cases hFirst : (degree l).1 = (degree i).1
    · have hSecond : (degree l).2 ≠ (degree i).2 := fun h => hl (hd (Prod.ext hFirst h))
      simp [hFirst, Polynomial.coeff_monomial, hSecond]
    · simp [hFirst]
  · simp

/-- A full grid with enough first-coordinate Taylor readings separates
any finite set of distinct monomial rows under these degree bounds. -/
theorem frobeniusJets_grid_separate {K Rows : Type*} [Field K] [Fintype K] [Fintype Rows]
    (degree : Rows → ℕ × ℕ) (hd : Function.Injective degree) {J : ℕ}
    (hFirst : ∀ i, (degree i).1 < Fintype.card K * J)
    (hSecond : ∀ i, (degree i).2 < Fintype.card K)
    (c : Rows → K)
    (h : ∀ a b : K, ∀ j < J,
      (∑ i, c i * (monomialJet (degree i).1 j a * b ^ (degree i).2)) = 0) : c = 0 := by
  classical
  by_cases hJ : J = 0
  · subst J
    exact funext fun i => (Nat.not_lt_zero ((degree i).1) (by simpa using hFirst i)).elim
  let Q := rowPolynomial degree c
  let F (b : K) := Q.map (Polynomial.evalRingHom b)
  have hF (b : K) : F b = ∑ i, Polynomial.monomial (degree i).1 (c i * b ^ (degree i).2) := by
    change Polynomial.mapRingHom (Polynomial.evalRingHom b)
      (∑ i, Polynomial.monomial (degree i).1 (Polynomial.monomial (degree i).2 (c i))) = _
    rw [map_sum]
    refine sum_congr rfl fun i _ => ?_
    change (Polynomial.monomial (degree i).1 (Polynomial.monomial (degree i).2 (c i))).map
      (Polynomial.evalRingHom b) = _
    rw [Polynomial.map_monomial]
    congr 1
    exact Polynomial.eval_monomial
  have hZero (b : K) : F b = 0 := by
    apply polynomial_eq_zero_of_all_taylor_coeffs (J := J)
    · rw [hF]
      have hq : 0 < Fintype.card K * J := Nat.mul_pos Fintype.card_pos (Nat.pos_of_ne_zero hJ)
      apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := Fintype.card K * J - 1) ?_)
        (by omega)
      intro i _
      exact (Polynomial.natDegree_monomial_le _).trans (by have := hFirst i; omega)
    · intro a j hj
      rw [hF]
      simp only [map_sum, Polynomial.finsetSum_coeff, taylor_monomial_coeff]
      simpa only [mul_assoc, mul_left_comm, mul_comm] using h a b j hj
  have hPoly : Q = 0 := by
    apply Polynomial.ext
    intro r
    apply polynomial_eq_zero_of_eval_family (a := id) Function.injective_id
    · have hq : 0 < Fintype.card K := Fintype.card_pos
      simp only [Q, rowPolynomial, Polynomial.finsetSum_coeff]
      apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := Fintype.card K - 1) ?_)
        (by omega)
      intro i _
      by_cases hir : (degree i).1 = r
      · rw [Polynomial.coeff_monomial, if_pos hir]
        exact (Polynomial.natDegree_monomial_le _).trans (by have := hSecond i; omega)
      · simp [Polynomial.coeff_monomial, hir]
    · intro b
      change Polynomial.evalRingHom b (Q.coeff r) = 0
      have hh := congrArg (fun P : Polynomial K => P.coeff r) (hZero b)
      simpa only [F, Polynomial.coeff_map, Polynomial.coeff_zero] using hh
  funext i
  rw [← rowPolynomial_coeff_coeff degree hd c i]
  simp [show rowPolynomial degree c = 0 from hPoly]

/-- Diagonal readings also separate when the field size exceeds the
total row degrees and the jet count exceeds the second-coordinate degree. -/
theorem frobeniusJets_diagonal_separate {K Rows : Type*} [Field K] [Fintype K] [Fintype Rows]
    (degree : Rows → ℕ × ℕ) (hd : Function.Injective degree) {J : ℕ}
    (hTotal : ∀ i, (degree i).1 + (degree i).2 < Fintype.card K)
    (hSecond : ∀ i, (degree i).2 < J)
    (c : Rows → K)
    (h : ∀ a : K, ∀ j < J,
      (∑ i, c i * (monomialJet (degree i).1 j a * a ^ (degree i).2)) = 0) : c = 0 := by
  classical
  by_cases hJ : J = 0
  · subst J
    exact funext fun i => (Nat.not_lt_zero _ (hSecond i)).elim
  let Q := rowPolynomial degree c
  let G := Q.taylor (Polynomial.X : Polynomial K)
  have hG (j : ℕ) : G.coeff j = ∑ i,
      Polynomial.monomial (degree i).2 (c i) * monomialJet (degree i).1 j Polynomial.X := by
    simp only [G, Q, rowPolynomial, map_sum, Polynomial.finsetSum_coeff, taylor_monomial_coeff]
  have hGC (j : ℕ) (hj : j < J) : G.coeff j = 0 := by
    apply polynomial_eq_zero_of_eval_family (a := id) Function.injective_id
    · rw [hG]
      have hq : 0 < Fintype.card K := Fintype.card_pos
      apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := Fintype.card K - 1) ?_)
        (by omega)
      intro i _
      simp only [monomialJet]
      have hdeg : (Polynomial.monomial (degree i).2 (c i) *
          ((Nat.choose (degree i).1 j : Polynomial K) * Polynomial.X ^ ((degree i).1 - j))).natDegree ≤
            (degree i).2 + ((degree i).1 - j) := by
        apply (Polynomial.natDegree_mul_le ..).trans
        apply Nat.add_le_add (Polynomial.natDegree_monomial_le _)
        exact (Polynomial.natDegree_mul_le ..).trans (by simp)
      exact hdeg.trans (by have := hTotal i; omega)
    · intro a
      change (G.coeff j).eval a = 0
      rw [hG, Polynomial.eval_finsetSum]
      simpa only [monomialJet, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_natCast,
        Polynomial.eval_X, Polynomial.eval_monomial, mul_assoc, mul_left_comm, mul_comm] using h a j hj
  have hDvd : (Polynomial.X : Polynomial (Polynomial K)) ^ J ∣ G :=
    Polynomial.X_pow_dvd_iff.2 hGC
  have hEval (a : K) : Q.eval (Polynomial.C a) = 0 := by
    have ht : (Polynomial.C a - Polynomial.X) ^ J ∣ Q.eval (Polynomial.C a) := by
      obtain ⟨Q₁, hQ₁⟩ := hDvd
      refine ⟨Q₁.eval (Polynomial.C a - Polynomial.X), ?_⟩
      calc
        _ = G.eval (Polynomial.C a - Polynomial.X) :=
          (Polynomial.taylor_eval_sub (Polynomial.X : Polynomial K) Q (Polynomial.C a)).symm
        _ = _ := by rw [hQ₁, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    by_contra he
    have hs := Polynomial.natDegree_le_of_dvd ht he
    have hDegree₁ : (Polynomial.C a - Polynomial.X).natDegree = 1 := by
      rw [← neg_sub, Polynomial.natDegree_neg, Polynomial.natDegree_X_sub_C]
    rw [Polynomial.natDegree_pow, hDegree₁, mul_one] at hs
    have hDegree : (Q.eval (Polynomial.C a)).natDegree < J := by
      simp only [Q, rowPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
      apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := J - 1) ?_) (by omega)
      intro i _
      have hdeg : (Polynomial.monomial (degree i).2 (c i) *
          Polynomial.C a ^ (degree i).1).natDegree ≤ (degree i).2 := by
        rw [← map_pow, Polynomial.monomial_mul_C]
        exact Polynomial.natDegree_monomial_le _
      exact hdeg.trans (by have := hSecond i; omega)
    exact (not_le_of_gt hDegree) hs
  have hZero : Q = 0 := by
    apply polynomial_eq_zero_of_eval_family (a := Polynomial.C) Polynomial.C_injective
    · have hq : 0 < Fintype.card K := Fintype.card_pos
      simp only [Q, rowPolynomial]
      apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := Fintype.card K - 1) ?_)
        (by omega)
      intro i _
      exact (Polynomial.natDegree_monomial_le _).trans (by have := hTotal i; omega)
    · exact hEval
  funext i
  rw [← rowPolynomial_coeff_coeff degree hd c i]
  simp [show rowPolynomial degree c = 0 from hZero]

/-- Values alone separate rows on the power graph when the substituted
exponents are distinct and below the field cardinality. -/
theorem frobeniusValues_powerGraph_separate {K Rows : Type*} [Field K] [Fintype K] [Fintype Rows]
    (degree : Rows → ℕ × ℕ) (d : ℕ)
    (hd : Function.Injective fun r => (degree r).1 + d * (degree r).2)
    (hDeg : ∀ r, (degree r).1 + d * (degree r).2 < Fintype.card K)
    (c : Rows → K)
    (h : ∀ a : K, (∑ r, c r * (monomialJet (degree r).1 0 a * (a ^ d) ^ (degree r).2)) = 0) :
    c = 0 := by
  classical
  let e (r : Rows) := (degree r).1 + d * (degree r).2
  let Q : Polynomial K := ∑ r, Polynomial.monomial (e r) (c r)
  have hZero : Q = 0 := by
    apply polynomial_eq_zero_of_eval_family (a := id) Function.injective_id
    · have hq : 0 < Fintype.card K := Fintype.card_pos
      apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := Fintype.card K - 1) ?_)
        (by omega)
      intro i _
      exact (Polynomial.natDegree_monomial_le _).trans (by have := hDeg i; dsimp [e]; omega)
    · intro a
      change Q.eval a = 0
      simpa [Q, e, Polynomial.eval_finsetSum, monomialJet, pow_add, pow_mul] using h a
  funext i
  have hh := congrArg (fun P : Polynomial K => P.coeff (e i)) hZero
  simp only [Q, Polynomial.finsetSum_coeff, Polynomial.coeff_zero] at hh
  rw [sum_eq_single i] at hh
  · simpa using hh
  · intro r _ hr
    exact Polynomial.coeff_monomial_of_ne _ (fun he => hr (hd he.symm))
  · simp

#print axioms frobeniusJets_grid_separate
#print axioms frobeniusJets_diagonal_separate
#print axioms frobeniusValues_powerGraph_separate

end
end AlpogeSuperZeta
