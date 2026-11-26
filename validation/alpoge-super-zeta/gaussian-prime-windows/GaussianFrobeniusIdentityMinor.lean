import GaussianFrobeniusMinorIdeal
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Int.NatAbs

/-! An integer-node minor for the identity reading. Change the row
\(X^rY^s\) to \(X^r(Y-X)^s\), keeping the same triangle and the same columns. -/

namespace AlpogeSuperZeta

open Finset Matrix Polynomial

noncomputable section

private noncomputable def identityShiftRow {x k : ℝ} (hk : 1 ≤ k) (i : FrobeniusTriangleRow x k)
    (d : Fin (i.1.val + 1)) : FrobeniusTriangleRow x k :=
  ⟨⟨d.val, (Nat.le_of_lt_succ d.isLt).trans_lt i.1.isLt⟩,
    ⟨i.2.val + (i.1.val - d.val), by
      have hd : d.val ≤ i.1.val := Nat.le_of_lt_succ d.isLt
      have hi := Nat.lt_ceil.mp i.2.isLt
      have hsub : 0 ≤ (i.1.val : ℝ) - d.val := sub_nonneg.mpr (Nat.cast_le.mpr hd)
      have hmul := mul_le_mul_of_nonneg_right hk hsub
      apply Nat.lt_ceil.mpr
      push_cast [Nat.cast_sub hd]
      linarith⟩⟩

private def identityShiftMatrix (R : Type*) [CommRing R] (x k : ℝ) :
    Matrix (FrobeniusTriangleRow x k) (FrobeniusTriangleRow x k) R :=
  fun i v =>
    if v.1.val ≤ i.1.val ∧ v.2.val + v.1.val = i.2.val + i.1.val then
      (i.1.val.choose v.1.val : R) * (-1) ^ (i.1.val - v.1.val)
    else 0

private theorem identityShiftMatrix_det (R : Type*) [CommRing R] (x k : ℝ) :
    (identityShiftMatrix R x k).det = 1 := by
  classical
  let b (i : FrobeniusTriangleRow x k) := i.1
  let M := identityShiftMatrix R x k
  have ht : Mᵀ.BlockTriangular b := by
    intro i j h
    change j.1.val < i.1.val at h
    change identityShiftMatrix R x k j i = _
    exact if_neg (fun h' => (not_le_of_gt h) h'.1)
  have hb (s : Fin ⌈x / k⌉₊) : Mᵀ.toSquareBlock b s = 1 := by
    ext i j
    have hs : i.val.1 = j.val.1 := i.property.trans j.property.symm
    change identityShiftMatrix R x k j.val i.val = (1 : Matrix _ _ R) i j
    by_cases e : i = j
    · subst j
      simp [identityShiftMatrix]
    · have hr : i.val.2.val ≠ j.val.2.val := by
        intro h
        exact e (Subtype.ext (frobeniusTriangleDegree_injective x k
          (Prod.ext h (congrArg Fin.val hs))))
      have hne : i.val.2.val + i.val.1.val ≠ j.val.2.val + j.val.1.val := by
        have hs' := congrArg Fin.val hs
        omega
      rw [Matrix.one_apply_ne e]
      exact if_neg (fun h => hne h.2)
  change M.det = 1
  rw [← Matrix.det_transpose, ht.det_fintype]
  simp only [hb, Matrix.det_one, Finset.prod_const_one]

private theorem identityShiftSum {M : Type*} [AddCommMonoid M] {x k : ℝ}
    (hk : 1 ≤ k) (i : FrobeniusTriangleRow x k) (F : FrobeniusTriangleRow x k → M) :
    (∑ v, if v.1.val ≤ i.1.val ∧ v.2.val + v.1.val = i.2.val + i.1.val then
      F v else 0) = ∑ d : Fin (i.1.val + 1), F (identityShiftRow hk i d) := by
  classical
  let e : Fin (i.1.val + 1) ↪ FrobeniusTriangleRow x k :=
    ⟨identityShiftRow hk i, fun a b h => Fin.ext (congrArg (fun v => v.1.val) h)⟩
  have he : univ.filter (fun v : FrobeniusTriangleRow x k =>
      v.1.val ≤ i.1.val ∧ v.2.val + v.1.val = i.2.val + i.1.val) = univ.map e := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · intro hv
      let d : Fin (i.1.val + 1) := ⟨v.1.val, Nat.lt_succ_of_le hv.1⟩
      refine ⟨d, frobeniusTriangleDegree_injective x k (Prod.ext ?_ rfl)⟩
      change i.2.val + (i.1.val - v.1.val) = v.2.val
      omega
    · rintro ⟨d, rfl⟩
      change d.val ≤ i.1.val ∧ (i.2.val + (i.1.val - d.val)) + d.val = i.2.val + i.1.val
      have hd := d.isLt
      omega
  rw [← sum_filter, he, sum_map]
  rfl

private theorem shiftedMonomial_coeff {R : Type*} [CommRing R] (a : R) (r j : ℕ) :
    (((X : R[X]) + C a) ^ r).coeff j = monomialJet r j a := by
  rw [← Polynomial.taylor_X_pow]
  rw [← Polynomial.monomial_one_right_eq_X_pow, Polynomial.taylor_coeff,
    Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  simp only [monomialJet, mul_one]

private theorem shiftedBinomialTerm {R : Type*} [CommRing R] (a : R) (r s d : ℕ) :
    C ((s.choose d : R) * (-1) ^ (s - d)) * ((X + C a) ^ (r + (s - d)) * (C a) ^ d) =
      (X + C a) ^ r * ((C a) ^ d * (-(X + C a)) ^ (s - d) * (s.choose d : R[X])) := by
  rw [neg_pow (X + C a) (s - d), pow_add (X + C a) r (s - d)]
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one]
  ac_rfl

private theorem identityShiftPolynomial {R : Type*} [CommRing R] {x k : ℝ}
    (hk : 1 ≤ k) (i : FrobeniusTriangleRow x k) (a : R) :
    (∑ v : FrobeniusTriangleRow x k, C (identityShiftMatrix R x k i v) *
      ((X + C a) ^ v.2.val * (C a) ^ v.1.val)) =
      (X + C a) ^ i.2.val * (-X) ^ i.1.val := by
  let t : R[X] := X + C a
  let binomial (d : ℕ) : R[X] :=
    (C a) ^ d * (-t) ^ (i.1.val - d) * (i.1.val.choose d : R[X])
  calc
    _ = ∑ v : FrobeniusTriangleRow x k,
        if v.1.val ≤ i.1.val ∧ v.2.val + v.1.val = i.2.val + i.1.val then
          C ((i.1.val.choose v.1.val : R) * (-1) ^ (i.1.val - v.1.val)) *
            (t ^ v.2.val * (C a) ^ v.1.val) else 0 := by
      apply sum_congr rfl
      intro v _
      dsimp only [identityShiftMatrix, t]
      split_ifs <;> simp
    _ = ∑ d : Fin (i.1.val + 1),
        C ((i.1.val.choose d.val : R) * (-1) ^ (i.1.val - d.val)) *
          (t ^ (i.2.val + (i.1.val - d.val)) * (C a) ^ d.val) := by
      simpa only [identityShiftRow] using identityShiftSum hk i (fun v =>
        C ((i.1.val.choose v.1.val : R) * (-1) ^ (i.1.val - v.1.val)) *
          (t ^ v.2.val * (C a) ^ v.1.val))
    _ = t ^ i.2.val * (∑ d : Fin (i.1.val + 1), binomial d.val) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      exact shiftedBinomialTerm a i.2.val i.1.val d.val
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range binomial]
      dsimp only [binomial]
      rw [← add_pow]
      have he : C a + -t = -X := by dsimp [t]; ring
      rw [he]

private theorem identityShiftMatrix_mul_apply {R : Type*} [CommRing R] {x k : ℝ} {J : ℕ}
    (hk : 1 ≤ k) (order : FrobeniusTriangleRow x k → Fin J)
    (node : FrobeniusTriangleRow x k → R) (i j : FrobeniusTriangleRow x k) :
    (identityShiftMatrix R x k * frobeniusTriangleHasseMatrix (RingHom.id R) node order) i j =
      if i.1.val ≤ (order j).val then
        (-1 : R) ^ i.1.val * monomialJet i.2.val ((order j).val - i.1.val) (node j)
      else 0 := by
  let a := node j
  let n := (order j).val
  have hTerm (r s : ℕ) : (((X + C a) ^ r) * (C a) ^ s).coeff n =
      monomialJet r n a * a ^ s := by
    rw [← map_pow, mul_comm, Polynomial.coeff_C_mul, shiftedMonomial_coeff, mul_comm]
  have hRight : (X + C a) ^ i.2.val * (-X) ^ i.1.val =
      C ((-1 : R) ^ i.1.val) * ((X + C a) ^ i.2.val * X ^ i.1.val) := by
    rw [neg_pow, map_pow, map_neg, map_one]
    ac_rfl
  have he := congrArg (fun P : R[X] => P.coeff n) (identityShiftPolynomial hk i a)
  rw [hRight, Polynomial.coeff_C_mul, Polynomial.coeff_mul_X_pow'] at he
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, hTerm, shiftedMonomial_coeff] at he
  rw [Matrix.mul_apply]
  change (∑ v, identityShiftMatrix R x k i v * (monomialJet v.2.val n a * a ^ v.1.val)) =
    if i.1.val ≤ n then (-1 : R) ^ i.1.val * monomialJet i.2.val (n - i.1.val) a else 0
  by_cases h : i.1.val ≤ n
  · rw [if_pos h] at he ⊢
    exact he
  · rw [if_neg h, mul_zero] at he
    rw [if_neg h]
    exact he

private theorem det_vandermonde_natural_nodes (R : Type*) [CommRing R] (m : ℕ) :
    (vandermonde fun i : Fin m => (i.val : R)).det =
      ∏ i : Fin m, (i.val.factorial : R) := by
  have hsf (n : ℕ) : (n.superFactorial : R) = ∏ j ∈ range (n + 1), (j.factorial : R) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.superFactorial_succ, Nat.cast_mul, ih,
        prod_range_succ (fun j : ℕ => (j.factorial : R)) (n + 1)]
      exact mul_comm _ _
  cases m with
  | zero => simp
  | succ n =>
    rw [det_vandermonde_id_eq_superFactorial, hsf]
    exact (Fin.prod_univ_eq_prod_range (fun j : ℕ => (j.factorial : R)) (n + 1)).symm

private def triangleBlockEquiv (x k : ℝ) (s : Fin ⌈x / k⌉₊) :
    Fin ⌈x - k * (s.val : ℝ)⌉₊ ≃ {i : FrobeniusTriangleRow x k // i.1 = s} :=
  Equiv.ofBijective (fun r => ⟨⟨s, r⟩, rfl⟩)
    ⟨fun r t h => Fin.ext (congrArg (fun i => i.val.2.val) h), by
      rintro ⟨⟨j, r⟩, h⟩
      change j = s at h
      subst j
      exact ⟨r, rfl⟩⟩

/-- The identity minor with node \(r\) and Hasse order \(s\) at column
\((r,s)\). Its determinant is a product of signed factorials. -/
theorem frobeniusTriangleIdentityMinor_factorial {R : Type*} [CommRing R] {x k : ℝ} {J : ℕ}
    (hk : 1 ≤ k) (hOrder : ∀ i : FrobeniusTriangleRow x k, i.1.val < J) :
    frobeniusTriangleHasseMinor (RingHom.id R)
      (fun i : FrobeniusTriangleRow x k => (i.2.val : R)) (fun i => ⟨i.1.val, hOrder i⟩) =
      ∏ i : FrobeniusTriangleRow x k, ((-1 : R) ^ i.1.val * (i.2.val.factorial : R)) := by
  classical
  let b (i : FrobeniusTriangleRow x k) := i.1
  let order (i : FrobeniusTriangleRow x k) : Fin J := ⟨i.1.val, hOrder i⟩
  let node (i : FrobeniusTriangleRow x k) : R := i.2.val
  let A := frobeniusTriangleHasseMatrix (RingHom.id R) node order
  let U := identityShiftMatrix R x k
  let M := U * A
  have hM (i j : FrobeniusTriangleRow x k) : M i j =
      if i.1.val ≤ j.1.val then
        (-1 : R) ^ i.1.val * monomialJet i.2.val (j.1.val - i.1.val) (node j)
      else 0 := identityShiftMatrix_mul_apply hk order node i j
  have ht : M.BlockTriangular b := by
    intro i j h
    change j.1.val < i.1.val at h
    rw [hM, if_neg (Nat.not_le_of_lt h)]
  have hb (s : Fin ⌈x / k⌉₊) : (M.toSquareBlock b s).det =
      ∏ r : Fin ⌈x - k * (s.val : ℝ)⌉₊, ((-1 : R) ^ s.val * (r.val.factorial : R)) := by
    let e := triangleBlockEquiv x k s
    rw [← Matrix.det_submatrix_equiv_self e]
    have he : ((M.toSquareBlock b s).submatrix e e) =
        ((-1 : R) ^ s.val) • (vandermonde fun i : Fin ⌈x - k * (s.val : ℝ)⌉₊ => (i.val : R))ᵀ := by
      ext i j
      change M ⟨s,i⟩ ⟨s,j⟩ = (-1 : R) ^ s.val * (j.val : R) ^ i.val
      simp [hM, node, monomialJet]
    rw [he, Matrix.det_smul, Matrix.det_transpose, det_vandermonde_natural_nodes, prod_mul_distrib,
      Finset.prod_const, card_univ]
  have hDet : A.det = M.det := by
    rw [show M = U * A from rfl, Matrix.det_mul, show U.det = 1 from identityShiftMatrix_det R x k,
      one_mul]
  change A.det = _
  rw [hDet]
  rw [ht.det_fintype]
  simp only [hb, Fintype.prod_sigma]

private theorem sqrtTriangle_identity_orders {x : ℝ} (hx : 2 ≤ x)
    (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) :
    i.1.val < gaussianSqrtJetCount x := by
  let v := x ^ (1 / 2 : ℝ)
  have hv : 0 < v := Real.rpow_pos_of_pos (by linarith) _
  have hsq : v ^ 2 = x := by
    rw [show v = Real.sqrt x from (Real.sqrt_eq_rpow x).symm, Real.sq_sqrt (by linarith)]
  have hle : x / gaussianSqrtTriangleScale x ≤ v := by
    change x / (2 * v) ≤ v
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  exact Nat.lt_ceil.mpr ((Nat.lt_ceil.mp i.1.isLt).trans_le hle)

private theorem sqrtTriangle_scale_one {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ gaussianSqrtTriangleScale x := by
  have hv := Real.one_le_rpow (show 1 ≤ x by linarith) (by norm_num : 0 ≤ (1 / 2 : ℝ))
  dsimp [gaussianSqrtTriangleScale]
  linarith

/-- The same factorial product is an explicit generator of the
identity minor ideal over the coefficient ring. -/
theorem sqrtFrobeniusIdentityMinor_factorial_mem (R : Type*) [CommRing R] {x : ℝ}
    (hx : 2 ≤ x) :
    (∏ i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x),
      ((-1 : R) ^ i.1.val * (i.2.val.factorial : R))) ∈
      sqrtFrobeniusMinorIdeal x (RingHom.id R) := by
  let node (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) : R := i.2.val
  let order (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) : Fin (gaussianSqrtJetCount x) :=
    ⟨i.1.val, sqrtTriangle_identity_orders hx i⟩
  apply Ideal.subset_span
  exact ⟨(node, order), frobeniusTriangleIdentityMinor_factorial (sqrtTriangle_scale_one hx)
    (sqrtTriangle_identity_orders hx)⟩

/-- The same integer-node choice works at every retained prime. -/
theorem sqrtFrobeniusIdentityMinor_valuation {x : ℝ} (hx : 2 ≤ x)
    {p : ℕ} (hp : p.Prime) (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ)) :
    (frobeniusTriangleHasseMinor (RingHom.id ℤ)
      (fun i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x) => (i.2.val : ℤ))
      (fun i => (⟨i.1.val, sqrtTriangle_identity_orders hx i⟩ : Fin (gaussianSqrtJetCount x)))).natAbs.factorization p =
      frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p := by
  classical
  rw [frobeniusTriangleIdentityMinor_factorial (sqrtTriangle_scale_one hx)]
  change (Int.natAbsHom (∏ i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x),
    ((-1 : ℤ) ^ i.1.val * (i.2.val.factorial : ℤ)))).factorization p = _
  have hAbs (s r : ℕ) : Int.natAbsHom ((-1 : ℤ) ^ s * (r.factorial : ℤ)) = r.factorial := by
    rw [map_mul, map_pow]
    change ((-1 : ℤ).natAbs) ^ s * ((r.factorial : ℤ).natAbs) = _
    simp
  simp only [map_prod, hAbs]
  rw [Nat.factorization_prod_apply (fun _ _ => Nat.factorial_ne_zero _)]
  have hpSq := (sqrtFrobeniusScale_prime_bounds hx hLow).1
  have hRow (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) :
      i.2.val.factorial.factorization p = i.2.val / p := by
    have hDeg : (i.2.val : ℝ) < x := by
      have hi := Nat.lt_ceil.mp i.2.isLt
      exact hi.trans_le (sub_le_self _ (mul_nonneg (le_trans zero_le_one (sqrtTriangle_scale_one hx))
        (Nat.cast_nonneg _)))
    have hSq : i.2.val < p ^ 2 := by exact_mod_cast hDeg.trans_le hpSq
    have hLog : Nat.log p i.2.val < 2 := by
      by_cases hZero : i.2.val = 0
      · simp [hZero]
      · exact (Nat.log_lt_iff_lt_pow hp.one_lt hZero).2 hSq
    rw [Nat.factorization_factorial hp hLog]
    have hs : Ico 1 2 = ({1} : Finset ℕ) := by
      ext j
      simp only [mem_Ico, mem_singleton]
      omega
    rw [hs, sum_singleton, pow_one]
  simp only [hRow, frobeniusTriangleDivisibility, Fintype.sum_sigma]
  simp_rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => r / p)]
  exact Fin.sum_univ_eq_sum_range (fun s : ℕ => ∑ r ∈ range ⌈x - gaussianSqrtTriangleScale x * (s : ℝ)⌉₊,
    r / p) _

#print axioms frobeniusTriangleIdentityMinor_factorial
#print axioms sqrtFrobeniusIdentityMinor_factorial_mem
#print axioms sqrtFrobeniusIdentityMinor_valuation

end

end AlpogeSuperZeta
