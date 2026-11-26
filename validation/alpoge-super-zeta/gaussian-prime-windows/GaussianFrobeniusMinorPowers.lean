import GaussianFrobeniusMinorIdeal
import Mathlib.LinearAlgebra.Matrix.Block

/-! At a matching Frobenius place the integral row change from
\(X^rY^s\) to \(X^{r\bmod p}Y^s(X^p-Y)^{\lfloor r/p\rfloor}\)
gives a lower bound for the prime exponent of every eligible minor. -/

namespace AlpogeSuperZeta

open Finset Matrix Polynomial

noncomputable section

private noncomputable def frobeniusPowerRow {x k : ℝ} (hk : 0 < k) {p : ℕ} (hp : 0 < p)
    (hkp : k ≤ (p : ℝ)) (i : FrobeniusTriangleRow x k)
    (d : Fin (i.2.val / p + 1)) : FrobeniusTriangleRow x k := by
  have hd : d.val ≤ i.2.val / p := Nat.le_of_lt_succ d.isLt
  have hmul : p * d.val ≤ i.2.val := by
    simpa only [Nat.mul_comm p d.val] using (Nat.le_div_iff_mul_le hp).mp hd
  have hi := Nat.lt_ceil.mp i.2.isLt
  have hCost := mul_le_mul_of_nonneg_right hkp (Nat.cast_nonneg (α := ℝ) d.val)
  have hTotal : ((i.2.val - p * d.val : ℕ) : ℝ) + k * ((i.1.val + d.val : ℕ) : ℝ) < x := by
    push_cast [Nat.cast_sub hmul]
    linarith
  let second : Fin ⌈x / k⌉₊ := ⟨i.1.val + d.val, Nat.lt_ceil.mpr <|
    (lt_div_iff₀ hk).2 (by linarith [Nat.cast_nonneg (α := ℝ) (i.2.val - p * d.val)])⟩
  exact ⟨second, ⟨i.2.val - p * d.val, Nat.lt_ceil.mpr (by dsimp [second]; linarith)⟩⟩

private def frobeniusPowerMatrix (R : Type*) [CommRing R] (x k : ℝ) (p : ℕ) :
    Matrix (FrobeniusTriangleRow x k) (FrobeniusTriangleRow x k) R :=
  fun i v =>
    if i.1.val ≤ v.1.val ∧ v.1.val - i.1.val ≤ i.2.val / p ∧
        v.2.val + p * (v.1.val - i.1.val) = i.2.val
    then ((i.2.val / p).choose (v.1.val - i.1.val) : R) * (-1) ^ (v.1.val - i.1.val)
    else 0

private theorem frobeniusPowerMatrix_det (R : Type*) [CommRing R] (x k : ℝ) (p : ℕ) :
    (frobeniusPowerMatrix R x k p).det = 1 := by
  classical
  let b (i : FrobeniusTriangleRow x k) := i.1
  let U := frobeniusPowerMatrix R x k p
  have hU : U.BlockTriangular b := by
    intro i v h
    change v.1.val < i.1.val at h
    exact if_neg (fun h' => (not_le_of_gt h) h'.1)
  have hBlock (s : Fin ⌈x / k⌉₊) : U.toSquareBlock b s = 1 := by
    ext i v
    have hs : i.val.1 = v.val.1 := i.property.trans v.property.symm
    change frobeniusPowerMatrix R x k p i.val v.val = (1 : Matrix _ _ R) i v
    by_cases he : i = v
    · subst v
      simp [frobeniusPowerMatrix]
    · have hne : v.val.2.val ≠ i.val.2.val := fun h =>
        he (Subtype.ext (frobeniusTriangleDegree_injective x k
          (Prod.ext h.symm (congrArg Fin.val hs))))
      have hs' : v.val.1.val - i.val.1.val = 0 := by
        have hh := congrArg Fin.val hs
        omega
      rw [Matrix.one_apply_ne he]
      simp [frobeniusPowerMatrix, hs', hne]
  change U.det = 1
  rw [hU.det_fintype]
  simp only [hBlock, Matrix.det_one, Finset.prod_const_one]

private theorem frobeniusPowerSum {M : Type*} [AddCommMonoid M] {x k : ℝ}
    (hk : 0 < k) {p : ℕ} (hp : 0 < p) (hkp : k ≤ (p : ℝ)) (i : FrobeniusTriangleRow x k)
    (F : FrobeniusTriangleRow x k → M) :
    (∑ v, if i.1.val ≤ v.1.val ∧ v.1.val - i.1.val ≤ i.2.val / p ∧
        v.2.val + p * (v.1.val - i.1.val) = i.2.val then F v else 0) =
      ∑ d : Fin (i.2.val / p + 1), F (frobeniusPowerRow hk hp hkp i d) := by
  classical
  let e : Fin (i.2.val / p + 1) ↪ FrobeniusTriangleRow x k :=
    ⟨frobeniusPowerRow hk hp hkp i, fun a b h => Fin.ext (Nat.add_left_cancel
      (congrArg (fun v => v.1.val) h))⟩
  have he : univ.filter (fun v : FrobeniusTriangleRow x k =>
      i.1.val ≤ v.1.val ∧ v.1.val - i.1.val ≤ i.2.val / p ∧
        v.2.val + p * (v.1.val - i.1.val) = i.2.val) = univ.map e := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · intro hv
      let d : Fin (i.2.val / p + 1) := ⟨v.1.val - i.1.val, Nat.lt_succ_of_le hv.2.1⟩
      refine ⟨d, frobeniusTriangleDegree_injective x k (Prod.ext ?_ ?_)⟩
      · change i.2.val - p * (v.1.val - i.1.val) = v.2.val
        omega
      · change i.1.val + (v.1.val - i.1.val) = v.1.val
        omega
    · rintro ⟨d, rfl⟩
      change i.1.val ≤ i.1.val + d.val ∧ (i.1.val + d.val) - i.1.val ≤ i.2.val / p ∧
        (i.2.val - p * d.val) + p * ((i.1.val + d.val) - i.1.val) = i.2.val
      rw [Nat.add_sub_cancel_left]
      have hd : d.val ≤ i.2.val / p := Nat.le_of_lt_succ d.isLt
      have hmul : p * d.val ≤ i.2.val := by
        simpa only [Nat.mul_comm p d.val] using (Nat.le_div_iff_mul_le hp).mp hd
      exact ⟨Nat.le_add_right _ _, hd, Nat.sub_add_cancel hmul⟩
  rw [← sum_filter, he, sum_map]
  rfl

private theorem frobeniusPowerTerm {R : Type*} [CommRing R] (a b : R[X]) (r s p d : ℕ)
    (hd : d ≤ r / p) :
    C (((r / p).choose d : R) * (-1) ^ d) * (a ^ (r - p * d) * b ^ (s + d)) =
      (a ^ (r % p) * b ^ s) * ((-b) ^ d * (a ^ p) ^ (r / p - d) * ((r / p).choose d : R[X])) := by
  have hExponent : r - p * d = r % p + p * (r / p - d) := by
    have hr := Nat.mod_add_div r p
    have hm := Nat.mul_le_mul_left p hd
    rw [Nat.mul_sub]
    omega
  rw [hExponent, pow_add a (r % p) (p * (r / p - d)), pow_mul a p (r / p - d),
    pow_add b s d, neg_pow b d]
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one]
  ac_rfl

private theorem frobeniusPowerPolynomial {R : Type*} [CommRing R] {x k : ℝ}
    (hk : 0 < k) {p : ℕ} (hp : 0 < p) (hkp : k ≤ (p : ℝ)) (i : FrobeniusTriangleRow x k)
    (a b : R[X]) :
    (∑ v : FrobeniusTriangleRow x k, C (frobeniusPowerMatrix R x k p i v) *
        (a ^ v.2.val * b ^ v.1.val)) =
      (a ^ (i.2.val % p) * b ^ i.1.val) * (a ^ p - b) ^ (i.2.val / p) := by
  let binomial (d : ℕ) : R[X] :=
    (-b) ^ d * (a ^ p) ^ (i.2.val / p - d) * ((i.2.val / p).choose d : R[X])
  calc
    _ = ∑ v : FrobeniusTriangleRow x k,
        if i.1.val ≤ v.1.val ∧ v.1.val - i.1.val ≤ i.2.val / p ∧
            v.2.val + p * (v.1.val - i.1.val) = i.2.val
        then C (((i.2.val / p).choose (v.1.val - i.1.val) : R) * (-1) ^ (v.1.val - i.1.val)) *
          (a ^ v.2.val * b ^ v.1.val) else 0 := by
      apply sum_congr rfl
      intro v _
      dsimp only [frobeniusPowerMatrix]
      split_ifs <;> simp
    _ = ∑ d : Fin (i.2.val / p + 1), C (((i.2.val / p).choose d.val : R) * (-1) ^ d.val) *
        (a ^ (i.2.val - p * d.val) * b ^ (i.1.val + d.val)) := by
      simpa only [frobeniusPowerRow, Nat.add_sub_cancel_left] using
        frobeniusPowerSum hk hp hkp i (fun v =>
          C (((i.2.val / p).choose (v.1.val - i.1.val) : R) * (-1) ^ (v.1.val - i.1.val)) *
            (a ^ v.2.val * b ^ v.1.val))
    _ = (a ^ (i.2.val % p) * b ^ i.1.val) * (∑ d : Fin (i.2.val / p + 1), binomial d.val) := by
      rw [mul_sum]
      exact sum_congr rfl fun d _ => frobeniusPowerTerm a b i.2.val i.1.val p d.val
        (Nat.le_of_lt_succ d.isLt)
    _ = _ := by
      rw [Fin.sum_univ_eq_sum_range binomial]
      dsimp only [binomial]
      rw [← add_pow, add_comm (-b), ← sub_eq_add_neg]

private theorem powerShiftedMonomialCoeff {R : Type*} [CommRing R] (a : R) (r j : ℕ) :
    (((X : R[X]) + C a) ^ r).coeff j = monomialJet r j a := by
  rw [← Polynomial.taylor_X_pow, ← Polynomial.monomial_one_right_eq_X_pow,
    Polynomial.taylor_coeff, Polynomial.hasseDeriv_monomial, Polynomial.eval_monomial]
  simp only [monomialJet, mul_one]

private theorem frobeniusPowerMatrix_mul_apply {R : Type*} [CommRing R] {x k : ℝ} {p J : ℕ}
    (hk : 0 < k) (hp : 0 < p) (hkp : k ≤ (p : ℝ)) (σ : R →+* R)
    (node : FrobeniusTriangleRow x k → R) (order : FrobeniusTriangleRow x k → Fin J)
    (i j : FrobeniusTriangleRow x k) :
    (frobeniusPowerMatrix R x k p * frobeniusTriangleHasseMatrix σ node order) i j =
      ((((X : R[X]) + C (node j)) ^ (i.2.val % p) * (C (σ (node j))) ^ i.1.val) *
        (((X + C (node j)) ^ p - C (σ (node j))) ^ (i.2.val / p))).coeff (order j).val := by
  let a := node j
  let b := σ a
  let n := (order j).val
  have hTerm (r s : ℕ) : (((X + C a) ^ r) * (C b) ^ s).coeff n = monomialJet r n a * b ^ s := by
    rw [← map_pow, mul_comm, Polynomial.coeff_C_mul, powerShiftedMonomialCoeff, mul_comm]
  have h := congrArg (fun P : R[X] => P.coeff n) (frobeniusPowerPolynomial hk hp hkp i (X + C a) (C b))
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, hTerm] at h
  rw [Matrix.mul_apply]
  exact h

private theorem mul_lowCoeff_mem {R : Type*} [CommRing R] (I J : Ideal R) (u v : R[X]) {bound : ℕ}
    (hu : ∀ n < bound, u.coeff n ∈ I) (hv : ∀ n < bound, v.coeff n ∈ J) :
    ∀ n < bound, (u * v).coeff n ∈ I * J := by
  intro n hn
  rw [Polynomial.coeff_mul]
  apply Ideal.sum_mem
  intro d hd
  have hd' := HasAntidiagonal.mem_antidiagonal.mp hd
  exact Ideal.mul_mem_mul (hu d.1 (by omega)) (hv d.2 (by omega))

private theorem pow_lowCoeff_mem {R : Type*} [CommRing R] (P : Ideal R) (u : R[X]) {bound : ℕ}
    (hu : ∀ n < bound, u.coeff n ∈ P) (h : ℕ) :
    ∀ n < bound, (u ^ h).coeff n ∈ P ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [pow_succ, pow_succ]
    exact mul_lowCoeff_mem (P ^ h) P (u ^ h) u ih hu

private theorem frobeniusFactor_lowCoeff_mem {R : Type*} [CommRing R] (P : Ideal R) {p : ℕ}
    [CharP (R ⧸ P) p] (hp : p.Prime) (a b : R)
    (h : Ideal.Quotient.mk P b = (Ideal.Quotient.mk P a) ^ p) :
    ∀ n < p, (((X : R[X]) + C a) ^ p - C b).coeff n ∈ P := by
  intro n hn
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  let q := Ideal.Quotient.mk P
  have hJet : q (monomialJet p n a) = monomialJet p n (q a) := by simp [monomialJet]
  have hRead := hasseFrobeniusJets_eq_below_p p hp (q a) (q b) h.symm n hn
  rw [Polynomial.coeff_sub, powerShiftedMonomialCoeff, map_sub, hJet, hRead, Polynomial.coeff_C]
  by_cases hn₀ : n = 0
  · subst n
    simp [q]
  · simp [hn₀]

private theorem det_mem_pow_of_rows {R Rows : Type*} [CommRing R] [Fintype Rows] [DecidableEq Rows]
    (P : Ideal R) (M : Matrix Rows Rows R) (weight : Rows → ℕ)
    (hM : ∀ i j, M i j ∈ P ^ weight i) : M.det ∈ P ^ (∑ i, weight i) := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Ideal.sum_mem
  intro v _
  apply Ideal.mul_mem_left
  rw [← Finset.prod_pow_eq_pow_sum univ weight P]
  exact Ideal.prod_mem_prod fun i _ => hM i (v i)

private theorem frobeniusTriangleDivisibility_row_sum (x k : ℝ) (p : ℕ) :
    (∑ i : FrobeniusTriangleRow x k, i.2.val / p) = frobeniusTriangleDivisibility x k p := by
  simp only [frobeniusTriangleDivisibility, Fintype.sum_sigma]
  simp_rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => r / p)]
  exact Fin.sum_univ_eq_sum_range (fun s : ℕ => ∑ r ∈ range ⌈x - k * (s : ℝ)⌉₊, r / p) _

/-- A full minor at a matching Frobenius place is divisible by the
floor sum, for every choice of nodes and every jet order below \(p\). -/
theorem frobeniusTriangleHasseMinor_mem_pow {R : Type*} [CommRing R] (P : Ideal R)
    (σ : R →+* R) {x k : ℝ} (hk : 0 < k) {p J : ℕ} [CharP (R ⧸ P) p]
    (hp : p.Prime) (hkp : k ≤ (p : ℝ))
    (hFrob : ∀ a : R, Ideal.Quotient.mk P (σ a) = (Ideal.Quotient.mk P a) ^ p)
    (node : FrobeniusTriangleRow x k → R) (order : FrobeniusTriangleRow x k → Fin J)
    (hOrder : ∀ j, (order j).val < p) :
    frobeniusTriangleHasseMinor σ node order ∈ P ^ frobeniusTriangleDivisibility x k p := by
  classical
  let U := frobeniusPowerMatrix R x k p
  let A := frobeniusTriangleHasseMatrix σ node order
  let w (i : FrobeniusTriangleRow x k) := i.2.val / p
  have hDet : (U * A).det = A.det := by
    rw [Matrix.det_mul, show U.det = 1 from frobeniusPowerMatrix_det R x k p, one_mul]
  have hWeight : (∑ i, w i) = frobeniusTriangleDivisibility x k p :=
    frobeniusTriangleDivisibility_row_sum x k p
  change A.det ∈ P ^ frobeniusTriangleDivisibility x k p
  rw [← hDet, ← hWeight]
  apply det_mem_pow_of_rows P _ w
  intro i j
  change (frobeniusPowerMatrix R x k p * frobeniusTriangleHasseMatrix σ node order) i j ∈ _
  rw [frobeniusPowerMatrix_mul_apply hk hp.pos hkp]
  let t : R[X] := X + C (node j)
  let b := C (σ (node j))
  let u := t ^ (i.2.val % p) * b ^ i.1.val
  have hLow := frobeniusFactor_lowCoeff_mem P hp (node j) (σ (node j)) (hFrob (node j))
  have hPow := pow_lowCoeff_mem P (t ^ p - b) hLow (w i)
  have hTop : ∀ n < p, u.coeff n ∈ (1 : Ideal R) := by simp
  simpa only [one_mul] using
    mul_lowCoeff_mem 1 (P ^ w i) u ((t ^ p - b) ^ w i) hTop hPow (order j).val (hOrder j)

/-- At the square-root cutoff every eligible minor carries the same
lower bound on its exponent at any matching Frobenius place. -/
theorem sqrtFrobeniusMinorIdeal_le_pow_of_frobenius {R : Type*} [CommRing R]
    (P : Ideal R) (σ : R →+* R) {x : ℝ} (hx : 2 ≤ x) {p : ℕ}
    [CharP (R ⧸ P) p] (hp : p.Prime) (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hFrob : ∀ a : R, Ideal.Quotient.mk P (σ a) = (Ideal.Quotient.mk P a) ^ p) :
    sqrtFrobeniusMinorIdeal x σ ≤ P ^ frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p := by
  have hk : 0 < gaussianSqrtTriangleScale x := by
    dsimp [gaussianSqrtTriangleScale]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith) _)
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨node, order⟩, rfl⟩
  exact frobeniusTriangleHasseMinor_mem_pow P σ hk hp hLow hFrob node order
    (fun j => gaussianSqrtJet_order_lt_retainedPrime hLow (order j).isLt)

/-- For order-zero readings, the same row change exposes the exact power
of a common scalar and leaves the normalized value determinant. -/
theorem frobeniusTriangleHasseMinor_value_factor {R : Type*} [CommRing R]
    (σ : R →+* R) {x k : ℝ} (hk : 0 < k) {p J : ℕ} (hp : 0 < p) (hkp : k ≤ (p : ℝ))
    (c : R) (digit : R → R) (hd : ∀ a, a ^ p - σ a = c * digit a)
    (node : FrobeniusTriangleRow x k → R) (order : FrobeniusTriangleRow x k → Fin J)
    (hOrder : ∀ j, (order j).val = 0) :
    frobeniusTriangleHasseMinor σ node order = c ^ frobeniusTriangleDivisibility x k p *
      (Matrix.of fun (i j : FrobeniusTriangleRow x k) =>
        node j ^ (i.2.val % p) * (σ (node j)) ^ i.1.val * (digit (node j)) ^ (i.2.val / p)).det := by
  classical
  let U := frobeniusPowerMatrix R x k p
  let A := frobeniusTriangleHasseMatrix σ node order
  let M := Matrix.of fun (i j : FrobeniusTriangleRow x k) =>
    node j ^ (i.2.val % p) * (σ (node j)) ^ i.1.val * (digit (node j)) ^ (i.2.val / p)
  let D := Matrix.diagonal fun i : FrobeniusTriangleRow x k => c ^ (i.2.val / p)
  have hX : Polynomial.constantCoeff (X : R[X]) = 0 := by
    change (X : R[X]).coeff 0 = 0
    simp
  have hC (a : R) : Polynomial.constantCoeff (C a) = a := by
    change (C a).coeff 0 = a
    simp
  have hMat : U * A = D * M := by
    ext i j
    change (frobeniusPowerMatrix R x k p * frobeniusTriangleHasseMatrix σ node order) i j =
      (Matrix.diagonal (fun i : FrobeniusTriangleRow x k => c ^ (i.2.val / p)) * M) i j
    rw [frobeniusPowerMatrix_mul_apply hk hp hkp, hOrder j, Matrix.diagonal_mul,
      ← Polynomial.constantCoeff_apply]
    simp only [map_mul, map_pow, map_sub, map_add, hX, hC, zero_add, hd, mul_pow, Matrix.of_apply, M]
    ac_rfl
  calc
    A.det = (U * A).det := by
      rw [Matrix.det_mul, show U.det = 1 from frobeniusPowerMatrix_det R x k p, one_mul]
    _ = _ := by
      rw [hMat, Matrix.det_mul, show D.det = ∏ i : FrobeniusTriangleRow x k, c ^ (i.2.val / p)
        from Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum, frobeniusTriangleDivisibility_row_sum]

#print axioms frobeniusTriangleHasseMinor_mem_pow
#print axioms sqrtFrobeniusMinorIdeal_le_pow_of_frobenius
#print axioms frobeniusTriangleHasseMinor_value_factor

end

end AlpogeSuperZeta
