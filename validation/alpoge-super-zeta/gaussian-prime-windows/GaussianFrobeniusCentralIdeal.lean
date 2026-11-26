import GaussianFrobeniusIdentityIdeal
import Mathlib.Algebra.Ring.GeomSum

/-! At a place with residue field of size \(p^2\), varying a node by
\(pb\) preserves its residue and moves its normalized Frobenius difference
by \(-\sigma(b)\). The two residue readings then separate every triangle row. -/

namespace AlpogeSuperZeta

open Finset Matrix UniqueFactorizationMonoid

noncomputable section

private theorem quotient_primeCast_zero {R : Type*} [CommRing R] (P : Ideal R) {p : ℕ}
    [CharP (R ⧸ P) p] :
    Ideal.Quotient.mk P (p : R) = 0 := by
  rw [map_natCast]
  exact (CharP.cast_eq_zero_iff (R ⧸ P) p p).mpr (dvd_refl p)

/-- Lifting the node by \(pb\) translates the second residue by the
negative of \(\sigma b\). The first residue is fixed. -/
theorem normalizedFrobenius_shift {R : Type*} [CommRing R] [IsDomain R] (P : Ideal R)
    {p : ℕ} [CharP (R ⧸ P) p] (hPrimeCast : (p : R) ≠ 0) (σ : R →+* R)
    (digit : R → R) (hd : ∀ a, a ^ p - σ a = (p : R) * digit a) (a b : R) :
    Ideal.Quotient.mk P (digit (a + (p : R) * b)) =
      Ideal.Quotient.mk P (digit a) - Ideal.Quotient.mk P (σ b) := by
  let q := Ideal.Quotient.mk P
  let S := ∑ i ∈ range p, (a + (p : R) * b) ^ i * a ^ (p - 1 - i)
  have hqP : q (p : R) = 0 := quotient_primeCast_zero P
  have hqAB : q (a + (p : R) * b) = q a := by
    simp only [map_add, map_mul, hqP, zero_mul, add_zero]
  have hqS : q S = 0 := by
    dsimp only [S]
    rw [map_sum]
    calc
      _ = ∑ _i ∈ range p, (q a) ^ (p - 1) := by
        refine sum_congr rfl fun i hi => ?_
        have hExp : i + (p - 1 - i) = p - 1 := by
          have := mem_range.mp hi
          omega
        simp only [map_mul, map_pow, hqAB, ← pow_add, hExp]
      _ = 0 := by
        have hpZero : (p : R ⧸ P) = 0 := by simpa only [map_natCast] using hqP
        rw [sum_const, card_range, nsmul_eq_mul, hpZero, zero_mul]
  have hDiff : (a + (p : R) * b) ^ p - a ^ p = (p : R) * (b * S) := by
    rw [← geom_sum₂_mul]
    change S * (a + (p : R) * b - a) = _
    ring
  have he : (p : R) * digit (a + (p : R) * b) =
      (p : R) * (digit a + b * S - σ b) := by
    calc
      _ = (a + (p : R) * b) ^ p - σ (a + (p : R) * b) := (hd _).symm
      _ = ((a + (p : R) * b) ^ p - a ^ p) + (a ^ p - σ a) - (p : R) * σ b := by
        rw [map_add, map_mul, map_natCast]
        ring
      _ = _ := by
        rw [hDiff, hd a]
        ring
  change q (digit (a + (p : R) * b)) = q (digit a) - q (σ b)
  rw [mul_left_cancel₀ hPrimeCast he, map_sub, map_add, map_mul, hqS, mul_zero, add_zero]

/-- Both readings of the same integral node can be prescribed independently. -/
theorem normalizedFrobenius_pair_surjective {R : Type*} [CommRing R] [IsDomain R]
    (P : Ideal R) {p : ℕ} [CharP (R ⧸ P) p] (hPrimeCast : (p : R) ≠ 0)
    (σ : R ≃+* R) (digit : R → R) (hd : ∀ a, a ^ p - σ a = (p : R) * digit a) :
    Function.Surjective fun a : R => (Ideal.Quotient.mk P a, Ideal.Quotient.mk P (digit a)) := by
  intro v
  let q := Ideal.Quotient.mk P
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective v.1
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (q (digit a) - v.2)
  let z := σ.symm b
  have hqP : q (p : R) = 0 := quotient_primeCast_zero P
  refine ⟨a + (p : R) * z, Prod.ext ?_ ?_⟩
  · change q (a + (p : R) * z) = v.1
    simpa only [map_add, map_mul, hqP, zero_mul, add_zero] using ha
  · change q (digit (a + (p : R) * z)) = v.2
    rw [normalizedFrobenius_shift P hPrimeCast σ.toRingHom digit hd]
    change q (digit a) - q (σ (σ.symm b)) = v.2
    rw [RingEquiv.apply_symm_apply, hb, sub_sub_cancel]

private noncomputable def normalizedFrobeniusDegree {x k : ℝ} (p : ℕ)
    (i : FrobeniusTriangleRow x k) : ℕ × ℕ :=
  (i.2.val % p + p * i.1.val, i.2.val / p)

private theorem normalizedFrobeniusDegree_injective {x k : ℝ} {p : ℕ} (hp : 0 < p) :
    Function.Injective (normalizedFrobeniusDegree (x := x) (k := k) p) := by
  intro i j h
  have hExp := congrArg Prod.fst h
  have hDiv := congrArg Prod.snd h
  change i.2.val / p = j.2.val / p at hDiv
  change i.2.val % p + p * i.1.val = j.2.val % p + p * j.1.val at hExp
  have hMod := congrArg (fun m : ℕ => m % p) hExp
  have hMod' : i.2.val % p = j.2.val % p := by simpa [Nat.add_mod] using hMod
  rw [hMod', Nat.add_left_cancel_iff] at hExp
  have hs := Nat.eq_of_mul_eq_mul_left hp hExp
  have hr : i.2.val = j.2.val := by
    calc
      _ = i.2.val % p + p * (i.2.val / p) := (Nat.mod_add_div _ _).symm
      _ = j.2.val := by rw [hMod', hDiv, Nat.mod_add_div]
  exact frobeniusTriangleDegree_injective x k (Prod.ext hr hs)

private theorem sqrtFrobeniusDegree_lt_prime {x : ℝ} (hx : 2 ≤ x) {p : ℕ}
    (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) :
    i.1.val < p ∧ i.2.val < p ^ 2 := by
  let v := x ^ (1 / 2 : ℝ)
  let k := gaussianSqrtTriangleScale x
  have hv : 0 < v := Real.rpow_pos_of_pos (by linarith) _
  have hk : 0 < k := by change 0 < 2 * v; positivity
  have hsq : v ^ 2 = x := by
    rw [show v = Real.sqrt x from (Real.sqrt_eq_rpow x).symm, Real.sq_sqrt (by linarith)]
  have hS := Nat.lt_ceil.mp i.1.isLt
  have hs : x / k ≤ v := by
    change x / (2 * v) ≤ v
    exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hvp : v ≤ (p : ℝ) := by
    change 2 * v ≤ (p : ℝ) at hLow
    linarith
  have hR := Nat.lt_ceil.mp i.2.isLt
  have hR' : (i.2.val : ℝ) < x :=
    hR.trans_le (sub_le_self _ (mul_nonneg hk.le (Nat.cast_nonneg _)))
  exact ⟨Nat.cast_lt.mp (hS.trans_le (hs.trans hvp)),
    Nat.cast_lt.mp (hR'.trans_le (sqrtFrobeniusScale_prime_bounds hx hLow).1)⟩

/-- The two exponent digits distinguish the entire normalized row array. -/
theorem sqrtFrobeniusNormalizedRows_separate {K : Type*} [Field K] [Fintype K] {x : ℝ}
    (hx : 2 ≤ x) {p : ℕ} (hp : p.Prime) (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hCard : p ^ 2 ≤ Fintype.card K)
    (c : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x) → K)
    (h : ∀ a b : K, (∑ i, c i * (a ^ (i.2.val % p + p * i.1.val) * b ^ (i.2.val / p))) = 0) :
    c = 0 := by
  refine frobeniusJets_grid_separate (J := 1) (normalizedFrobeniusDegree p)
    (normalizedFrobeniusDegree_injective hp.pos) ?_ ?_ c ?_
  · intro i
    have hS := (sqrtFrobeniusDegree_lt_prime hx hLow i).1
    have h1 := Nat.mod_lt i.2.val hp.pos
    have h2 := Nat.mul_le_mul_left p (Nat.succ_le_of_lt hS)
    change i.2.val % p + p * i.1.val < Fintype.card K * 1
    rw [mul_one]
    have hPower : i.2.val % p + p * i.1.val < p ^ 2 := by
      rw [Nat.mul_succ] at h2
      rw [pow_two]
      omega
    exact hPower.trans_le hCard
  · intro i
    have hR := (sqrtFrobeniusDegree_lt_prime hx hLow i).2
    have hDiv : i.2.val / p < p := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa [pow_two] using hR)
    have hpSq : p ≤ p ^ 2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hp.pos (show 1 ≤ 2 by decide)
    exact hDiv.trans_le (hpSq.trans hCard)
  · intro a b j hj
    have hj' : j = 0 := by omega
    subst j
    simpa [normalizedFrobeniusDegree, monomialJet] using h a b

private theorem exists_normalized_value_minor {K Rows Cols : Type*} [Field K] [Fintype Rows]
    [DecidableEq Rows] (M : Rows → Cols → K)
    (h : ∀ c : Rows → K, (∀ v, (∑ i, c i * M i v) = 0) → c = 0) :
    ∃ node : Rows → Cols, (Matrix.of fun i j => M i (node j)).det ≠ 0 := by
  classical
  let col (v : Cols) : Rows → K := fun i => M i v
  let B := Pi.basisFun K Rows
  have hSpan : Submodule.span K (Set.range col) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf, hfker⟩ := Submodule.exists_le_ker_of_lt_top _
      (lt_top_iff_ne_top.mpr hne)
    have hc : (fun i => f (B i)) = 0 := h _ (fun v => by
      have hv : f (col v) = 0 := hfker (Submodule.subset_span ⟨v, rfl⟩)
      have he := congrArg f (B.sum_repr (col v))
      simpa only [B, col, Pi.basisFun_repr, map_sum, map_smul, smul_eq_mul,
        mul_comm, hv] using he)
    apply hf
    exact B.ext (congrFun hc)
  obtain ⟨ι, node, _, hSpan', hLin⟩ := exists_linearIndependent' K col
  let B' := Module.Basis.mk hLin ((hSpan'.trans hSpan).ge)
  let e := B.indexEquiv B'
  let N := Matrix.of fun i j => M i (node (e j))
  have hN : LinearIndependent K N.col := by
    change LinearIndependent K (fun j i => M i (node (e j)))
    simpa only [col, Function.comp_def] using hLin.comp e e.injective
  exact ⟨node ∘ e, ((Matrix.isUnit_iff_isUnit_det N).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hN)).ne_zero⟩

/-- At an unramified place with at least \(p^2\) residues, exact integral
divisibility by \(p\) yields a minor with the least possible exponent. -/
theorem sqrtFrobeniusMinorIdeal_exactExponent_of_normalized_values {R : Type*}
    [CommRing R] [IsDedekindDomain R] (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)]
    (σ : R ≃+* R) {x : ℝ} (hx : 2 ≤ x) {p : ℕ} [CharP (R ⧸ P) p] (hp : p.Prime)
    (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ)) (hUnramified : (p : R) ∉ P ^ 2)
    (hCard : p ^ 2 ≤ Fintype.card (R ⧸ P)) (hDiv : ∀ a : R, (p : R) ∣ a ^ p - σ a) :
    let e := frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p
    sqrtFrobeniusMinorIdeal x σ.toRingHom ≤ P ^ e ∧
      ¬ sqrtFrobeniusMinorIdeal x σ.toRingHom ≤ P ^ (e + 1) := by
  classical
  let k := gaussianSqrtTriangleScale x
  let Rows := FrobeniusTriangleRow x k
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  let q := Ideal.Quotient.mk P
  choose digit hd using hDiv
  have hqP : q (p : R) = 0 := quotient_primeCast_zero P
  have hpP : (p : R) ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hqP
  have hp₀ : (p : R) ≠ 0 := fun he => hUnramified (he ▸ (P ^ 2).zero_mem)
  have hFrob (a : R) : q (σ a) = q a ^ p := by
    have he := congrArg q (hd a)
    rw [map_sub, map_pow, map_mul, hqP, zero_mul] at he
    exact (sub_eq_zero.mp he).symm
  refine ⟨sqrtFrobeniusMinorIdeal_le_pow_of_frobenius P σ.toRingHom hx hp hLow hFrob, ?_⟩
  let M (i : Rows) (a : R) : R ⧸ P :=
    q a ^ (i.2.val % p) * q (σ a) ^ i.1.val * q (digit a) ^ (i.2.val / p)
  have hSep (c : Rows → R ⧸ P) (h : ∀ a, (∑ i, c i * M i a) = 0) : c = 0 := by
    apply sqrtFrobeniusNormalizedRows_separate hx hp hLow hCard c
    intro a b
    obtain ⟨v, hv⟩ := normalizedFrobenius_pair_surjective P hp₀ σ digit hd (a,b)
    have ha : q v = a := congrArg Prod.fst hv
    have hb : q (digit v) = b := congrArg Prod.snd hv
    simpa only [M, hFrob, ha, hb, ← pow_mul, ← pow_add] using h v
  obtain ⟨node, hDet⟩ := exists_normalized_value_minor M hSep
  let N := Matrix.of fun (i j : Rows) =>
    node j ^ (i.2.val % p) * (σ (node j)) ^ i.1.val * (digit (node j)) ^ (i.2.val / p)
  have hMap : q.mapMatrix N = Matrix.of fun i j => M i (node j) := by
    ext i j
    change q (N i j) = M i (node j)
    simp only [N, M, Matrix.of_apply, map_mul, map_pow]
  have hUnit : N.det ∉ P := by
    intro h
    have hz : q N.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [RingHom.map_det, hMap] at hz
    exact hDet hz
  have hJ : 0 < gaussianSqrtJetCount x := by
    change 0 < ⌈x ^ (1 / 2 : ℝ)⌉₊
    apply Nat.lt_ceil.mpr
    simp only [Nat.cast_zero]
    exact Real.rpow_pos_of_pos (show (0 : ℝ) < x by linarith) _
  have hk : 0 < k := by dsimp [k, gaussianSqrtTriangleScale]; positivity
  let order : Rows → Fin (gaussianSqrtJetCount x) := fun _ => ⟨0,hJ⟩
  have hFact := frobeniusTriangleHasseMinor_value_factor σ.toRingHom hk hp.pos hLow
    (p : R) digit hd node order (fun _ => rfl)
  have hMember : frobeniusTriangleHasseMinor σ.toRingHom node order ∈
      sqrtFrobeniusMinorIdeal x σ.toRingHom :=
    Ideal.subset_span ⟨(node,order), rfl⟩
  intro hAll
  have hProd := hAll hMember
  rw [hFact] at hProd
  exact pow_notMem_succ_of_notMem_sq P hpP hUnramified _
    ((Ideal.IsMaximal.mem_pow_mul P hProd).resolve_right hUnit)

/-- The same exact normalized-value result as a count of ideal factors. -/
theorem sqrtFrobeniusMinorIdeal_count_of_normalized_values {R : Type*} [CommRing R]
    [IsDedekindDomain R] (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)]
    (σ : R ≃+* R) {x : ℝ} (hx : 2 ≤ x) {p : ℕ} [CharP (R ⧸ P) p] (hp : p.Prime)
    (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ)) (hUnramified : (p : R) ∉ P ^ 2)
    (hCard : p ^ 2 ≤ Fintype.card (R ⧸ P)) (hDiv : ∀ a : R, (p : R) ∣ a ^ p - σ a) :
    (normalizedFactors (sqrtFrobeniusMinorIdeal x σ.toRingHom)).count P =
      frobeniusTriangleDivisibility x (gaussianSqrtTriangleScale x) p := by
  classical
  obtain ⟨hLower, hUpper⟩ := sqrtFrobeniusMinorIdeal_exactExponent_of_normalized_values P σ hx hp
    hLow hUnramified hCard hDiv
  exact Ideal.count_normalizedFactors_eq hLower hUpper

#print axioms normalizedFrobenius_shift
#print axioms normalizedFrobenius_pair_surjective
#print axioms sqrtFrobeniusNormalizedRows_separate
#print axioms sqrtFrobeniusMinorIdeal_exactExponent_of_normalized_values
#print axioms sqrtFrobeniusMinorIdeal_count_of_normalized_values

end

end AlpogeSuperZeta
