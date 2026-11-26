import GaussianFrobeniusJetSeparation
import GaussianSqrtFrobeniusBudget
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! A residue field can rule out a prime from the ideal of all full
square-root triangle minors, without restricting the size of the nodes. -/

namespace AlpogeSuperZeta

open Finset

noncomputable section

private theorem exists_minor_of_separating {K Rows Cols : Type*}
    [Field K] [Fintype Rows] [DecidableEq Rows] (M : Rows → Cols → K)
    (h : ∀ c : Rows → K, (∀ j, (∑ i, c i * M i j) = 0) → c = 0) :
    ∃ j : Rows → Cols, (Matrix.of fun r c => M r (j c)).det ≠ 0 := by
  classical
  let col (j : Cols) : Rows → K := fun i => M i j
  let B := Pi.basisFun K Rows
  have hSpan : Submodule.span K (Set.range col) = ⊤ := by
    by_contra hne
    obtain ⟨f, hf, hfker⟩ := Submodule.exists_le_ker_of_lt_top
      (Submodule.span K (Set.range col)) (lt_top_iff_ne_top.mpr hne)
    have hc : (fun i => f (B i)) = 0 := h _ (fun j => by
      have hcol : f (col j) = 0 := hfker (Submodule.subset_span ⟨j, rfl⟩)
      have he := congrArg f (B.sum_repr (col j))
      simpa only [B, col, Pi.basisFun_repr, map_sum, map_smul, smul_eq_mul, mul_comm, hcol] using he)
    apply hf
    apply B.ext
    intro i
    exact congrFun hc i
  obtain ⟨ι, j, _, hjSpan, hjLin⟩ := exists_linearIndependent' K col
  let B' := Module.Basis.mk hjLin ((hjSpan.trans hSpan).ge)
  let e := B.indexEquiv B'
  let N := Matrix.of fun r c => M r (j (e c))
  have hN : LinearIndependent K N.col := by
    change LinearIndependent K (fun c i => M i (j (e c)))
    simpa only [col, Function.comp_def] using hjLin.comp e e.injective
  exact ⟨j ∘ e, ((Matrix.isUnit_iff_isUnit_det N).mp
    (Matrix.linearIndependent_cols_iff_isUnit.mp hN)).ne_zero⟩

theorem frobeniusTriangleDegree_injective (x k : ℝ) :
    Function.Injective (frobeniusTriangleDegree (x := x) (k := k)) := by
  rintro ⟨s, r⟩ ⟨t, u⟩ h
  have hs : s = t := Fin.ext (congrArg Prod.snd h)
  subst t
  have hr : r = u := Fin.ext (congrArg Prod.fst h)
  subst u
  rfl

private theorem sqrtFrobeniusRow_bounds {x : ℝ} (hx : 2 ≤ x)
    (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) :
    ((frobeniusTriangleDegree i).1 : ℝ) + ((frobeniusTriangleDegree i).2 : ℝ) < x ∧
      (frobeniusTriangleDegree i).2 < gaussianSqrtJetCount x := by
  let v := x ^ (1 / 2 : ℝ)
  let k := gaussianSqrtTriangleScale x
  have hx₁ : 1 ≤ x := by linarith
  have hv : 1 ≤ v := Real.one_le_rpow hx₁ (by norm_num)
  have hk : 1 ≤ k := by change (1 : ℝ) ≤ 2 * v; linarith
  have hsq : v ^ 2 = x := by rw [show v = Real.sqrt x from (Real.sqrt_eq_rpow x).symm, Real.sq_sqrt (by linarith)]
  have hFirst := Nat.lt_ceil.mp i.2.isLt
  change ((frobeniusTriangleDegree i).1 : ℝ) <
    x - k * ((frobeniusTriangleDegree i).2 : ℝ) at hFirst
  constructor
  · have hh := mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg (α := ℝ) (frobeniusTriangleDegree i).2)
    linarith
  · apply Nat.lt_ceil.mpr
    change ((frobeniusTriangleDegree i).2 : ℝ) < v
    by_contra! hh
    have hprod := mul_le_mul_of_nonneg_left hh (show 0 ≤ k from zero_le_one.trans hk)
    have he : k * v = 2 * x := by change (2 * v) * v = 2 * x; nlinarith
    linarith [Nat.cast_nonneg (α := ℝ) (frobeniusTriangleDegree i).1]

theorem sqrtFrobeniusScale_prime_bounds {x : ℝ} (hx : 2 ≤ x) {p : ℕ}
    (hp : gaussianSqrtTriangleScale x ≤ (p : ℝ)) :
    x ≤ ((p ^ 2 : ℕ) : ℝ) ∧ x ≤ ((p * gaussianSqrtJetCount x : ℕ) : ℝ) := by
  let v := x ^ (1 / 2 : ℝ)
  have hv : 0 ≤ v := Real.rpow_nonneg (by linarith) _
  have hsq : v ^ 2 = x := by rw [show v = Real.sqrt x from (Real.sqrt_eq_rpow x).symm, Real.sq_sqrt (by linarith)]
  have hJ : v ≤ (gaussianSqrtJetCount x : ℝ) := Nat.le_ceil v
  change 2 * v ≤ (p : ℝ) at hp
  constructor
  · push_cast
    have hh := pow_le_pow_left₀ (show 0 ≤ 2 * v by positivity) hp 2
    nlinarith
  · push_cast
    have hh := mul_le_mul hp hJ hv (Nat.cast_nonneg _)
    nlinarith

/-- If the exponent of the first coordinate is below the stride, the
exponent on a power graph remembers both original exponents. -/
theorem frobeniusPowerGraph_degree_injective {Rows : Type*} (degree : Rows → ℕ × ℕ)
    (hd : Function.Injective degree) {d : ℕ} (hd₀ : 0 < d)
    (hFirst : ∀ i, (degree i).1 < d) :
    Function.Injective fun i => (degree i).1 + d * (degree i).2 := by
  intro i j hij
  change (degree i).1 + d * (degree i).2 = (degree j).1 + d * (degree j).2 at hij
  have hr : (degree i).1 = (degree j).1 := by
    have h := congrArg (fun n : ℕ => n % d) hij
    simpa [Nat.add_mod, Nat.mod_eq_of_lt (hFirst i), Nat.mod_eq_of_lt (hFirst j)] using h
  rw [hr, Nat.add_left_cancel_iff] at hij
  exact hd (Prod.ext hr (Nat.eq_of_mul_eq_mul_left hd₀ hij))

def frobeniusTriangleHasseMatrix {R : Type*} [CommRing R] {x k : ℝ} {J : ℕ} (σ : R →+* R)
    (node : FrobeniusTriangleRow x k → R) (order : FrobeniusTriangleRow x k → Fin J) :
    Matrix (FrobeniusTriangleRow x k) (FrobeniusTriangleRow x k) R :=
  Matrix.of fun i j => monomialJet (frobeniusTriangleDegree i).1 (order j : ℕ) (node j) *
    σ (node j) ^ (frobeniusTriangleDegree i).2

/-- The Hasse minor at one ordered list of nodes and derivative orders. -/
def frobeniusTriangleHasseMinor {R : Type*} [CommRing R] {x k : ℝ} {J : ℕ} (σ : R →+* R)
    (node : FrobeniusTriangleRow x k → R) (order : FrobeniusTriangleRow x k → Fin J) : R :=
  (frobeniusTriangleHasseMatrix σ node order).det

def sqrtFrobeniusMinorIdeal {R : Type*} [CommRing R] (x : ℝ) (σ : R →+* R) : Ideal R :=
  Ideal.span (Set.range fun v :
    (FrobeniusTriangleRow x (gaussianSqrtTriangleScale x) → R) ×
      (FrobeniusTriangleRow x (gaussianSqrtTriangleScale x) → Fin (gaussianSqrtJetCount x)) =>
    frobeniusTriangleHasseMinor σ v.1 v.2)

private theorem sqrtFrobeniusMinorIdeal_not_le_of_separating {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] (x : ℝ) (σ : R →+* R)
    (h : ∀ c : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x) → R ⧸ P,
      (∀ a : R, ∀ j : Fin (gaussianSqrtJetCount x),
        (∑ i, c i * (monomialJet (frobeniusTriangleDegree i).1 (j : ℕ) (Ideal.Quotient.mk P a) *
          (Ideal.Quotient.mk P (σ a)) ^ (frobeniusTriangleDegree i).2)) = 0) → c = 0) :
    ¬ sqrtFrobeniusMinorIdeal x σ ≤ P := by
  classical
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  let q := Ideal.Quotient.mk P
  let M (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) (v : R × Fin (gaussianSqrtJetCount x)) :=
    monomialJet (frobeniusTriangleDegree i).1 (v.2 : ℕ) (q v.1) * q (σ v.1) ^ (frobeniusTriangleDegree i).2
  obtain ⟨v, hDet⟩ := exists_minor_of_separating M
    (fun c hc => h c fun a j => hc (a,j))
  intro hIdeal
  let a := fun j => (v j).1
  let order := fun j => (v j).2
  have hMember : frobeniusTriangleHasseMinor σ a order ∈ P :=
    hIdeal (Ideal.subset_span ⟨(a, order), rfl⟩)
  have hZero : q (frobeniusTriangleHasseMinor σ a order) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hMember
  let A := frobeniusTriangleHasseMatrix σ a order
  change q A.det = 0 at hZero
  rw [RingHom.map_det] at hZero
  have hMap : q.mapMatrix A = Matrix.of fun i j => M i (v j) := by
    apply Matrix.ext
    intro i j
    change q (monomialJet (frobeniusTriangleDegree i).1 (order j : ℕ) (a j) *
      σ (a j) ^ (frobeniusTriangleDegree i).2) = M i (v j)
    simp [M, a, order, monomialJet]
  exact hDet (hMap ▸ hZero)

theorem quotient_pair_surjective_of_comap_ne {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] (σ : R ≃+* R) (h : P.comap σ.toRingHom ≠ P) :
    Function.Surjective fun a : R => (Ideal.Quotient.mk P a, Ideal.Quotient.mk P (σ a)) := by
  let q := Ideal.Quotient.mk P
  let Q := P.comap σ.toRingHom
  let : Q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ σ.surjective
  rintro ⟨x, y⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := P) x
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (I := P) y
  obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.mp (Ideal.isCoprime_of_isMaximal (Ne.symm h))
  have hu₀ : q u = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hu
  have hv₁ : q v = 1 := by
    have hh := congrArg q huv
    simpa only [map_add, map_one, hu₀, zero_add] using hh
  have hv₀ : q (σ v) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (show σ v ∈ P from hv)
  have hu₁ : q (σ u) = 1 := by
    have hh := congrArg (fun z : R => q (σ z)) huv
    simpa only [map_add, map_one, hv₀, add_zero] using hh
  refine ⟨v * a + u * σ.symm b, Prod.ext ?_ ?_⟩
  · change q (v * a + u * σ.symm b) = x
    rw [map_add, map_mul, map_mul, hu₀, hv₁, one_mul, zero_mul, add_zero]
    exact ha
  · change q (σ (v * a + u * σ.symm b)) = y
    rw [map_add, map_mul, map_mul, map_add, map_mul, map_mul, hv₀, hu₁,
      zero_mul, one_mul, zero_add, RingEquiv.apply_symm_apply]
    exact hb

/-- Two different residue ideals allow independent coordinates. -/
theorem sqrtFrobeniusMinorIdeal_not_le_of_comap_ne {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)] (σ : R ≃+* R)
    {x : ℝ} (hx : 2 ≤ x) {p : ℕ} (hp : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hq : p ≤ Fintype.card (R ⧸ P)) (h : P.comap σ.toRingHom ≠ P) :
    ¬ sqrtFrobeniusMinorIdeal x σ.toRingHom ≤ P := by
  classical
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  apply sqrtFrobeniusMinorIdeal_not_le_of_separating P x σ.toRingHom
  intro c hc
  have hScale := sqrtFrobeniusScale_prime_bounds hx hp
  have hDegree (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) :
      (frobeniusTriangleDegree i).1 < Fintype.card (R ⧸ P) * gaussianSqrtJetCount x := by
    have hh := (sqrtFrobeniusRow_bounds hx i).1
    have hr : ((frobeniusTriangleDegree i).1 : ℝ) < x :=
      lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg _)) hh
    exact (Nat.cast_lt.mp (hr.trans_le hScale.2)).trans_le (Nat.mul_le_mul_right _ hq)
  have hSecond (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) :
      (frobeniusTriangleDegree i).2 < Fintype.card (R ⧸ P) :=
    (gaussianSqrtJet_order_lt_retainedPrime hp (sqrtFrobeniusRow_bounds hx i).2).trans_le hq
  apply frobeniusJets_grid_separate _ (frobeniusTriangleDegree_injective _ _) hDegree hSecond c
  intro a b j hj
  obtain ⟨z, hz⟩ := quotient_pair_surjective_of_comap_ne P σ h (a, b)
  have hza : Ideal.Quotient.mk P z = a := congrArg Prod.fst hz
  have hzb : Ideal.Quotient.mk P (σ.toRingHom z) = b := congrArg Prod.snd hz
  simpa only [Fin.val_mk, hza, hzb] using hc z ⟨j,hj⟩

/-- The identity reading has full row rank if the residue field
cardinality reaches the cutoff. -/
theorem sqrtFrobeniusMinorIdeal_not_le_of_diagonal {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)] (σ : R →+* R)
    {x : ℝ} (hx : 2 ≤ x) (hq : x ≤ (Fintype.card (R ⧸ P) : ℝ))
    (h : ∀ a : R, Ideal.Quotient.mk P (σ a) = Ideal.Quotient.mk P a) :
    ¬ sqrtFrobeniusMinorIdeal x σ ≤ P := by
  classical
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  apply sqrtFrobeniusMinorIdeal_not_le_of_separating P x σ
  intro c hc
  have hTotal (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) :
      (frobeniusTriangleDegree i).1 + (frobeniusTriangleDegree i).2 < Fintype.card (R ⧸ P) := by
    have ht := (sqrtFrobeniusRow_bounds hx i).1.trans_le hq
    exact Nat.cast_lt.mp (by simpa only [Nat.cast_add] using ht)
  apply frobeniusJets_diagonal_separate _ (frobeniusTriangleDegree_injective _ _) hTotal
    (fun i => (sqrtFrobeniusRow_bounds hx i).2) c
  intro a j hj
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (I := P) a
  simpa only [h, Fin.val_mk] using hc z ⟨j,hj⟩

private theorem sqrtFrobeniusMinorIdeal_not_le_of_powerGraph_degrees {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)] (σ : R →+* R)
    {x : ℝ} (hx : 0 < x) {d : ℕ} (hd : 0 < d)
    (hFirst : ∀ i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x),
      (frobeniusTriangleDegree i).1 < d)
    (hExp : ∀ i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x),
      (frobeniusTriangleDegree i).1 + d * (frobeniusTriangleDegree i).2 < Fintype.card (R ⧸ P))
    (h : ∀ a : R, Ideal.Quotient.mk P (σ a) = (Ideal.Quotient.mk P a) ^ d) :
    ¬ sqrtFrobeniusMinorIdeal x σ ≤ P := by
  classical
  let : Field (R ⧸ P) := Ideal.Quotient.field P
  apply sqrtFrobeniusMinorIdeal_not_le_of_separating P x σ
  intro c hc
  have hJ : 0 < gaussianSqrtJetCount x :=
    Nat.lt_ceil.mpr (by simpa using Real.rpow_pos_of_pos hx (1 / 2 : ℝ))
  apply frobeniusValues_powerGraph_separate frobeniusTriangleDegree d
    (frobeniusPowerGraph_degree_injective frobeniusTriangleDegree
      (frobeniusTriangleDegree_injective _ _) hd hFirst) hExp c
  intro a
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (I := P) a
  simpa only [h, Fin.val_mk] using hc z ⟨0,hJ⟩

/-- For order-four Frobenius, the central reading is the p-squared power
graph in a field with at least p to the fourth elements. Values suffice. -/
theorem sqrtFrobeniusMinorIdeal_not_le_of_powerGraph {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)] (σ : R →+* R)
    {x : ℝ} (hx : 2 ≤ x) {p : ℕ} (hp : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hq : p ^ 4 ≤ Fintype.card (R ⧸ P))
    (h : ∀ a : R, Ideal.Quotient.mk P (σ a) = (Ideal.Quotient.mk P a) ^ (p ^ 2)) :
    ¬ sqrtFrobeniusMinorIdeal x σ ≤ P := by
  let d (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) := frobeniusTriangleDegree i
  have hx₀ : 0 < x := by linarith
  have hp₀ : 0 < p := Nat.cast_pos.mp ((by dsimp [gaussianSqrtTriangleScale]; positivity :
    0 < gaussianSqrtTriangleScale x).trans_le hp)
  have hFirst (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) : (d i).1 < p ^ 2 := by
    have hr : ((d i).1 : ℝ) < x :=
      lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg _)) (sqrtFrobeniusRow_bounds hx i).1
    exact Nat.cast_lt.mp (hr.trans_le (sqrtFrobeniusScale_prime_bounds hx hp).1)
  have hExp (i : FrobeniusTriangleRow x (gaussianSqrtTriangleScale x)) :
      (d i).1 + p ^ 2 * (d i).2 < Fintype.card (R ⧸ P) := by
    have hs : (d i).2 < p :=
      gaussianSqrtJet_order_lt_retainedPrime hp (sqrtFrobeniusRow_bounds hx i).2
    calc
      _ < p ^ 2 + p ^ 2 * (d i).2 := Nat.add_lt_add_right (hFirst i) _
      _ = p ^ 2 * ((d i).2 + 1) := by ring
      _ ≤ p ^ 2 * p := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hs)
      _ = p ^ 3 := by ring
      _ ≤ p ^ 4 := Nat.pow_le_pow_right hp₀ (by decide)
      _ ≤ _ := hq
  exact sqrtFrobeniusMinorIdeal_not_le_of_powerGraph_degrees P σ hx₀ (pow_pos hp₀ _) hFirst hExp h

/-- Even the matching p-power graph separates all rows at or above
the upper cutoff when the residue field has at least p squared elements. -/
theorem sqrtFrobeniusMinorIdeal_not_le_of_powerGraph_at_upper_cutoff {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsMaximal] [Fintype (R ⧸ P)] (σ : R →+* R)
    {x : ℝ} (hx : 2 ≤ x) {p : ℕ} (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hHigh : x ≤ (p : ℝ)) (hq : p ^ 2 ≤ Fintype.card (R ⧸ P))
    (h : ∀ a : R, Ideal.Quotient.mk P (σ a) = (Ideal.Quotient.mk P a) ^ p) :
    ¬ sqrtFrobeniusMinorIdeal x σ ≤ P := by
  have hx₀ : 0 < x := by linarith
  have hp₀ : 0 < p := Nat.cast_pos.mp (hx₀.trans_le hHigh)
  refine sqrtFrobeniusMinorIdeal_not_le_of_powerGraph_degrees P σ hx₀ hp₀ ?_ ?_ h
  · intro i
    have hr : ((frobeniusTriangleDegree i).1 : ℝ) < x :=
      lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg _)) (sqrtFrobeniusRow_bounds hx i).1
    exact Nat.cast_lt.mp (hr.trans_le hHigh)
  · intro i
    let r := (frobeniusTriangleDegree i).1
    let s := (frobeniusTriangleDegree i).2
    have hr : (r : ℝ) < x :=
      lt_of_le_of_lt (le_add_of_nonneg_right (Nat.cast_nonneg _)) (sqrtFrobeniusRow_bounds hx i).1
    have hrp : r < p := Nat.cast_lt.mp (hr.trans_le hHigh)
    have hs : s < p := gaussianSqrtJet_order_lt_retainedPrime hLow (sqrtFrobeniusRow_bounds hx i).2
    calc
      r + p * s < p + p * s := Nat.add_lt_add_right hrp _
      _ = p * (s + 1) := by ring
      _ ≤ p * p := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hs)
      _ = p ^ 2 := by ring
      _ ≤ _ := hq

/-- On the matching Frobenius graph, the rows X^p and Y coincide
after reduction in every allowed jet. The strict upper endpoint
ensures both rows are present. -/
theorem sqrtFrobeniusMinorIdeal_le_of_frobenius {R : Type*} [CommRing R]
    (P : Ideal R) (σ : R →+* R) {x : ℝ} (hx : 2 ≤ x) {p : ℕ}
    [CharP (R ⧸ P) p] (hp : p.Prime) (hLow : gaussianSqrtTriangleScale x ≤ (p : ℝ))
    (hHigh : (p : ℝ) < x)
    (hFrob : ∀ a : R, Ideal.Quotient.mk P (σ a) = (Ideal.Quotient.mk P a) ^ p) :
    sqrtFrobeniusMinorIdeal x σ ≤ P := by
  classical
  let k := gaussianSqrtTriangleScale x
  have hx₀ : 0 < x := by linarith
  have hk : 0 < k := by dsimp [k, gaussianSqrtTriangleScale]; positivity
  have hkx : k < x := hLow.trans_lt hHigh
  let s₀ : Fin ⌈x / k⌉₊ := ⟨0, Nat.lt_ceil.mpr (by simpa using div_pos hx₀ hk)⟩
  let s₁ : Fin ⌈x / k⌉₊ := ⟨1, Nat.lt_ceil.mpr (by simpa using (one_lt_div hk).mpr hkx)⟩
  let i : FrobeniusTriangleRow x k := ⟨s₀, ⟨p, Nat.lt_ceil.mpr (by simpa [s₀] using hHigh)⟩⟩
  let j : FrobeniusTriangleRow x k := ⟨s₁, ⟨0, Nat.lt_ceil.mpr (by simpa [s₁] using sub_pos.mpr hkx)⟩⟩
  have hii : frobeniusTriangleDegree i = (p, 0) := rfl
  have hjj : frobeniusTriangleDegree j = (0, 1) := rfl
  have hDiff : i ≠ j := by
    intro he
    exact Nat.zero_ne_one (congrArg (fun r : FrobeniusTriangleRow x k => r.1.val) he)
  apply Ideal.span_le.mpr
  rintro _ ⟨⟨node, order⟩, rfl⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk P (frobeniusTriangleHasseMatrix σ node order).det = 0
  rw [RingHom.map_det]
  apply Matrix.det_zero_of_row_eq hDiff
  funext c
  let q := Ideal.Quotient.mk P
  change q ((monomialJet (frobeniusTriangleDegree i).1 (order c : ℕ) (node c)) *
      σ (node c) ^ (frobeniusTriangleDegree i).2) =
    q ((monomialJet (frobeniusTriangleDegree j).1 (order c : ℕ) (node c)) *
      σ (node c) ^ (frobeniusTriangleDegree j).2)
  rw [hii, hjj]
  have hOrder : (order c : ℕ) < p := gaussianSqrtJet_order_lt_retainedPrime hLow (order c).isLt
  have hRead := hasseFrobeniusJets_eq_below_p p hp (q (node c)) (q (σ (node c)))
    (hFrob (node c)).symm (order c : ℕ) hOrder
  have hJet (n : ℕ) : q (monomialJet n (order c : ℕ) (node c)) =
      monomialJet n (order c : ℕ) (q (node c)) := by simp [monomialJet]
  have hConstant (a : R ⧸ P) (m : ℕ) :
      monomialJet 0 m a = if m = 0 then 1 else 0 := by
    cases m <;> simp [monomialJet, Nat.choose_eq_zero_of_lt]
  simp only [pow_zero, pow_one, mul_one, map_mul, hJet, hRead, hConstant]
  split_ifs <;> simp

#print axioms frobeniusTriangleDegree_injective
#print axioms sqrtFrobeniusScale_prime_bounds
#print axioms sqrtFrobeniusMinorIdeal_le_of_frobenius
#print axioms frobeniusPowerGraph_degree_injective
#print axioms quotient_pair_surjective_of_comap_ne
#print axioms sqrtFrobeniusMinorIdeal_not_le_of_comap_ne
#print axioms sqrtFrobeniusMinorIdeal_not_le_of_diagonal
#print axioms sqrtFrobeniusMinorIdeal_not_le_of_powerGraph
#print axioms sqrtFrobeniusMinorIdeal_not_le_of_powerGraph_at_upper_cutoff

end
end AlpogeSuperZeta
