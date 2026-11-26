import GaussianFrobeniusJetScaffold
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Nat.Choose.Dvd

/-! Ordinary derivatives can create a repeated row on the identity graph. -/

namespace AlpogeSuperZeta

/-- The ordinary X derivative of order j of X^r Y^s at (x,y). -/
def ordinaryMonomialJet {R : Type*} [CommRing R]
    (r s j : ℕ) (x y : R) : R :=
  (r.descFactorial j : R) * x ^ (r - j) * y ^ s

private theorem cast_descFactorial_char (R : Type*) [CommRing R]
    (p j : ℕ) [CharP R p] : (p.descFactorial (j + 1) : R) = 0 := by
  induction j with
  | zero => rw [Nat.descFactorial_one, CharP.cast_eq_zero R p]
  | succ j ih => rw [Nat.descFactorial_succ, Nat.cast_mul, ih, mul_zero]

theorem ordinaryJets_Xp_Yp_eq_on_diagonal {R : Type*} [CommRing R]
    (p : ℕ) [CharP R p] (x : R) (j : ℕ) :
    ordinaryMonomialJet p 0 j x x = ordinaryMonomialJet 0 p j x x := by
  cases j with
  | zero => simp [ordinaryMonomialJet]
  | succ j =>
    unfold ordinaryMonomialJet
    rw [cast_descFactorial_char R p j, Nat.zero_descFactorial_succ]
    simp

/-- The two rows agree in every column, regardless of the chosen nodes or
derivative orders. This applies to each full-row square minor. -/
theorem ordinaryIdentityGraphMinor_det_zero {R Rows : Type*} [CommRing R]
    [Fintype Rows] [DecidableEq Rows] (p : ℕ) [CharP R p] (hp : p ≠ 0)
    (degree : Rows → ℕ × ℕ) (x : Rows → R) (order : Rows → ℕ)
    (i j : Rows) (hi : degree i = (p, 0)) (hj : degree j = (0, p)) :
    Matrix.det (fun r c => ordinaryMonomialJet (degree r).1 (degree r).2 (order c) (x c) (x c)) =
      0 := by
  have hij : i ≠ j := by
    intro h
    exact hp (by simpa only [hi, hj] using congrArg (fun r => (degree r).1) h)
  apply Matrix.det_zero_of_row_eq hij
  funext c
  simp only [hi, hj]
  exact ordinaryJets_Xp_Yp_eq_on_diagonal p (x c) (order c)

/-- The coefficient derivative of order p does distinguish these two rows. -/
theorem hasseJets_Xp_Yp_ne_at_order_p {R : Type*} [CommRing R] [Nontrivial R]
    (p : ℕ) (hp : 0 < p) (x : R) :
    monomialJet p p x * x ^ (0 : ℕ) ≠ monomialJet 0 p x * x ^ p := by
  simp [monomialJet, Nat.choose_eq_zero_of_lt hp]

theorem hasseFrobeniusJets_eq_below_p {R : Type*} [CommRing R]
    (p : ℕ) [CharP R p] (hp : p.Prime) (x y : R) (hxy : x ^ p = y) (j : ℕ) (hj : j < p) :
    monomialJet p j x = if j = 0 then y else 0 := by
  by_cases h : j = 0
  · subst j
    simp [monomialJet, hxy]
  · have hcast : (p.choose j : R) = 0 :=
      (CharP.cast_eq_zero_iff R p _).2 (hp.dvd_choose_self h hj)
    rw [if_neg h, monomialJet, hcast, zero_mul]

/-- The order that separates the unwanted rows also breaks the wanted
Frobenius relation X^p = Y, even at a node where that relation holds. -/
theorem hasseFrobeniusJets_ne_at_order_p {R : Type*} [CommRing R] [Nontrivial R]
    (p : ℕ) (hp : p ≠ 0) (x y : R) :
    monomialJet p p x ≠ (if p = 0 then y else 0) := by
  simp [monomialJet, hp]

/-- Take the ordinary partial derivative of the given order, then evaluate. -/
noncomputable def ordinaryPolynomialJet {R σ : Type*} [CommRing R]
    (axis : σ) (j : ℕ) (point : σ → R) : MvPolynomial σ R →ₗ[R] R :=
  (MvPolynomial.aeval point).toLinearMap.comp ((MvPolynomial.pderiv axis).toLinearMap ^ j)

theorem ordinaryPolynomialJet_pow_eq_zero {R σ : Type*} [CommRing R]
    (p : ℕ) [CharP R p] (hp : p ≠ 0) (f : MvPolynomial σ R)
    (point : σ → R) (h : MvPolynomial.aeval point f = 0) (axis : σ) (j : ℕ) :
    ordinaryPolynomialJet axis j point (f ^ p) = 0 := by
  cases j with
  | zero =>
    simp only [ordinaryPolynomialJet, LinearMap.comp_apply, pow_zero, Module.End.one_apply,
      AlgHom.toLinearMap_apply]
    rw [map_pow, h, zero_pow hp]
  | succ j =>
    have hp' : (p : MvPolynomial σ R) = 0 := by
      rw [← map_natCast (MvPolynomial.C : R →+* MvPolynomial σ R), CharP.cast_eq_zero R p, map_zero]
    have hderiv : MvPolynomial.pderiv axis (f ^ p) = 0 := by
      rw [MvPolynomial.pderiv_pow, hp', zero_mul, zero_mul]
    unfold ordinaryPolynomialJet
    rw [LinearMap.comp_apply, pow_succ, Module.End.mul_apply]
    change MvPolynomial.aeval point
      (((MvPolynomial.pderiv axis).toLinearMap ^ j) (MvPolynomial.pderiv axis (f ^ p))) = 0
    rw [hderiv, map_zero, map_zero]

/-- Any nonzero relation whose pth power is in the row span annihilates
every square minor using all rows and ordinary derivative columns. -/
theorem ordinaryPolynomialMinor_det_zero {R σ Rows : Type*} [CommRing R] [IsDomain R]
    [Fintype Rows] [DecidableEq Rows] (p : ℕ) [CharP R p] (hp : p ≠ 0)
    (row : Rows → MvPolynomial σ R) (coeff : Rows → R)
    (f : MvPolynomial σ R) (hf : f ≠ 0)
    (hspan : ∑ r, coeff r • row r = f ^ p)
    (point : Rows → σ → R) (hpoint : ∀ c, MvPolynomial.aeval (point c) f = 0)
    (axis : Rows → σ) (order : Rows → ℕ) :
    (Matrix.of fun r c => ordinaryPolynomialJet (axis c) (order c) (point c) (row r)).det = 0 := by
  let A : Matrix Rows Rows R :=
    .of fun r c => ordinaryPolynomialJet (axis c) (order c) (point c) (row r)
  change A.det = 0
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  intro hLI
  have hsum : ∑ r, coeff r • A r = 0 := by
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    let read := ordinaryPolynomialJet (axis c) (order c) (point c)
    change ∑ r, coeff r • read (row r) = 0
    calc
      _ = read (∑ r, coeff r • row r) := by simp only [map_sum, map_smul]
      _ = 0 := by rw [hspan]; exact ordinaryPolynomialJet_pow_eq_zero p hp f (point c) (hpoint c) _ _
  have hcoeff := linearIndependent_iff'.mp hLI Finset.univ coeff hsum
  have hzero : ∑ r, coeff r • row r = 0 :=
    Finset.sum_eq_zero fun r hr => by rw [hcoeff r hr, zero_smul]
  exact pow_ne_zero p hf (hspan.symm.trans hzero)

#print axioms ordinaryJets_Xp_Yp_eq_on_diagonal
#print axioms ordinaryIdentityGraphMinor_det_zero
#print axioms hasseJets_Xp_Yp_ne_at_order_p
#print axioms hasseFrobeniusJets_eq_below_p
#print axioms hasseFrobeniusJets_ne_at_order_p
#print axioms ordinaryPolynomialJet_pow_eq_zero
#print axioms ordinaryPolynomialMinor_det_zero

end AlpogeSuperZeta
