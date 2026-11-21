import PrimeIdealCoefficient
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.ComputeDegree

/-! The field obtained by adjoining a square root of −5045155 + 1027708 i. -/

noncomputable section
namespace QuarticModel
open Polynomial NumberField QuarticCoefficient

theorem monic_g : sqrtDeltaPolynomial.Monic := by
  unfold sqrtDeltaPolynomial
  monicity!

private abbrev residuePolynomial : (ZMod 3)[X] := X^4 + 2*X^2 + 2

private theorem eval_quadratic {q : (ZMod 3)[X]} (hq : q.Monic) (hd : q.natDegree = 2)
    (x : ZMod 3) : q.eval x = q.coeff 0 + q.coeff 1 * x + x^2 := by
  have hl : q.coeff 2 = 1 := hd ▸ hq.coeff_natDegree
  rw [Polynomial.eval_eq_sum_range, hd]
  simp [Finset.sum_range_succ, hl]

/-- Modulo three the quartic has constant value two at all three inputs.
Neither a linear factor nor two monic quadratic factors can have those values. -/
private theorem residue_irreducible : Irreducible residuePolynomial := by
  have hm : residuePolynomial.Monic := by unfold residuePolynomial; monicity!
  have hd : residuePolynomial.natDegree = 4 := by unfold residuePolynomial; compute_degree!
  have he : ∀ x : ZMod 3, residuePolynomial.eval x = 2 := by
    have hn : ∀ x : ZMod 3, x^4 + 2*x^2 + 2 = 2 := by decide
    simpa [residuePolynomial] using hn
  apply hm.irreducible_iff_lt_natDegree_lt (by intro h; simp [h] at hd) |>.2
  intro q hq hn hdiv
  rw [Finset.mem_Ioc, hd] at hn
  obtain ⟨r, hr⟩ := hdiv
  have hrm : r.Monic := hq.of_mul_monic_left (hr ▸ hm)
  have hqr (x : ZMod 3) : q.eval x * r.eval x = 2 := by rw [← eval_mul, ← hr, he]
  rcases (show q.natDegree = 1 ∨ q.natDegree = 2 by omega) with h₁ | h₂
  · have H := hqr (-(q.coeff 0))
    conv at H => lhs; lhs; rw [hq.eq_X_add_C h₁]
    simp at H
    exact (by decide : (0 : ZMod 3) ≠ 2) H
  · have hdeg := hq.natDegree_mul hrm
    rw [← hr, hd, h₂] at hdeg
    have hr₂ : r.natDegree = 2 := by omega
    have impossible : ∀ a b c d : ZMod 3,
        ¬ ∀ x : ZMod 3, (a + b*x + x^2) * (c + d*x + x^2) = 2 := by decide
    apply impossible (q.coeff 0) (q.coeff 1) (r.coeff 0) (r.coeff 1)
    simpa only [eval_quadratic hq h₂, eval_quadratic hrm hr₂] using hqr

theorem irreducible_g : Irreducible sqrtDeltaPolynomial := by
  apply monic_g.irreducible_of_irreducible_map (Int.castRingHom (ZMod 3))
  have h₁ : (10090310 : ZMod 3) = 2 := by decide
  have h₂ : (26509772707289 : ZMod 3) = 2 := by decide
  have hc₁ : (10090310 : (ZMod 3)[X]) = 2 := by
    simpa only [Polynomial.C_ofNat] using congrArg Polynomial.C h₁
  have hc₂ : (26509772707289 : (ZMod 3)[X]) = 2 := by
    simpa only [Polynomial.C_ofNat] using congrArg Polynomial.C h₂
  simpa only [sqrtDeltaPolynomial, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_mul, Polynomial.map_ofNat, hc₁, hc₂] using residue_irreducible

abbrev rationalPolynomial := sqrtDeltaPolynomial.map (algebraMap ℤ ℚ)

instance : Fact (Irreducible rationalPolynomial) :=
  ⟨monic_g.irreducible_iff_irreducible_map_fraction_map.mp irreducible_g⟩

/-- The rational quartic field with its distinguished root. -/
abbrev K := AdjoinRoot rationalPolynomial

instance : NumberField K := by
  let : Module.Finite ℚ K := (monic_g.map (algebraMap ℤ ℚ)).finite_adjoinRoot
  exact NumberField.of_module_finite ℚ K

theorem degree_four : Module.finrank ℚ K = 4 := by
  change Module.finrank ℚ (ℚ[X] ⧸ Ideal.span {rationalPolynomial}) = 4
  rw [finrank_quotient_span_eq_natDegree, rationalPolynomial, monic_g.natDegree_map]
  unfold sqrtDeltaPolynomial
  compute_degree!

private theorem root_relation : (AdjoinRoot.root rationalPolynomial)^4 +
    10090310*(AdjoinRoot.root rationalPolynomial)^2 + 26509772707289 = 0 := by
  have hp : rationalPolynomial = X^4 + 10090310 * X^2 + 26509772707289 := by
    simp only [rationalPolynomial, sqrtDeltaPolynomial, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_mul, Polynomial.map_ofNat]
  have h := AdjoinRoot.mk_self (f := rationalPolynomial)
  calc
    _ = AdjoinRoot.mk rationalPolynomial (X^4 + 10090310 * X^2 + 26509772707289) := by
      simp only [AdjoinRoot.root, map_add, map_mul, map_pow, map_ofNat]
    _ = 0 := (congrArg (AdjoinRoot.mk rationalPolynomial) hp.symm).trans h

private theorem root_aeval : aeval (AdjoinRoot.root rationalPolynomial) sqrtDeltaPolynomial = 0 := by
  simpa only [sqrtDeltaPolynomial, map_add, map_mul, map_pow, aeval_X, map_ofNat] using root_relation

def theta : 𝓞 K := ⟨AdjoinRoot.root rationalPolynomial, sqrtDeltaPolynomial, monic_g, root_aeval⟩

theorem minpoly_theta : minpoly ℤ theta = sqrtDeltaPolynomial := by
  rw [← RingOfIntegers.minpoly_coe]
  exact eq_of_monic_of_associated (minpoly.monic theta.2) monic_g
    ((minpoly.irreducible theta.2).associated_of_dvd irreducible_g
      (minpoly.isIntegrallyClosed_dvd theta.2 root_aeval))

theorem theta_generates : Algebra.adjoin ℚ {algebraMap (𝓞 K) K theta} = ⊤ :=
  AdjoinRoot.adjoinRoot_eq_top (f := rationalPolynomial)

def gaussianI : K := ((theta : K)^2 + 5045155) / 1027708

theorem gaussianI_sq : gaussianI^2 = -1 := by
  have h : (theta : K)^4 + 10090310 * (theta : K)^2 + 26509772707289 = 0 := by
    exact root_relation
  unfold gaussianI
  field_simp
  linear_combination h

theorem theta_sq : (theta : K)^2 = -5045155 + 1027708 * gaussianI := by
  unfold gaussianI
  ring

#print axioms minpoly_theta
#print axioms theta_generates
#print axioms gaussianI_sq
#print axioms theta_sq

end QuarticModel
