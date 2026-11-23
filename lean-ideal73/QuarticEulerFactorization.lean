import GaussianBaseEuler

/-! Separate the rational Euler denominator of the actual quartic into
its unweighted Gaussian factors and its relative discriminant factors. -/

namespace QuarticModel

open NumberField FieldCoefficientTransfer
open scoped Classical

attribute [local instance] Ideal.Quotient.field

local notation "T" => (PowerSeries.X : PowerSeries ℂ)

noncomputable def quarticDiscriminantSign (p : ℕ) [Fact p.Prime]
    (I : ↥(gaussianPrimesAbove p)) : ℤ :=
  let : I.val.IsMaximal := gaussianPrimesAbove_isMaximal I.property
  let : Finite (GaussianInt ⧸ I.val) := gaussian_finiteQuotient I.val (gaussianPrimesAbove_ne_bot I.property)
  let : Fintype (GaussianInt ⧸ I.val) := Fintype.ofFinite _
  if (2 : GaussianInt ⧸ I.val) = 0 then 1
  else quadraticChar (GaussianInt ⧸ I.val) (Ideal.Quotient.mk I.val gaussianDiscriminant)

private theorem relative_euler_eval (p : ℕ) [Fact p.Prime] (I : ↥(gaussianPrimesAbove p)) :
    (quarticEulerDenominator I.val).eval₂ (Int.castRingHom (PowerSeries ℂ)) (T^(I.val.inertiaDeg ℤ)) =
      (1-T^(I.val.inertiaDeg ℤ)) *
        (1-(quarticDiscriminantSign p I : PowerSeries ℂ)*T^(I.val.inertiaDeg ℤ)) := by
  let : I.val.IsMaximal := gaussianPrimesAbove_isMaximal I.property
  have hI := gaussianPrimesAbove_ne_bot I.property
  let : Finite (GaussianInt ⧸ I.val) := gaussian_finiteQuotient I.val hI
  let : Fintype (GaussianInt ⧸ I.val) := Fintype.ofFinite _
  by_cases h : (2 : GaussianInt ⧸ I.val) = 0
  · rw [quartic_even_euler_denominator _ hI h]
    simp [quarticDiscriminantSign, h, pow_two]
  · rw [quartic_odd_euler_denominator _ hI h]
    simp only [Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_one,
      Polynomial.eval₂_C, Polynomial.eval₂_X, quarticDiscriminantSign, if_neg h]
    rfl

/-- The reciprocal of the quartic local series is the product of the
rational zeta, beta, and Gaussian discriminant denominators. -/
theorem rational_euler_denominator_factored (p : ℕ) [Fact p.Prime] :
    (∏ P : PrimeAbove K p, (1-T^(P.val.inertiaDeg ℤ))) =
      ((1-T)*(1-(ZMod.χ₄ (p : ZMod 4) : PowerSeries ℂ)*T)) *
        ∏ I : ↥(gaussianPrimesAbove p), (1-(quarticDiscriminantSign p I : PowerSeries ℂ)*T^(I.val.inertiaDeg ℤ)) := by
  rw [rational_euler_denominator_via_gaussian,
    ← Finset.prod_coe_sort (gaussianPrimesAbove p)
      (fun I => (quarticEulerDenominator I).eval₂ (Int.castRingHom (PowerSeries ℂ)) (T^(I.inertiaDeg ℤ)))]
  simp_rw [relative_euler_eval]
  rw [Finset.prod_mul_distrib, Finset.prod_coe_sort (gaussianPrimesAbove p)
    (fun I => 1-T^(I.inertiaDeg ℤ)), gaussian_base_euler_denominator]

theorem fieldLocalEulerSeries_mul_character_denominators (p : ℕ) [Fact p.Prime] :
    fieldLocalEulerSeries K p *
      (((1-T)*(1-(ZMod.χ₄ (p : ZMod 4) : PowerSeries ℂ)*T)) *
        ∏ I : ↥(gaussianPrimesAbove p), (1-(quarticDiscriminantSign p I : PowerSeries ℂ)*T^(I.val.inertiaDeg ℤ))) =
        1 := by
  rw [← rational_euler_denominator_factored]
  exact fieldLocalEulerSeries_mul_denominator K p

#print axioms rational_euler_denominator_factored
#print axioms fieldLocalEulerSeries_mul_character_denominators

end QuarticModel
