import QuarticEulerFactorization

/-! The archived character at the prime above two and its local factor. -/

namespace QuarticModel

open FieldCoefficientTransfer
open scoped Classical

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
attribute [local instance] Ideal.Quotient.field

theorem quarticDiscriminantSign_dyadic (I : ↥(gaussianPrimesAbove 2)) :
    quarticDiscriminantSign 2 I = archivedGaussianSign ⟨1,1⟩ := by
  have htwo : (2 : GaussianInt ⧸ I.val) = 0 := by
    rw [← map_ofNat (Ideal.Quotient.mk I.val)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (dyadic_gaussian_prime_two_mem I.property)
  have hs : archivedGaussianSign ⟨1,1⟩ = 1 := by norm_num [archivedGaussianSign]
  simp only [quarticDiscriminantSign, if_pos htwo, hs]

theorem fieldLocalEulerSeries_mul_archived_dyadic_denominator :
    let T := (PowerSeries.X : PowerSeries ℂ)
    fieldLocalEulerSeries K 2 * ((1-T)*(1-(archivedGaussianSign ⟨1,1⟩ : PowerSeries ℂ)*T)) = 1 := by
  have hc := fieldLocalEulerSeries_mul_character_denominators 2
  have hdeg (I : ↥(gaussianPrimesAbove 2)) : I.val.inertiaDeg ℤ = 1 := by
    have hm {A : Ideal GaussianInt} (hA : A ∈ gaussianPrimesAbove 2) :
        A = Ideal.span {(⟨1,1⟩ : GaussianInt)} := by
      simpa only [dyadic_gaussian_prime, Finset.mem_singleton] using hA
    rw [hm I.property, dyadic_gaussian_prime_degree]
  have hCard : Fintype.card ↥(gaussianPrimesAbove 2) = 1 := by
    rw [Fintype.card_coe, dyadic_gaussian_prime, Finset.card_singleton]
  simp_rw [quarticDiscriminantSign_dyadic, hdeg] at hc
  have hzero : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by decide
  simpa only [Finset.prod_const, Finset.card_univ, hCard, pow_one, hzero,
    Int.cast_zero, zero_mul, sub_zero, mul_one] using hc

#print axioms quarticDiscriminantSign_dyadic
#print axioms fieldLocalEulerSeries_mul_archived_dyadic_denominator

end QuarticModel
