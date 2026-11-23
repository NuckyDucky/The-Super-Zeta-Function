import QuarticArchivedCoefficients
import IdealNormCoprime
import IdealMul

/-! The Gaussian weights of coprime norm multiply by the same ideal
factorization that proves multiplicativity of ordinary ideal counts. -/

namespace QuarticModel

open ArithmeticFunction FieldCoefficientTransfer
open scoped Classical

theorem signedIdealNormSum_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    signedIdealNormSum (m*n) = signedIdealNormSum m * signedIdealNormSum n := by
  let : Fintype (GaussianNormFiber m) := Fintype.ofFinite _
  let : Fintype (GaussianNormFiber n) := Fintype.ofFinite _
  unfold signedIdealNormSum
  rw [← (IdealNormCoprime.splitEquiv (R := GaussianInt) hmn).tsum_eq
    (fun I => (archivedIdealCharacter I.val : ℂ))]
  simp only [tsum_fintype, IdealNormCoprime.splitEquiv, Equiv.coe_fn_mk, map_mul, Int.cast_mul,
    Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem signedIdealCoefficients_multiplicative : signedIdealCoefficients.IsMultiplicative := by
  refine IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
  · let : Unique (GaussianNormFiber 1) :=
      { default := ⟨⊤, by simp⟩
        uniq := fun I => Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.property) }
    simp [signedIdealCoefficients, toArithmeticFunction, signedIdealNormSum]
    have h (I : GaussianNormFiber 1) : I.val = 1 :=
      (Ideal.absNorm_eq_one_iff.mp I.property).trans Ideal.one_eq_top.symm
    rw [h, map_one]
  · intro m n hm hn hmn
    simpa [signedIdealCoefficients, toArithmeticFunction, hm, hn] using signedIdealNormSum_mul_of_coprime hmn

/-- A single arithmetic-function equality, including all composite indices. -/
theorem idealCounts_eq_archived_convolution :
    idealCounts K = zetaCoeff * betaCoeff * signedIdealCoefficients := by
  have hb : betaCoeff.IsMultiplicative := chi4.isMultiplicative_toArithmeticFunction
  exact (IsMultiplicative.eq_iff_eq_on_prime_powers (idealCounts K) (idealCounts_mul K)
    (zetaCoeff * betaCoeff * signedIdealCoefficients)
    ((zetaCoeff_mul.mul hb).mul signedIdealCoefficients_multiplicative)).mpr
      idealCounts_primePower_eq_archived_convolution

#print axioms signedIdealCoefficients_multiplicative
#print axioms idealCounts_eq_archived_convolution

end QuarticModel
