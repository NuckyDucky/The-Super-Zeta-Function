import QuarticArchivedPrimePowers
import Mathlib.Algebra.Ring.GeomSum

/-! At every rational prime the archived Gaussian Euler factors remove
seventh powers separately at each prime ideal. -/

namespace AlpogeSuperZeta

open Finset PowerSeries QuarticModel FieldCoefficientTransfer

noncomputable section

private theorem jacobi_pow_seven (a : ℤ) (d : ℕ) : jacobiSym a d ^ 7 = jacobiSym a d := by
  rcases jacobiSym.trichotomy a d with h | h | h <;> norm_num [h]

theorem archivedIdealCharacter_pow_seven (I : Ideal GaussianInt) :
    archivedIdealCharacter I ^ 7 = archivedIdealCharacter I := by
  obtain ⟨a, rfl⟩ : Submodule.IsPrincipal I := inferInstance
  simp only [archivedIdealCharacter_span, archivedGaussianSign, mul_pow, jacobi_pow_seven]

local notation "T" => (PowerSeries.X : PowerSeries ℂ)

/-- Retain exponents zero through six independently for every prime ideal
above the marked rational prime. -/
def signedSeventhFreeEulerSeries (p : ℕ) : PowerSeries ℂ :=
  ∏ I : ↥(gaussianPrimesAbove p),
    ∑ j ∈ range 7, (C (archivedIdealCharacter I.val : ℂ) * T ^ I.val.inertiaDeg ℤ) ^ j

theorem signedLocalEulerSeries_mul_seventhFreeNumerator (p : ℕ) :
    signedLocalEulerSeries p * (∏ I : ↥(gaussianPrimesAbove p),
      (1 - C (archivedIdealCharacter I.val : ℂ) * T ^ (7 * I.val.inertiaDeg ℤ))) =
      signedSeventhFreeEulerSeries p := by
  rw [signedSeventhFreeEulerSeries, signedLocalEulerSeries, ← prod_mul_distrib]
  apply prod_congr rfl
  intro I _
  let a := (archivedIdealCharacter I.val : ℂ)
  let d := I.val.inertiaDeg ℤ
  let t := C a * T ^ d
  let : I.val.IsPrime := Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor _
    (Multiset.mem_toFinset.mp I.property))
  have hd : d ≠ 0 := (I.val.inertiaDeg_pos ℤ).ne'
  have ha : a ^ 7 = a := by
    dsimp [a]
    exact_mod_cast archivedIdealCharacter_pow_seven I.val
  have ht : t ^ 7 = C a * T ^ (7 * d) := by
    dsimp [t]
    rw [mul_pow, ← map_pow, ha, ← pow_mul, Nat.mul_comm d 7]
  have hG : weightedGeometricAtDegree a d * (1 - t) = 1 :=
    weightedGeometricAtDegree_mul_denominator a hd
  change weightedGeometricAtDegree a d * (1 - C a * T ^ (7 * d)) =
    ∑ j ∈ range 7, t ^ j
  rw [← ht, ← geom_sum_mul_neg, mul_left_comm, hG, mul_one]

#print axioms archivedIdealCharacter_pow_seven
#print axioms signedLocalEulerSeries_mul_seventhFreeNumerator

end
end AlpogeSuperZeta
