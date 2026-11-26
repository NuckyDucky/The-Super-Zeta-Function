import GaussianRealQuadraticWeights
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! A fixed two-by-two evaluation minor for the identity and central
Frobenius labels. Its norm is computed in the two quadratic algebras. -/

namespace AlpogeSuperZeta

open QuadraticAlgebra QuarticModel

abbrev ArchivedRealQuadraticOrder := QuadraticAlgebra ℤ 26509772707289 0

def archivedRealQuarticRadicand : ArchivedRealQuadraticOrder :=
  2 * (-5045155 + ω)

abbrev ArchivedMixedQuarticOrder :=
  QuadraticAlgebra ArchivedRealQuadraticOrder archivedRealQuarticRadicand 0

/-- The rows are `1` and `XY`. The two columns evaluate at
`(1,1)` and `(4+β, 4+sign*β)`. -/
def archivedFixedFrobeniusMinor (sign : ℤ) : Matrix (Fin 2) (Fin 2) ArchivedMixedQuarticOrder :=
  !![1, 1; 1, (4 + ω) * (4 + (sign : ArchivedMixedQuarticOrder) * ω)]

def archivedFixedFrobeniusMinorNorm (sign : ℤ) : ℤ :=
  (archivedFixedFrobeniusMinor sign).det.norm.norm

theorem archivedFixedFrobeniusMinor_norms :
    archivedFixedFrobeniusMinorNorm 1 = 17845486579044415855504745 ∧
      archivedFixedFrobeniusMinorNorm (-1) = 17845827611207068750107961 := by
  unfold archivedFixedFrobeniusMinorNorm
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  decide +kernel

/-- The expected unequal prime readings and two off-class divisors. -/
theorem archivedFixedFrobeniusMinor_local_test :
    (5 ∣ archivedFixedFrobeniusMinorNorm 1 ∧ ¬25 ∣ archivedFixedFrobeniusMinorNorm 1 ∧
      ¬5 ∣ archivedFixedFrobeniusMinorNorm (-1)) ∧
    (¬13 ∣ archivedFixedFrobeniusMinorNorm 1 ∧ 169 ∣ archivedFixedFrobeniusMinorNorm (-1) ∧
      ¬2197 ∣ archivedFixedFrobeniusMinorNorm (-1)) ∧
    (¬73 ∣ archivedFixedFrobeniusMinorNorm 1 ∧ ¬73 ∣ archivedFixedFrobeniusMinorNorm (-1)) ∧
    (49 ∣ archivedFixedFrobeniusMinorNorm 1 ∧ ¬343 ∣ archivedFixedFrobeniusMinorNorm 1) ∧
    (3721 ∣ archivedFixedFrobeniusMinorNorm (-1) ∧ ¬226981 ∣ archivedFixedFrobeniusMinorNorm (-1)) := by
  rw [archivedFixedFrobeniusMinor_norms.1, archivedFixedFrobeniusMinor_norms.2]
  decide +kernel

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance : Fact (Nat.Prime 61) := ⟨by decide⟩

/-- The extra divisors are genuine off-class factors of the fixed minor. -/
theorem archivedFixedFrobeniusMinor_off_class_weights :
    archivedGaussianPrimeWeight 7 = 0 ∧ archivedGaussianPrimeWeight 61 = 2 := by
  constructor
  · exact archivedGaussianPrimeWeight_inert (p := 7) (by decide)
  · rw [archivedGaussianPrimeWeight_split (p := 61) (by decide) 11 (by decide)]
    have h₁ : quadraticChar (ZMod 61) ((-5045155 : ZMod 61) + 1027708 * 11) = 1 := by
      decide +kernel
    have h₂ : quadraticChar (ZMod 61) ((-5045155 : ZMod 61) - 1027708 * 11) = 1 := by
      decide +kernel
    rw [h₁, h₂]
    norm_num

#print axioms archivedFixedFrobeniusMinor_norms
#print axioms archivedFixedFrobeniusMinor_local_test
#print axioms archivedFixedFrobeniusMinor_off_class_weights

end AlpogeSuperZeta
