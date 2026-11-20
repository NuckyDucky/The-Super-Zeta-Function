import SuperZeta.UnitSpectrum
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Tactic.Ring

namespace SuperZeta.TwoInputSpectrum

open Complex UnitSpectrum
open scoped ComplexConjugate BigOperators

noncomputable section

abbrev Index := Unit ⊕ (ℕ ⊕ ℕ)

/-- Principal complex powers of the same unit-coupling determinant root at two exponents. -/
def term (j : Index) (x y : ℂ) : ℂ :=
  squaredRoot j ^ (-x) * conj (squaredRoot j ^ (-y))

theorem conjugate_swap (j : Index) (x y : ℂ) : conj (term j x y) = term j y x := by
  simp [term, mul_comm]

theorem real_diagonal (j : Index) (x : ℂ) :
    term j x x = (normSq (squaredRoot j ^ (-x)) : ℂ) :=
  Complex.mul_conj _

/-- A zero second exponent recovers the original summand, including its branch. -/
theorem term_at_zero (j : Index) (x : ℂ) : term j x 0 = squaredRoot j ^ (-x) := by
  simp [term]

theorem unshifted_root_hasSum {x : ℂ} (hl : 1/2 < x.re) (hu : x.re < 1) :
    HasSum (fun j => term j x 0) (continuation x) := by
  simpa only [term_at_zero] using UnitSpectrum.root_hasSum hl hu

theorem angular_difference (x y psi : ℂ) :
    cos ((x - conj y) * psi) - cos ((x + conj y) * psi) =
    2 * sin (x * psi) * sin (conj y * psi) := by
  rw [sub_mul, add_mul, Complex.cos_sub, Complex.cos_add]
  ring

/-- The ratio of double and single shifts isolates cosh of the root angle.
The undivided identity includes the real-root case, where both differences vanish. -/
theorem double_shift (t : ℝ) :
    Real.cosh (2*t) - 1 = 2 * (Real.cosh t - 1) * (Real.cosh t + 1) := by
  rw [Real.cosh_two_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq t]

theorem isolated_angle (m t : ℝ) (hm : m ≠ 0) (ht : Real.cosh t - 1 ≠ 0) :
    (m * (Real.cosh (2*t) - 1)) / (2 * (m * (Real.cosh t - 1))) - 1 =
    Real.cosh t := by
  rw [double_shift]
  field_simp
  ring

end
end SuperZeta.TwoInputSpectrum
