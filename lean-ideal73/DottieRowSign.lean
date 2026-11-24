import RelativeQuarticConductorPrimes
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

namespace QuarticModel

open private fastJacobiSym fastJacobiSym.eq from Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-- The exact archived sign on an integer lattice row. Direct use of Mathlib's
verified fast recurrence also makes the sign reduce in the kernel. -/
def dottieRowSign (a b : ℤ) : ℤ :=
  fastJacobiSym (a + b * 32) 41 * fastJacobiSym (a + b * 109) 457 *
    fastJacobiSym (a + b * 516876951) 1414835497

theorem dottieRowSign_eq_archivedGaussianSign (a b : ℤ) :
    dottieRowSign a b = archivedGaussianSign ⟨a, b⟩ := by
  simp only [dottieRowSign, archivedGaussianSign, ← fastJacobiSym.eq]

#print axioms dottieRowSign
#print axioms dottieRowSign_eq_archivedGaussianSign

end QuarticModel
