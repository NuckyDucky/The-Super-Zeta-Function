import Discriminant23GaussMoments
import Discriminant23GaussTheta
import Discriminant23ClassMellinCentered

namespace FieldTarget

open Finset

/-- The common integer inputs for both class combinations and all degrees. -/
structure GaussPanelApproximation where
  expNode : ℤ
  principal : GaussianInt
  other : GaussianInt
  plusPhase : GaussianInt
  minusPhase : GaussianInt
  deriving DecidableEq

def gaussPanelApproximation (p : ℕ) (i : Fin 24) : GaussPanelApproximation where
  expNode := gaussPanelPositiveExpNumerator p i
  principal := gaussPanelThetaNumerator true p i
  other := gaussPanelThetaNumerator false p i
  plusPhase := gaussPanelExpNumerator (-1) 116 p i
  minusPhase := gaussPanelExpNumerator (-3) (-116) p i

def gaussWeightDenominator : ℕ := 32 * 10 ^ 30

def gaussCoefficientDenominator : ℕ := gaussWeightDenominator * gaussExpScale ^ 3 * gaussMomentScale

/-- Three factors use the exponential grid and the moment uses its own finer
grid. The quadrature weight keeps its original rational denominator. -/
def gaussPanelCoefficientNumerator (b : ℤ) (p : ℕ) (i : Fin 24) (k : ℕ)
    (a : GaussPanelApproximation) : GaussianInt :=
  ⟨(gauss24Pair i).2 * gaussPanelMomentNumerator p i k * a.expNode, 0⟩ *
    (a.principal + (b : GaussianInt) * a.other) *
    (a.plusPhase + ((-1 : GaussianInt) ^ k) * a.minusPhase)

def gaussPanelCoefficientSum (b : ℤ) (p k : ℕ) : GaussianInt :=
  ∑ i : Fin 24, gaussPanelCoefficientNumerator b p i k (gaussPanelApproximation p i)

def gaussCoefficientNumerator (b : ℤ) (k : ℕ) : GaussianInt :=
  ∑ p ∈ range 32, gaussPanelCoefficientSum b p k

end FieldTarget
