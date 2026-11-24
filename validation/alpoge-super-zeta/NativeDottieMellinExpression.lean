import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Real expressions for the finite part of the first-disk Mellin coefficients.
The same definitions can be used with each pinned Lean toolchain. -/
noncomputable section

namespace DottieOriented.NativeSpectrum

open MeasureTheory

/-- The two determinant values after multiplying each by the same
positive factor $\exp(-2x)$. -/
def finiteLogGap (x : ℝ) : ℝ :=
  let b := Real.exp (-x)
  let t := 1-b^2
  let a := t^2+(3+4*x^2)*b^2
  Real.log ((a-2*x*b*t)/(a+2*x*b*t))

/-- The real or imaginary part of the normalized Mellin integrand. -/
def finiteCoefficientDensity (imaginary : Bool) (k : ℕ) (u : ℝ) : ℝ :=
  (-2*u)^k/(k.factorial:ℝ) * Real.exp (-u/2) * finiteLogGap (Real.exp u) *
    (if imaginary then -Real.sin (7067363/500000*u) else Real.cos (7067363/500000*u))

def finiteCoefficient (imaginary : Bool) (k : ℕ) : ℝ :=
  ∫ u in (-32:ℝ)..5, finiteCoefficientDensity imaginary k u

end DottieOriented.NativeSpectrum
end
