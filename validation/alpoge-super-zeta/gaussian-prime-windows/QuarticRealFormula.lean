import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! The same explicit quartic theta and its Mellin transform on both
toolchains. The Jacobi symbols use the three original prime denominators. -/

namespace QuarticRealFormula

noncomputable def scale : ℝ := Real.sqrt 26509772707289 / Real.pi

noncomputable def theta (u : ℝ) : ℝ :=
  ∑' p : ℕ × ℕ,
    let m : ℕ := p.1 + 1
    let n := p.2
    ((jacobiSym ((m : ℤ) + n * 32) 41 * jacobiSym ((m : ℤ) + n * 109) 457 *
      jacobiSym ((m : ℤ) + n * 516876951) 1414835497 : ℤ) : ℝ) *
      Real.exp (-((m ^ 2 + n ^ 2 : ℕ) : ℝ) * u)

noncomputable def completed : ℂ → ℂ :=
  mellin (fun t : ℝ => (theta (t / scale) : ℂ))

end QuarticRealFormula
