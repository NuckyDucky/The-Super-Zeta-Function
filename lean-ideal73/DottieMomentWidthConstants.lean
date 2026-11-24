import DottieFixedTaylor

/-! Integer rounding for the uniform moment-weight error budget. The
Horner inputs have a pure imaginary argument of magnitude at most `8/5`.
The two entries bound the magnitude and the width, both in ticks. -/

namespace QuarticModel.DottieFixedIntervals

private def ceilNat (a b : ℕ) : ℕ := (a+b-1)/b

def halfPhaseHornerCaps : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (0,0)
  | terms+1, k =>
    let previous := halfPhaseHornerCaps terms (k+1)
    (ceilNat (8*previous.1) 5 + 2 + ceilNat scale.toNat k.factorial,
      ceilNat (8*previous.2) 5 + ceilNat previous.1 scale.toNat + 5)

def halfPhasePaddedCaps : ℕ × ℕ :=
  let pure := halfPhaseHornerCaps 24 0
  let pad := ceilNat (2^25*scale.toNat) (24:ℕ).factorial
  (pure.1+2*pad,pure.2+4*pad)

def phaseWidthCap : ℕ :=
  let p := halfPhasePaddedCaps
  ceilNat (2*p.1*p.2) scale.toNat + 8 + 4*ceilNat scale.toNat (10^13)

theorem phaseWidthCap_le : phaseWidthCap ≤ 15100000 := by decide +kernel

def inverseRootTickLower : ℕ := scale.toNat/38000-1

theorem inverseRootTickLower_sq_le :
    inverseRootTickLower^2*1442840576 ≤ scale.toNat^2 := by decide +kernel

/-- The minimum reciprocal square-root ticks absorb the absolute rounding
contribution even for the largest admissible norm. -/
theorem phaseWidth_budget_scalar :
    10^12*(3*15100000+70*scale.toNat) ≤
      (scale.toNat-10^12*15100000)*inverseRootTickLower := by decide +kernel

#print axioms phaseWidthCap_le
#print axioms inverseRootTickLower_sq_le
#print axioms phaseWidth_budget_scalar

end QuarticModel.DottieFixedIntervals
