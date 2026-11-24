import DottieQuickLog
import DottieLogMantissaTicks

namespace QuarticModel

open private dyadic_mantissa_bounds from DottieQuickLog

/-- The same lower endpoint as `dottieQuickLogLowerTicks`, with the exact
mantissa and `log 2` ticks retrieved from the checked table. -/
def dottieCachedLogLowerTicks (n : ℕ) : ℕ :=
  let k := n.log2 - 5
  let q : ℕ := 2^k
  let m := n / q
  let b := m*q
  dottieLogMantissaTicks[m]! + k * dottieLogMantissaTicks[2]! +
    logAtanhLowerTicks (2^96) (n-b) (n+b) 8

theorem dottieCachedLogLowerTicks_eq (n : ℕ) (hn : 0 < n) :
    dottieCachedLogLowerTicks n = dottieQuickLogLowerTicks n := by
  let k := n.log2-5
  let m := n / 2^k
  have hm : m ≤ 63 := (dyadic_mantissa_bounds n hn).2.1
  have ht : dottieLogMantissaTicks[2]! = logAtanhLowerTicks (2^96) 1 3 31 := by
    decide +kernel
  unfold dottieCachedLogLowerTicks dottieQuickLogLowerTicks
  dsimp only
  rw [dottieLogMantissaTicks_eq m (by omega), ht]

theorem dottieCachedLogLowerTicks_spec (n : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064) :
    (dottieCachedLogLowerTicks n : ℝ) ≤ (2:ℝ)^96 * Real.log n ∧
      (2:ℝ)^96 * Real.log n ≤ (dottieCachedLogLowerTicks n : ℝ) + 120 := by
  rw [dottieCachedLogLowerTicks_eq n hn]
  exact dottieQuickLogLowerTicks_spec n hn hcap

#print axioms dottieCachedLogLowerTicks_eq
#print axioms dottieCachedLogLowerTicks_spec

end QuarticModel
