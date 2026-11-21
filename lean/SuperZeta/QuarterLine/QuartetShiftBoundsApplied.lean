import SuperZeta.QuarterLine.QuartetShiftBoundsTotal
import SuperZeta.QuarterLine.QuartetShiftContinuation

namespace SuperZeta.QuartetShiftBounds
noncomputable section
open QuartetShiftContinuation

/-- Sum of the real-reference differences from every conjugate pair after the first. -/
theorem tail_quarter (t : ℝ) :
    ‖∑' n, levelDiff (n+1) (quarter t)‖ ≤
    48 * ‖quarter t‖ * Real.exp (11*|t|/10) := by
  let B := 4*‖quarter t‖*Real.exp (11/10*|t|)
  have hb : 0 ≤ B := by dsimp [B]; positivity
  have bound (n : ℕ) : ‖levelDiff (n+1) (quarter t)‖ ≤ B*quarterWeight ((n:ℝ)+2) := by
    have h := levelDiff_le n (s:=quarter t) (by norm_num [quarter])
    apply h.trans_eq
    dsimp only [quarter, B, quarterWeight]
    push_cast
    rw [show -2*(1/4:ℝ)-1 = -(3/2) by norm_num]
    ring
  have h := (sum_high_quartets hb bound).2
  exact h.trans_eq (by dsimp [B]; rw [show 11*|t|/10=11/10*|t| by ring]; ring)

end
end SuperZeta.QuartetShiftBounds
