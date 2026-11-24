import CrossleyQuarterWindow
import ArchivedQuarticZeroTransport

/-! Lee Crossley's compact difference in the original norm coordinate.
An anchor and lower bounds for the differences give upper bounds on the
signed shells, with the spectral point fixed throughout. -/

namespace SuperZeta.CrossleyQuarter

open Complex Finset
noncomputable section

def dyadicShell (R : ℝ → ℝ) (X : ℝ) : ℝ := R X - R (X/2)

theorem compact_eq_shells (R : ℝ → ℝ) (X : ℝ) :
    compact 2 R X = 2*dyadicShell R (X/2) - dyadicShell R X := by
  unfold compact dyadicShell
  rw [show X/2/2 = X/2^2 by ring]
  ring

theorem dyadicShell_div_pow_eq (R : ℝ → ℝ) (Y : ℝ) (n : ℕ) :
    dyadicShell R (2^n*Y)/2^n = dyadicShell R Y -
      ∑ j ∈ range n, compact 2 R (2^(j+1)*Y)/2^(j+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have harg : (2^(n+1)*Y)/2 = 2^n*Y := by rw [pow_succ]; ring
    have hstep := compact_eq_shells R (2^(n+1)*Y)
    rw [harg] at hstep
    calc
      _ = (2*dyadicShell R (2^n*Y) - compact 2 R (2^(n+1)*Y))/2^(n+1) := by
        rw [hstep]
        ring
      _ = dyadicShell R (2^n*Y)/2^n - compact 2 R (2^(n+1)*Y)/2^(n+1) := by
        rw [pow_succ (2:ℝ) n]
        ring
      _ = _ := by rw [ih, Finset.sum_range_succ]; ring

theorem dyadicShell_upper_of_compact_lower (R : ℝ → ℝ) (Y U : ℝ) (n : ℕ)
    (lower : ℕ → ℝ) (hanchor : dyadicShell R Y ≤ U)
    (hcompact : ∀ j < n, lower j ≤ compact 2 R (2^(j+1)*Y)) :
    dyadicShell R (2^n*Y)/2^n ≤ U - ∑ j ∈ range n, lower j/2^(j+1) := by
  rw [dyadicShell_div_pow_eq]
  exact sub_le_sub hanchor (Finset.sum_le_sum fun j hj =>
    div_le_div_of_nonneg_right (hcompact j (mem_range.mp hj)) (by positivity))

/-- An ordinary RH theorem, such as Crossley's `ordinary_rh`, supplies the
ordinary factor at the same off-line input in the critical strip. -/
theorem riemann_factor_ne_zero_of_ordinary_rh (hRH : RiemannHypothesis) {w : ℂ}
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) (hoff : w.re ≠ 1/2) :
    riemannZeta w ≠ 0 := by
  intro hz
  apply hoff (hRH w hz ?_ ?_)
  · rintro ⟨n, hn⟩
    have he := congrArg Complex.re hn
    norm_num [Complex.mul_re] at he
    nlinarith only [he, hw₀, Nat.cast_nonneg (α := ℝ) n]
  · intro he
    rw [he, Complex.one_re] at hw₁
    exact (lt_irrefl (1:ℝ)) hw₁

end
end SuperZeta.CrossleyQuarter

namespace QuarticModel

theorem archived_right_signed_budget_gap {T S : ℝ} (hS : 0 < S) {w : ℂ}
    (hw : w ∈ Metric.closedBall (archivedRightCenter T) (31/2048)) :
    189*((w.re-1/2)*S) < 190*((w.re-1/2)*S) := by
  have hx := archivedRightDisk_horizontal_gap hw
  have hu : 0 < (w.re-1/2)*S := mul_pos (by linarith only [hx]) hS
  linarith only [hu]

end QuarticModel

#print axioms SuperZeta.CrossleyQuarter.compact_eq_shells
#print axioms SuperZeta.CrossleyQuarter.dyadicShell_div_pow_eq
#print axioms SuperZeta.CrossleyQuarter.dyadicShell_upper_of_compact_lower
#print axioms SuperZeta.CrossleyQuarter.riemann_factor_ne_zero_of_ordinary_rh
#print axioms QuarticModel.archived_right_signed_budget_gap
