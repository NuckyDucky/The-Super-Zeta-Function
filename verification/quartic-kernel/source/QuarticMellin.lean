import QuarticKernel
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

open Set Complex

namespace QuarticKernel

/-- The signed Gaussian norm Dirichlet series in its half-plane of absolute
convergence. `rightMellin` asserts its completion identity in `2 < re s`. -/
noncomputable def normSeries (s : ℂ) : ℂ :=
  ∑' n : ℕ, (coeff n : ℂ) / (n : ℂ)^s

private theorem normSeries_abs_summable {σ : ℝ} (hσ : 2 < σ) :
    Summable (fun n : ℕ => ‖(coeff n : ℂ)‖ / ((n : ℝ)/scale)^σ) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (1-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hden (n : ℕ) : 0 ≤ ((n : ℝ)/scale)^σ :=
    Real.rpow_nonneg (div_nonneg (Nat.cast_nonneg _) scale_pos.le) _
  refine Summable.of_nonneg_of_le (fun n => div_nonneg (norm_nonneg _) (hden n)) ?_
    (hs.mul_left (scale^σ))
  intro n
  cases n with
  | zero => simp only [coeff_zero, Int.cast_zero, norm_zero, zero_div]
            exact mul_nonneg (Real.rpow_nonneg scale_pos.le _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  | succ n =>
    have hn : 0 < (n.succ : ℝ) := by positivity
    have he : ‖(coeff (n+1) : ℂ)‖ = |(coeff (n+1) : ℝ)| := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    have hbound : ‖(coeff (n+1) : ℂ)‖ / ((n.succ : ℝ)/scale)^σ ≤
        (n.succ : ℝ) / ((n.succ : ℝ)/scale)^σ := by
      exact div_le_div_of_nonneg_right (he.trans_le (coeff_abs_le (n+1))) (hden _)
    exact hbound.trans_eq (by
      rw [Real.div_rpow hn.le scale_pos.le, div_div_eq_mul_div, Real.rpow_sub hn, Real.rpow_one]
      ring)

theorem rightMellin {s : ℂ} (hs : 2 < s.re) :
    mellin (fun t : ℝ => (theta (t/scale) : ℂ)) s =
      (scale : ℂ)^s * Complex.Gamma s * normSeries s := by
  have hp (n : ℕ) : (coeff n : ℂ) = 0 ∨ 0 < (n : ℝ)/scale := by
    cases n with
    | zero => exact Or.inl (by simp [coeff_zero])
    | succ n => exact Or.inr (div_pos (by positivity) scale_pos)
  have ht (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasSum (fun n : ℕ => (coeff n : ℂ) * Real.exp (-((n : ℝ)/scale)*t))
        (theta (t/scale) : ℂ) := by
    have hpos : 0 < t/scale := div_pos (mem_Ioi.mp ht) scale_pos
    have hx := Complex.hasSum_ofReal.mpr (theta_summable hpos).hasSum
    convert hx using 1
    ext n
    rw [Complex.ofReal_mul, Complex.ofReal_intCast, ← Real.exp_nat_mul]
    congr 2
    ring_nf
  have hm := hasSum_mellin hp (by linarith : 0 < s.re) ht (normSeries_abs_summable hs)
  rw [← hm.tsum_eq, normSeries, ← tsum_mul_left]
  apply tsum_congr
  intro n
  cases n with
  | zero => simp [coeff_zero]
  | succ n =>
    have hn : 0 ≤ (n.succ : ℝ) := by positivity
    have hsc : scale * ((n.succ : ℝ)/scale) = (n.succ : ℝ) := by field_simp [scale_pos.ne']
    have hpows : (scale : ℂ)^s * ((n.succ : ℝ)/scale : ℝ)^s = (n.succ : ℂ)^s := by
      rw [← Complex.mul_cpow_ofReal_nonneg scale_pos.le (div_nonneg hn scale_pos.le),
        ← Complex.ofReal_mul, hsc, Complex.ofReal_natCast]
    have hbase : (scale : ℂ) ≠ 0 := by exact_mod_cast scale_pos.ne'
    have hscale : (scale : ℂ)^s ≠ 0 := fun h => hbase ((Complex.cpow_eq_zero_iff _ _).mp h).1
    rw [← hpows, ← mul_div_assoc, mul_assoc, mul_div_mul_left _ _ hscale]

#print axioms rightMellin

end QuarticKernel
