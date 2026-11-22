import SuperZeta.QuarterLine.QuartetShiftBoundsSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals

namespace SuperZeta.QuartetShiftBounds
noncomputable section
open Real Set Filter MeasureTheory

/-- The real majorant after the two conjugate powers have been estimated separately. -/
def quarterWeight (x : ℝ) : ℝ := (4+Real.log x)*x^(-(3/2):ℝ)

private lemma weight_deriv {x : ℝ} (hx : 0<x) :
    HasDerivAt quarterWeight ((-5-3/2*Real.log x)*x^(-(3/2):ℝ)/x) x := by
  have hd := ((Real.hasDerivAt_log hx.ne').const_add 4).mul
    (Real.hasDerivAt_rpow_const (p:=-(3/2:ℝ)) (Or.inl hx.ne'))
  convert hd using 1
  rw [Real.rpow_sub_one hx.ne']
  ring

private lemma weight_anti : AntitoneOn quarterWeight (Ici 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro x hx
    exact (weight_deriv (lt_of_lt_of_le zero_lt_one hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (weight_deriv (lt_of_lt_of_le zero_lt_one (interior_subset hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 1 ≤ x := interior_subset hx
    have hp := zero_lt_one.trans_le hx'
    rw [(weight_deriv hp).deriv]
    have hl := Real.log_nonneg hx'
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)) hp.le

private def primitive (x : ℝ) : ℝ := -(12+2*Real.log x)*x^(-(1/2):ℝ)

private lemma primitive_deriv {x : ℝ} (hx : 0<x) :
    HasDerivAt primitive (quarterWeight x) x := by
  have hd := ((((Real.hasDerivAt_log hx.ne').const_mul 2).const_add 12).neg).mul
    (Real.hasDerivAt_rpow_const (p:=-(1/2:ℝ)) (Or.inl hx.ne'))
  convert hd using 1
  unfold quarterWeight
  rw [show -(3/2:ℝ) = -(1/2)-1 by norm_num, Real.rpow_sub_one hx.ne']
  ring

theorem partial_weight_le (N : ℕ) :
    (∑ i ∈ Finset.range N, quarterWeight ((i:ℝ)+2)) ≤ 12 := by
  have hN : (1:ℝ) ≤ 1+N := by linarith [Nat.cast_nonneg (α:=ℝ) N]
  have anti := weight_anti.mono (Icc_subset_Ici_self : Icc (1:ℝ) (1+N) ⊆ Ici 1)
  have cmp := anti.sum_le_integral (a:=N) (x₀:=1)
  have eqn : (∫ x in (1:ℝ)..1+N, quarterWeight x) = primitive (1+N)-primitive 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le hN] at hx
      exact primitive_deriv (lt_of_lt_of_le zero_lt_one hx.1)
    · rw [← uIcc_of_le hN] at anti; exact anti.intervalIntegrable
  have hp : primitive (1+N) ≤ 0 := by
    unfold primitive
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith [Real.log_nonneg hN]) (by positivity)
  have h1 : primitive 1 = -12 := by norm_num [primitive]
  have hwrite : ∀ i : ℕ, 1 + ((i+1:ℕ):ℝ) = (i:ℝ)+2 := fun i => by push_cast; ring
  simp only [hwrite,eqn,h1] at cmp
  linarith

theorem quarter_weight_total :
    (∑' i : ℕ, quarterWeight ((i:ℝ)+2)) ≤ 12 := by
  apply Real.tsum_le_of_sum_range_le _ partial_weight_le
  intro n
  unfold quarterWeight
  have h := Real.log_nonneg (show 1 ≤ (n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
  positivity

/-- Absolute convergence and the uniform bound on the sum of all levels above the first. -/
theorem sum_high_quartets {g : ℕ → ℂ} {B : ℝ} (hb : 0 ≤ B)
    (hg : ∀ n, ‖g n‖ ≤ B * quarterWeight ((n:ℝ)+2)) :
    Summable g ∧ ‖∑' n, g n‖ ≤ 12*B := by
  have hpos (n : ℕ) : 0 ≤ quarterWeight ((n:ℝ)+2) := by
    unfold quarterWeight
    have h := Real.log_nonneg (show 1 ≤ (n:ℝ)+2 by linarith [Nat.cast_nonneg (α:=ℝ) n])
    positivity
  have hsum := summable_of_sum_range_le hpos partial_weight_le
  have hs := Summable.of_norm_bounded _ (hsum.mul_left B) hg
  refine ⟨hs, ?_⟩
  calc
    ‖∑' n, g n‖ ≤ ∑' n, ‖g n‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑' n : ℕ, B*quarterWeight ((n:ℝ)+2) := Summable.tsum_le_tsum hg hs.norm (hsum.mul_left B)
    _ = B * ∑' n : ℕ, quarterWeight ((n:ℝ)+2) := tsum_mul_left
    _ ≤ 12*B := by nlinarith only [mul_le_mul_of_nonneg_left quarter_weight_total hb]

end
end SuperZeta.QuartetShiftBounds
