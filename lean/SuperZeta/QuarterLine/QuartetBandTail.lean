import SuperZeta.QuarterLine.QuartetShiftContinuation
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals

namespace SuperZeta.QuartetBandTail
noncomputable section
open Real Set MeasureTheory QuartetShiftContinuation

private def weight (a x : ℝ) := (4+Real.log x)*x^(-a-1)
private def mass (a : ℝ) := 4/a+(1/a)^2
private def primitive (a x : ℝ) := -(mass a + a⁻¹*Real.log x)*x^(-a)

private lemma antitone_weight {a : ℝ} (ha : 0<a) :
    AntitoneOn (weight a) (Ici 1) := by
  have derivW {x : ℝ} (hx : 0 < x) : HasDerivAt (weight a)
      ((1-(a+1)*(4+Real.log x))*x^(-a-1)/x) x := by
    have hd := ((Real.hasDerivAt_log hx.ne').const_add 4).mul
      (Real.hasDerivAt_rpow_const (p:=-a-1) (Or.inl hx.ne'))
    convert hd using 1
    rw [Real.rpow_sub_one (y:=-a-1) hx.ne']
    ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · intro x hx
    exact (derivW (zero_lt_one.trans_le hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (derivW (zero_lt_one.trans_le (interior_subset hx))).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx₁ : 1 ≤ x := interior_subset hx
    have hp := zero_lt_one.trans_le hx₁
    rw [(derivW hp).deriv]
    have hl := Real.log_nonneg hx₁
    have hh : 1-(a+1)*(4+Real.log x) ≤ 0 := by
      nlinarith [mul_nonneg ha.le hl]
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hh (by positivity)) hp.le

private lemma primitive_deriv {a x : ℝ} (ha : 0<a) (hx : 0<x) :
    HasDerivAt (primitive a) (weight a x) x := by
  have hd := ((((Real.hasDerivAt_log hx.ne').const_mul a⁻¹).const_add (mass a)).neg).mul
    (Real.hasDerivAt_rpow_const (p:=-a) (Or.inl hx.ne'))
  convert hd using 1
  unfold weight mass
  rw [Real.rpow_sub_one hx.ne']
  field_simp [ha.ne', hx.ne']
  ring

private lemma partial_weight_le {a : ℝ} (ha : 0<a) (N : ℕ) :
    (∑ i ∈ Finset.range N, weight a ((i:ℝ)+2)) ≤ mass a := by
  have hN : (1:ℝ) ≤ 1+N := by linarith [Nat.cast_nonneg (α:=ℝ) N]
  have anti := (antitone_weight ha).mono (Icc_subset_Ici_self : Icc (1:ℝ) (1+N) ⊆ Ici 1)
  have cmp := anti.sum_le_integral (a:=N) (x₀:=1)
  have eqn : (∫ x in (1:ℝ)..1+N, weight a x) = primitive a (1+N)-primitive a 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le hN] at hx
      exact primitive_deriv ha (zero_lt_one.trans_le hx.1)
    · rw [← uIcc_of_le hN] at anti; exact anti.intervalIntegrable
  have hp : primitive a (1+N) ≤ 0 := by
    unfold primitive mass
    have hl := Real.log_nonneg hN
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  have h1 : primitive a 1 = -mass a := by simp [primitive]
  have hwrite : ∀ i : ℕ, 1 + ((i+1:ℕ):ℝ) = (i:ℝ)+2 := fun i => by push_cast; ring
  simp only [hwrite,eqn,h1] at cmp
  linarith

/-- A single bound covers all later quartets at all heights whenever the real
part of the spectral input is at least a/2. -/
theorem tail_from_abscissa {a : ℝ} {s : ℂ} (ha : 0<a) (hs : a ≤ 2*s.re) :
    ‖∑' n, levelDiff (n+1) s‖ ≤
      (4/a+(1/a)^2) * (4*‖s‖*Real.exp (11*|s.im|/10)) := by
  let B := 4*‖s‖*Real.exp (11*|s.im|/10)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hn₁ (n : ℕ) : 1 ≤ (n:ℝ)+2 := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hpos (n : ℕ) : 0 ≤ weight a ((n:ℝ)+2) := by
    unfold weight
    have h := Real.log_nonneg (hn₁ n)
    positivity
  have hsum := summable_of_sum_range_le hpos (partial_weight_le ha)
  have bound (n : ℕ) : ‖levelDiff (n+1) s‖ ≤ B*weight a ((n:ℝ)+2) := by
    have h := levelDiff_le n (s:=s) (by linarith)
    push_cast at h
    have hlog := Real.log_nonneg (hn₁ n)
    apply h.trans
    calc
      _ = B * ((4+Real.log ((n:ℝ)+2)) * ((n:ℝ)+2)^(-2*s.re-1)) := by
        dsimp [B]; rw [show 11*|s.im|/10=11/10*|s.im| by ring]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        exact Real.rpow_le_rpow_of_exponent_le (hn₁ n) (by linarith)
  have hz := Summable.of_norm_bounded _ (hsum.mul_left B) bound
  have total := Real.tsum_le_of_sum_range_le hpos (partial_weight_le ha)
  calc
    ‖∑' n, levelDiff (n+1) s‖ ≤ ∑' n, ‖levelDiff (n+1) s‖ := norm_tsum_le_tsum_norm hz.norm
    _ ≤ ∑' n : ℕ, B*weight a ((n:ℝ)+2) := Summable.tsum_le_tsum bound hz.norm (hsum.mul_left B)
    _ = B * ∑' n : ℕ, weight a ((n:ℝ)+2) := tsum_mul_left
    _ ≤ _ := by change _ ≤ mass a * B; rw [mul_comm (mass a)]; gcongr

theorem tail_band {s : ℂ} (hs : (7/32:ℝ) ≤ s.re) :
    ‖∑' n, levelDiff (n+1) s‖ ≤ 60*‖s‖*Real.exp (11*|s.im|/10) := by
  have h := tail_from_abscissa (a:=7/16) (by norm_num) (s:=s) (by linarith)
  apply h.trans
  norm_num1
  nlinarith only [mul_nonneg (norm_nonneg s) (Real.exp_pos (11*|s.im|/10)).le]

end
end SuperZeta.QuartetBandTail
