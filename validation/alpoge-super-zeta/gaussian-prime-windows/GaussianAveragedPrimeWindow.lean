import GaussianAveragedRoundingResidual
import GaussianCutoffAverageMellin
import GaussianPrimePrefixKernel

/-! The averaged prime cutoff as a finite sum over signed prime prefixes. -/

namespace AlpogeSuperZeta

open Finset MeasureTheory Set
open scoped Classical

noncomputable section

private theorem signedPrimeWeight_zero : archivedGaussianSignedPrimeWeight 0 = 0 := by
  simp [archivedGaussianSignedPrimeWeight]

private def centeredPrimeTerm (p : ℕ) (t : ℝ) : ℝ :=
  archivedGaussianSignedPrimeWeight p *
    (t / (3 * (p : ℝ)) - squaredRoundingResidual (t / (p : ℝ)))

private theorem centeredPrimeTerm_eq_zero {p : ℕ} {t : ℝ} (ht : 0 ≤ t) (hp : t ≤ (p : ℝ)) :
    centeredPrimeTerm p t = 0 := by
  rcases Nat.eq_zero_or_pos p with rfl | hp₀
  · simp [centeredPrimeTerm, signedPrimeWeight_zero]
  · have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp₀
    rw [centeredPrimeTerm, squaredRoundingResidual_eq_div_three (by positivity) ((div_le_one hp').mpr hp)]
    ring

private theorem primeSquared_eq_fixed_sum {t x : ℝ} (ht : 1 ≤ t) (htx : t ≤ x) :
    archivedGaussianPrimeSquaredWindow t =
      (∑ p ∈ range (⌊x⌋₊ + 1), centeredPrimeTerm p t) - t / 3 * archivedGaussianPrimeCenter := by
  rw [archivedGaussianPrimeSquaredWindow_eq_sum ht]
  congr 1
  calc
    _ = ∑ p ∈ range (⌊t⌋₊ + 1), centeredPrimeTerm p t := by
      apply sum_congr rfl
      intro p _
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp [centeredPrimeTerm, signedPrimeWeight_zero]
      · rw [centeredPrimeTerm, squaredRoundingResidual_at_prime (one_pos.trans_le ht) hp]
        ring
    _ = _ := by
      refine sum_subset (range_mono (Nat.succ_le_succ (Nat.floor_le_floor htx))) ?_
      intro p _ hp
      have hfloor : ⌊t⌋₊ + 1 ≤ p := Nat.le_of_not_gt fun h => hp (mem_range.mpr h)
      have ht' : t ≤ (p : ℝ) := (Nat.lt_floor_add_one t).le.trans (by exact_mod_cast hfloor)
      exact centeredPrimeTerm_eq_zero (zero_le_one.trans ht) ht'

private theorem centeredPrimeTerm_integrable (p : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (centeredPrimeTerm p) volume a b := by
  have hR : IntervalIntegrable (fun t : ℝ => squaredRoundingResidual (t / (p : ℝ))) volume a b := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro u hu v hv huv
    exact squaredRoundingResidual_monotoneOn
      (mem_Ici.mpr (div_nonneg (ha.trans hu.1) (Nat.cast_nonneg _)))
      (mem_Ici.mpr (div_nonneg (ha.trans hv.1) (Nat.cast_nonneg _)))
      (div_le_div_of_nonneg_right huv (Nat.cast_nonneg _))
  have hlin : Continuous (fun t : ℝ => t / (3 * (p : ℝ))) := continuous_id.div_const _
  exact ((hlin.intervalIntegrable a b).sub hR).const_mul _

private theorem centeredPrimeTerm_average {x : ℝ} (hx : 0 < x) (p : ℕ) :
    (2 / x) * (∫ t in 0..x, centeredPrimeTerm p t) - centeredPrimeTerm p x =
      (-archivedGaussianSignedPrimeWeight p) * averagedRoundingResidual (x / (p : ℝ)) := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [centeredPrimeTerm, signedPrimeWeight_zero]
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hi : IntervalIntegrable (fun t : ℝ => t / (3 * (p : ℝ))) volume 0 x :=
    (continuous_id.div_const _).intervalIntegrable _ _
  have hR : IntervalIntegrable (fun t : ℝ => squaredRoundingResidual (t / (p : ℝ))) volume 0 x := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le hx.le]
    intro u hu v hv huv
    exact squaredRoundingResidual_monotoneOn
      (mem_Ici.mpr (div_nonneg hu.1 hp'.le)) (mem_Ici.mpr (div_nonneg hv.1 hp'.le))
      (div_le_div_of_nonneg_right huv hp'.le)
  unfold centeredPrimeTerm
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hi hR,
    intervalIntegral.integral_div, integral_id, intervalIntegral.integral_comp_div _ hp'.ne',
    zero_div, zero_pow (by decide), sub_zero, smul_eq_mul, averagedRoundingResidual]
  field_simp
  ring

/-- The averaged prime cutoff uses only primes up to the cutoff, plus the explicit
endpoint correction from starting the integral at one. -/
theorem averagedPrimeSquaredWindow_eq_sum {x : ℝ} (hx : 1 ≤ x) :
    averagedCutoff archivedGaussianPrimeSquaredWindow x =
      (∑ p ∈ range (⌊x⌋₊ + 1), (-archivedGaussianSignedPrimeWeight p) *
        averagedRoundingResidual (x / (p : ℝ))) + archivedGaussianPrimeCenter / (3 * x) := by
  let s := range (⌊x⌋₊ + 1)
  let c := archivedGaussianPrimeCenter
  let F (t : ℝ) := (∑ p ∈ s, centeredPrimeTerm p t) - c / 3 * t
  have hc : Continuous (fun t : ℝ => c / 3 * t) := continuous_id.const_mul _
  have hF (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable F volume a b := by
    simpa only [F, Finset.sum_apply] using
      (IntervalIntegrable.sum s fun p _ => centeredPrimeTerm_integrable p ha hab).sub
        (hc.intervalIntegrable _ _)
  have heq (t : ℝ) (ht : 1 ≤ t) (htx : t ≤ x) :
      archivedGaussianPrimeSquaredWindow t = F t := by
    rw [primeSquared_eq_fixed_sum ht htx]
    unfold F c s
    ring
  have hI₁ : (∫ t in 1..x, archivedGaussianPrimeSquaredWindow t) = ∫ t in 1..x, F t := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hx]
    exact fun t ht => heq t ht.1 ht.2
  have hI₀ : (∫ t in 0..1, F t) = -c / 6 := by
    calc
      _ = ∫ t in 0..1, -(c / 3) * t := by
        apply intervalIntegral.integral_congr
        rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
        intro t ht
        have hterm (p : ℕ) : centeredPrimeTerm p t = 0 := by
          rcases Nat.eq_zero_or_pos p with rfl | hp
          · simp [centeredPrimeTerm, signedPrimeWeight_zero]
          · exact centeredPrimeTerm_eq_zero ht.1 (ht.2.trans (by exact_mod_cast hp))
        simp [F, hterm]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        norm_num
        ring
  have hAll : (∫ t in 0..x, F t) =
      (∑ p ∈ s, ∫ t in 0..x, centeredPrimeTerm p t) - (c / 3) * (x ^ 2 / 2) := by
    have hInt : IntervalIntegrable (fun t => ∑ p ∈ s, centeredPrimeTerm p t) volume 0 x := by
      have hEq : (∑ i ∈ s, centeredPrimeTerm i) = (fun t => ∑ p ∈ s, centeredPrimeTerm p t) := by
        funext t
        rw [Finset.sum_apply]
      rw [← hEq]
      exact IntervalIntegrable.sum s
        (fun p _ => centeredPrimeTerm_integrable p le_rfl (zero_le_one.trans hx))
    unfold F
    rw [intervalIntegral.integral_sub hInt (hc.intervalIntegrable _ _),
      intervalIntegral.integral_finsetSum
        (fun p _ => centeredPrimeTerm_integrable p le_rfl (zero_le_one.trans hx)),
      intervalIntegral.integral_const_mul, integral_id, zero_pow (by decide), sub_zero]
  have hSum : (∫ t in 0..1, F t) + (∫ t in 1..x, F t) = ∫ t in 0..x, F t :=
    intervalIntegral.integral_add_adjacent_intervals (hF 0 1 le_rfl zero_le_one) (hF 1 x zero_le_one hx)
  have hAdj : (∫ t in 1..x, F t) = (∫ t in 0..x, F t) + c / 6 := by
    rw [hI₀] at hSum
    linarith
  have hx₀ := one_pos.trans_le hx
  rw [averagedCutoff_eq_interval _ hx, hI₁, hAdj, hAll, heq x hx le_rfl]
  change (2 / x) * ((_ - c / 3 * (x ^ 2 / 2)) + c / 6) -
      ((∑ p ∈ s, centeredPrimeTerm p x) - c / 3 * x) =
    (∑ p ∈ s, (-archivedGaussianSignedPrimeWeight p) * averagedRoundingResidual (x / (p : ℝ))) +
      c / (3 * x)
  rw [show (2 / x) * ((_ - c / 3 * (x ^ 2 / 2)) + c / 6) -
      ((∑ p ∈ s, centeredPrimeTerm p x) - c / 3 * x) =
      ((2 / x) * (∑ p ∈ s, ∫ t in 0..x, centeredPrimeTerm p t) -
        (∑ p ∈ s, centeredPrimeTerm p x)) + c / (3 * x) by
    field_simp
    ring, mul_sum, ← sum_sub_distrib]
  exact congrArg (fun y : ℝ => y + c / (3 * x)) (sum_congr rfl
    fun p _ => centeredPrimeTerm_average hx₀ p)

private def averagedPrimeWeight (x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 1 / 2 else averagedRoundingResidual (x / (n : ℝ))

private def averagedPrimeWeightStep (x : ℝ) (n : ℕ) : ℝ :=
  averagedPrimeWeight x n - averagedPrimeWeight x (n + 1)

private theorem averagedPrimeWeight_antitone {x : ℝ} (hx : 0 ≤ x) :
    Antitone (averagedPrimeWeight x) := by
  intro m n hmn
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Nat.eq_zero_of_le_zero hmn]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa [averagedPrimeWeight, hn.ne'] using
      averagedRoundingResidual_le_half (div_nonneg hx (Nat.cast_nonneg n))
  simp only [averagedPrimeWeight, if_neg hm.ne', if_neg hn.ne']
  apply averagedRoundingResidual_monotoneOn
    (mem_Ici.mpr (div_nonneg hx (Nat.cast_nonneg n)))
    (mem_Ici.mpr (div_nonneg hx (Nat.cast_nonneg m)))
  exact div_le_div_of_nonneg_left hx (Nat.cast_pos.mpr hm) (Nat.cast_le.mpr hmn)

private theorem averagedPrimeWeight_eq_zero {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : x ≤ (n : ℝ)) :
    averagedPrimeWeight x n = 0 := by
  have hn' := hx.trans_le hn
  have hpos : 0 < n := Nat.cast_pos.mp hn'
  rw [averagedPrimeWeight, if_neg hpos.ne',
    averagedRoundingResidual_eq_zero (div_nonneg hx.le hn'.le) ((div_le_one hn').mpr hn)]

private theorem averagedPrimeWeightStep_le {x : ℝ} (hx : 1 ≤ x) {n : ℕ} (hn : 0 < n) :
    averagedPrimeWeightStep x n ≤ (1 + 2 / 3 * Real.log x) / x := by
  have hx₀ := one_pos.trans_le hx
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hns₀ : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hord : x / ((n + 1 : ℕ) : ℝ) ≤ x / (n : ℝ) :=
    div_le_div_of_nonneg_left hx₀.le hn₀ (Nat.cast_le.mpr (Nat.le_succ n))
  have h := averagedRoundingResidual_sub_le_log (div_pos hx₀ hns₀) hord hx
    (div_le_self hx₀.le hn₁)
  rw [averagedPrimeWeightStep, averagedPrimeWeight, if_neg hn.ne',
    averagedPrimeWeight, if_neg (Nat.succ_ne_zero n)]
  refine h.trans_eq ?_
  push_cast
  field_simp
  ring

/-- Exact summation by parts with the kernel's endpoint equal to zero. -/
private theorem averagedPrimeSquaredWindow_eq_prefix {x : ℝ} (hx : 1 ≤ x) :
    averagedCutoff archivedGaussianPrimeSquaredWindow x =
      (∑ n ∈ range (⌊x⌋₊ + 1), archivedGaussianSignedPrimePrefix n * averagedPrimeWeightStep x n) +
      archivedGaussianPrimeCenter / (3 * x) := by
  let N := ⌊x⌋₊ + 1
  let P := archivedGaussianSignedPrimePrefix
  let b := archivedGaussianSignedPrimeWeight
  let w := averagedPrimeWeight x
  have hN : w N = 0 := averagedPrimeWeight_eq_zero (one_pos.trans_le hx) (by
    simpa only [N, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one x).le)
  have h := sum_range_by_parts w (fun p : ℕ => -b p) (N + 1)
  change (∑ p ∈ range (N + 1), w p • -b p) = w (N + 1 - 1) • P N -
    ∑ i ∈ range (N + 1 - 1), (w (i + 1) - w i) • P i at h
  simp only [Nat.add_sub_cancel, smul_eq_mul, sum_range_succ _ N, hN, zero_mul, add_zero, zero_sub] at h
  rw [averagedPrimeSquaredWindow_eq_sum hx]
  congr 1
  calc
    _ = ∑ p ∈ range N, w p * -b p := by
      apply sum_congr rfl
      intro p _
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp [w, b, signedPrimeWeight_zero]
      · dsimp only [w, b]
        rw [averagedPrimeWeight, if_neg hp.ne', mul_comm]
    _ = _ := by
      rw [h, ← sum_neg_distrib]
      exact sum_congr rfl fun p _ => by dsimp [P, averagedPrimeWeightStep, w]; ring

/-- A signed prime bound on \([Y,Y^{3/2}]\) suffices for the averaged prime cutoff
on \([Y^{5/4},Y^{3/2}]\). Only earlier prime prefixes require the global envelope. -/
theorem averagedPrimeSquaredWindow_le_of_local_prefix {x Y θ A B : ℝ} (hY : 1 ≤ Y)
    (hx₁ : Y ^ (5 / 4 : ℝ) ≤ x) (hx₂ : x ≤ Y ^ (3 / 2 : ℝ))
    (hθ : 1 / 2 < θ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hglobal : ∀ n : ℕ, archivedGaussianSignedPrimePrefix n ≤ B * (n : ℝ) ^ (7 / 8 : ℝ))
    (hlocal : ∀ n : ℕ, Y ≤ (n : ℝ) → (n : ℝ) ≤ Y ^ (3 / 2 : ℝ) →
      archivedGaussianSignedPrimePrefix n ≤ A * (n : ℝ) ^ θ) :
    averagedCutoff archivedGaussianPrimeSquaredWindow x ≤
      (A / 2 + 2 * B * (1 + (2 / 3) / (θ - 1 / 2)) +
        |archivedGaussianPrimeCenter| / 3) * x ^ θ := by
  have hY₀ := one_pos.trans_le hY
  have hYx : Y ≤ x := by
    calc
      Y = Y ^ (1 : ℝ) := (Real.rpow_one Y).symm
      _ ≤ Y ^ (5 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY (by norm_num)
      _ ≤ x := hx₁
  have hx := hY.trans hYx
  have hx₀ := one_pos.trans_le hx
  have hθ₀ : 0 ≤ θ := by linarith
  have hlog := Real.log_nonneg hx
  let e := θ - 1 / 2
  let c := archivedGaussianPrimeCenter
  let N := ⌊x⌋₊ + 1
  let w := averagedPrimeWeight x
  let κ := averagedPrimeWeightStep x
  let L (n : ℕ) := if 0 < n ∧ (n : ℝ) < Y then κ n else 0
  let P := archivedGaussianSignedPrimePrefix
  let D := (1 + 2 / 3 * Real.log x) / x
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have he : 0 < e := sub_pos.mpr hθ
  have hκ (n : ℕ) : 0 ≤ κ n :=
    sub_nonneg.mpr (averagedPrimeWeight_antitone hx₀.le (Nat.le_succ n))
  have hκsum : (∑ n ∈ range N, κ n) = 1 / 2 := by
    change (∑ n ∈ range N, (w n - w (n + 1))) = _
    rw [sum_range_sub' w, show w N = 0 from
      averagedPrimeWeight_eq_zero hx₀ (by
        simpa only [N, Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one x).le), sub_zero]
    simp [w, averagedPrimeWeight]
  have hLsum : (∑ n ∈ range N, L n) ≤ (Y + 1) * D := by
    let s : Finset ℕ := (range N).filter fun n : ℕ => 0 < n ∧ (n : ℝ) < Y
    have hs : s ⊆ range ⌈Y⌉₊ := by
      intro n hn
      exact Finset.mem_range.mpr (Nat.lt_ceil.mpr (mem_filter.mp hn).2.2)
    calc
      _ = ∑ n ∈ s, κ n := (sum_filter ..).symm
      _ ≤ ∑ _n ∈ s, D := sum_le_sum fun _ hn => averagedPrimeWeightStep_le hx (mem_filter.mp hn).2.1
      _ = (s.card : ℝ) * D := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr (Finset.card_le_card hs)).trans
        (by rw [card_range]; exact (Nat.ceil_lt_add_one hY₀.le).le)) hD
  have hterm (n : ℕ) (hn : n ∈ range N) :
      P n * κ n ≤ (A * x ^ θ) * κ n + (B * Y ^ (7 / 8 : ℝ)) * L n := by
    have hxθ : 0 ≤ x ^ θ := Real.rpow_nonneg hx₀.le _
    by_cases h₀ : n = 0
    · subst n
      have hp₀ : P 0 = 0 := by simp [P, archivedGaussianSignedPrimePrefix, signedPrimeWeight_zero]
      rw [hp₀, zero_mul]
      simpa only [L, Nat.lt_irrefl, false_and, if_false, mul_zero, add_zero] using
        mul_nonneg (mul_nonneg hA hxθ) (hκ 0)
    have hn₀ := Nat.pos_of_ne_zero h₀
    by_cases hnY : (n : ℝ) < Y
    · rw [show L n = κ n from if_pos ⟨hn₀, hnY⟩]
      have hP := (hglobal n).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg n) hnY.le (by norm_num)) hB)
      exact (mul_le_mul_of_nonneg_right hP (hκ n)).trans
        (le_add_of_nonneg_left (mul_nonneg (mul_nonneg hA hxθ) (hκ n)))
    have hnx : (n : ℝ) ≤ x :=
      (Nat.cast_le.mpr (Nat.le_of_lt_succ (mem_range.mp hn))).trans (Nat.floor_le hx₀.le)
    have hP := (hlocal n (le_of_not_gt hnY) (hnx.trans hx₂)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg n) hnx hθ₀) hA)
    simp only [L, hnY, and_false, if_false, mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right hP (hκ n)
  have hsum : (∑ n ∈ range N, P n * κ n) ≤ (A * x ^ θ) * (1 / 2) +
      (B * Y ^ (7 / 8 : ℝ)) * ((Y + 1) * D) := by
    calc
      _ ≤ ∑ n ∈ range N, ((A * x ^ θ) * κ n + (B * Y ^ (7 / 8 : ℝ)) * L n) :=
        sum_le_sum hterm
      _ ≤ _ := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum, hκsum]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hLsum (by positivity))
  have hpow : Y * Y ^ (7 / 8 : ℝ) ≤ x * x ^ (1 / 2 : ℝ) := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hY₀.le _) hx₁ (by norm_num : 0 ≤ (3 / 2 : ℝ))
    rw [← Real.rpow_mul hY₀.le, show (5 / 4 : ℝ) * (3 / 2) = 1 + 7 / 8 by norm_num,
      Real.rpow_add hY₀, Real.rpow_one, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx₀, Real.rpow_one] at h
    exact h
  have hfront : (B * Y ^ (7 / 8 : ℝ)) * ((Y + 1) * D) ≤
      (2 * B * (1 + (2 / 3) / e)) * x ^ θ := by
    have hY' : Y + 1 ≤ 2 * Y := by linarith
    have hlog' : 1 + 2 / 3 * Real.log x ≤ (1 + (2 / 3) / e) * x ^ e := by
      have h := add_le_add (Real.one_le_rpow hx he.le)
        (mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx₀.le he) (by norm_num : 0 ≤ (2 / 3 : ℝ)))
      exact h.trans_eq (by ring)
    calc
      _ ≤ (B * Y ^ (7 / 8 : ℝ)) * ((2 * Y) * D) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hY' hD) (by positivity)
      _ = (2 * B * (Y * Y ^ (7 / 8 : ℝ))) * D := by ring
      _ ≤ (2 * B * (x * x ^ (1 / 2 : ℝ))) * D :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hD
      _ = (2 * B * x ^ (1 / 2 : ℝ)) * (1 + 2 / 3 * Real.log x) := by
        dsimp [D]; field_simp
      _ ≤ (2 * B * x ^ (1 / 2 : ℝ)) * ((1 + (2 / 3) / e) * x ^ e) :=
        mul_le_mul_of_nonneg_left hlog' (by positivity)
      _ = (2 * B * (1 + (2 / 3) / e)) * (x ^ (1 / 2 : ℝ) * x ^ e) := by ring
      _ = _ := by rw [← Real.rpow_add hx₀, show (1 / 2 : ℝ) + e = θ by dsimp [e]; ring]
  have hc : c / (3 * x) ≤ (|c| / 3) * x ^ θ := by
    calc
      _ ≤ |c| / (3 * x) := div_le_div_of_nonneg_right (le_abs_self _) (by positivity)
      _ = (|c| / 3) / x := by ring
      _ ≤ |c| / 3 := div_le_self (by positivity) hx
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (Real.one_le_rpow hx hθ₀)
  rw [averagedPrimeSquaredWindow_eq_prefix hx]
  calc
    _ ≤ ((A * x ^ θ) * (1 / 2) + (B * Y ^ (7 / 8 : ℝ)) * ((Y + 1) * D)) +
        c / (3 * x) := add_le_add hsum le_rfl
    _ ≤ ((A * x ^ θ) * (1 / 2) + (2 * B * (1 + (2 / 3) / e)) * x ^ θ) +
        (|c| / 3) * x ^ θ := add_le_add (add_le_add le_rfl hfront) hc
    _ = _ := by dsimp [e, c]; ring

#print axioms averagedPrimeSquaredWindow_eq_sum
#print axioms averagedPrimeSquaredWindow_eq_prefix
#print axioms averagedPrimeSquaredWindow_le_of_local_prefix

end

end AlpogeSuperZeta
