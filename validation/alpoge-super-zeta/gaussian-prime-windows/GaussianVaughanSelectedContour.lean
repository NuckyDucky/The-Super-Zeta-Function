import GaussianVaughanContourMoments
import GaussianVaughanConvolvedLeftLine
import MellinContourShift

/-! Integrate the reflected transform and choose the contour index for
each small argument. -/

namespace AlpogeSuperZeta

open Complex MeasureTheory

noncomputable section

theorem archivedGaussianVaughanConvolvedMellin_left_integrated :
    ∃ C ≥ 1, ∀ N ≥ 1,
      VerticalIntegrable archivedGaussianVaughanConvolvedMellin (-((7 * N : ℕ) : ℝ)) ∧
      (∫ t : ℝ, ‖archivedGaussianVaughanConvolvedMellin (gaussianVaughanLeftPoint N t)‖) ≤
        C ^ (N + 1) * ((N : ℝ) + 1) ^ (15 * N) := by
  obtain ⟨B, hB, h⟩ := archivedGaussianVaughanConvolvedMellin_left_pointwise
  have hc (N : ℕ) (_ : 1 ≤ N) :
      Continuous (fun t => archivedGaussianVaughanConvolvedMellin (gaussianVaughanLeftPoint N t)) :=
    archivedGaussianVaughanConvolvedMellin_entire.continuous.comp (by
      unfold gaussianVaughanLeftPoint
      fun_prop)
  exact gaussian_integrate_left_contours hc hB h

theorem archivedGaussianVaughanConvolvedMellin_left_inverse_bound :
    ∃ C ≥ 1, ∀ N ≥ 1, ∀ v > 0,
      ‖mellinInv (-((7 * N : ℕ) : ℝ)) archivedGaussianVaughanConvolvedMellin v‖ ≤
        C ^ (N + 1) * v ^ (7 * N) * ((N : ℝ) + 1) ^ (15 * N) := by
  obtain ⟨C, hC, h⟩ := archivedGaussianVaughanConvolvedMellin_left_integrated
  refine ⟨C, hC, fun N hN v hv => ?_⟩
  obtain ⟨hInt, hB⟩ := h N hN
  let J := ∫ t : ℝ, ‖archivedGaussianVaughanConvolvedMellin (gaussianVaughanLeftPoint N t)‖
  have hJ : 0 ≤ J := integral_nonneg fun _ => norm_nonneg _
  have hπ : (1 : ℝ) / (2 * Real.pi) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_three]
  have hu := norm_mellinInv_le hv hInt
  dsimp only [gaussianVaughanLeftPoint] at hJ hB
  rw [neg_neg, Real.rpow_natCast] at hu
  refine hu.trans ?_
  change ((1 / (2 * Real.pi)) * J) * v ^ (7 * N) ≤ _
  calc
    _ ≤ J * v ^ (7 * N) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hJ hπ) (by positivity)
    _ ≤ (C ^ (N + 1) * ((N : ℝ) + 1) ^ (15 * N)) * v ^ (7 * N) :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    _ = _ := by ring

private theorem gaussian_choose_left_contour {C : ℝ} (hC : 1 ≤ C) :
    ∃ c > 0, ∃ v₀ > 0, ∀ v > 0, v ≤ v₀ →
      ∃ N : ℕ, 1 ≤ N ∧ C ^ (N + 1) * v ^ (7 * N) * ((N : ℝ) + 1) ^ (15 * N) ≤
        C * Real.exp (-c * v ^ (-(7 / 15 : ℝ))) := by
  have hC₀ : 0 < C := zero_lt_one.trans_le hC
  let A := (2 * C) ^ (-(1 / 15 : ℝ))
  have hA : 0 < A := Real.rpow_pos_of_pos (by positivity) _
  have hA15 : A ^ (15 : ℕ) = (2 * C)⁻¹ := by
    dsimp only [A]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ) * C)]
    norm_num [Real.rpow_neg_one]
  let c := Real.log 2 / 2 * A
  let v₀ := (A / 4) ^ (15 / 7 : ℝ)
  have hc : 0 < c := mul_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num)) hA
  have hv₀ : 0 < v₀ := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨c, hc, v₀, hv₀, fun v hv hvle => ?_⟩
  let R := A * v ^ (-(7 / 15 : ℝ))
  have hR : 4 ≤ R := by
    dsimp only [R]
    rw [Real.rpow_neg hv.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos hv _)]
    have hvEq : v₀ ^ (7 / 15 : ℝ) = A / 4 := by
      dsimp only [v₀]
      rw [← Real.rpow_mul (by positivity : 0 ≤ A / 4)]
      norm_num
    calc
      _ ≤ 4 * v₀ ^ (7 / 15 : ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hv.le hvle (by norm_num)) (by norm_num)
      _ = _ := by rw [hvEq]; ring
  have hR₀ : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 4).trans hR
  let n := ⌊R⌋₊
  have hn : 4 ≤ n := (Nat.le_floor_iff hR₀).mpr (by exact_mod_cast hR)
  let N := n - 1
  have hN₁ : 1 ≤ N := by dsimp only [N]; omega
  have hnEq : N + 1 = n := by dsimp only [N]; omega
  have hnRe : (N : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hnEq
  have hNle : (N : ℝ) + 1 ≤ R := by rw [hnRe]; exact Nat.floor_le hR₀
  have hNge : R / 2 ≤ (N : ℝ) := by
    have ht : R < (n : ℝ) + 1 := Nat.lt_floor_add_one R
    linarith
  have hv15 : (v ^ (-(7 / 15 : ℝ))) ^ (15 : ℕ) = (v ^ (7 : ℕ))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hv.le,
      show (-(7 / 15 : ℝ)) * ↑(15 : ℕ) = -((7 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hv.le, Real.rpow_natCast]
  have hNorm : C * v ^ (7 : ℕ) * R ^ (15 : ℕ) = 1 / 2 := by
    dsimp only [R]
    rw [mul_pow, hA15, hv15]
    field_simp
  have hPow : C * v ^ (7 : ℕ) * ((N : ℝ) + 1) ^ (15 : ℕ) ≤ 1 / 2 := by
    rw [← hNorm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hNle _) (by positivity)
  have hHalf : (1 / 2 : ℝ) ^ N = Real.exp (-(Real.log 2 * N)) := by
    calc
      _ = Real.exp (-(Real.log 2)) ^ N := by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  refine ⟨N, hN₁, ?_⟩
  calc
    _ = C * (C * v ^ (7 : ℕ) * ((N : ℝ) + 1) ^ (15 : ℕ)) ^ N := by
      rw [pow_succ C, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
      ring
    _ ≤ C * (1 / 2 : ℝ) ^ N := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) hPow _) hC₀.le
    _ ≤ _ := by
      rw [hHalf]
      apply mul_le_mul_of_nonneg_left _ hC₀.le
      apply Real.exp_le_exp.mpr
      have he := mul_le_mul_of_nonneg_left hNge (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
      dsimp only [R] at he
      dsimp only [c]
      linarith

/-- For every sufficiently small positive argument, the selected negative
line gives the stretched exponential bound for the actual inverse integral. -/
theorem archivedGaussianVaughanConvolvedMellin_selected_inverse_bound :
    ∃ C > 0, ∃ c > 0, ∃ v₀ > 0, ∀ v > 0, v ≤ v₀ → ∃ N : ℕ, 1 ≤ N ∧
      ‖mellinInv (-((7 * N : ℕ) : ℝ)) archivedGaussianVaughanConvolvedMellin v‖ ≤
        C * Real.exp (-c * v ^ (-(7 / 15 : ℝ))) := by
  obtain ⟨C, hC, hInv⟩ := archivedGaussianVaughanConvolvedMellin_left_inverse_bound
  obtain ⟨c, hc, v₀, hv₀, hChoose⟩ := gaussian_choose_left_contour hC
  refine ⟨C, zero_lt_one.trans_le hC, c, hc, v₀, hv₀, fun v hv hvle => ?_⟩
  obtain ⟨N, hN, h⟩ := hChoose v hv hvle
  exact ⟨N, hN, (hInv N hN v hv).trans h⟩

#check archivedGaussianVaughanConvolvedMellin_selected_inverse_bound
#print axioms archivedGaussianVaughanConvolvedMellin_left_integrated
#print axioms archivedGaussianVaughanConvolvedMellin_left_inverse_bound
#print axioms archivedGaussianVaughanConvolvedMellin_selected_inverse_bound

end
end AlpogeSuperZeta
