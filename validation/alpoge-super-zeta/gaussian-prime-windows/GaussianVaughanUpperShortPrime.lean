import GaussianVaughanUpperIdentity
import GaussianVaughanKernelEndpoints
import GaussianVaughanPrimePowers

/-! The small prime part of the exact upper identity has a large
exponential saving because its theta argument is at most a log power. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Filter Finset
open scoped Classical

noncomputable section

theorem gaussian_exp_log_power_eventually_inverse {a b : ℝ} (ha : 0 < a) (hb : 1 < b) (k : ℕ) :
    ∀ᶠ X : ℝ in atTop, Real.exp (-(a * (Real.log X) ^ b)) ≤ (X ^ k)⁻¹ := by
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hCut := ((tendsto_rpow_atTop (sub_pos.mpr hb)).comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop ((k : ℝ) / a))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hLog, hCut] with X hX hLog hCut
  let ℓ := Real.log X
  have hℓ := zero_lt_one.trans_le hLog
  have h1 : (k : ℝ) ≤ a * ℓ ^ (b - 1) := by rw [mul_comm]; exact (div_le_iff₀ ha).mp hCut
  have hP : ℓ ^ b = ℓ ^ (b - 1) * ℓ := by
    calc
      _ = ℓ ^ ((b - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hℓ, Real.rpow_one]
  have hCost : (k : ℝ) * ℓ ≤ a * ℓ ^ b := by
    rw [hP, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 hℓ.le
  calc
    _ ≤ Real.exp (-((k : ℝ) * ℓ)) := Real.exp_le_exp.mpr (neg_le_neg hCost)
    _ = _ := by
      rw [Real.exp_neg, Real.exp_nat_mul, show Real.exp ℓ = X from Real.exp_log (zero_lt_one.trans hX)]

private theorem archivedPrimeCoeff_norm_le_fourX {p : ℕ} {X : ℝ} (hX : 0 ≤ X) (hp : (p : ℝ) ≤ 2 * X) :
    ‖archivedGaussianVaughanPrimeCoefficients p‖ ≤ 4 * X := by
  by_cases h : p.Prime
  · simp only [archivedGaussianVaughanPrimeCoefficients, coe_mk, if_pos h]
    refine (archivedGaussianMangoldt_norm_le p).trans ?_
    rw [vonMangoldt_apply_prime h]
    have hp₀ : (0 : ℝ) < p := Nat.cast_pos.mpr h.pos
    linarith [Real.log_le_sub_one_of_pos hp₀]
  · simp only [archivedGaussianVaughanPrimeCoefficients, coe_mk, if_neg h, norm_zero]
    positivity

theorem archivedGaussianVaughanShortPrimeReading_inv_bound (W : ℝ → ℝ)
    (hW : ∀ u ≥ 0, |W u| ≤ 1) (hSupport : ∀ u ≥ 2, W u = 0) :
    ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop,
      ‖archivedGaussianVaughanShortPrimeReading W (X / (Real.log X) ^ (5 / 2 : ℝ)) X⁻¹‖ ≤ C / X := by
  obtain ⟨D, hD, c, hc, hH⟩ := archivedGaussianVaughanKernel_small_exp
  refine ⟨12 * D, by positivity, ?_⟩
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hSmall := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 35 / 2)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop (128 / c))
  have hExp := gaussian_exp_log_power_eventually_inverse (a := c / 128) (b := 35 / 2)
    (by positivity) (by norm_num) 3
  filter_upwards [eventually_ge_atTop (1 : ℝ), hLog, hSmall, hExp]
    with X hX hLog hSmall hExp
  have hx := zero_lt_one.trans_le hX
  let ℓ := Real.log X
  have hℓ : 0 < ℓ := zero_lt_one.trans_le hLog
  let L := ℓ ^ (5 / 2 : ℝ)
  have hL : 0 < L := Real.rpow_pos_of_pos hℓ _
  let V := X / L
  have hV : 0 < V := div_pos hx hL
  have hVlarge : V ≤ X := div_le_self hx.le (Real.one_le_rpow hLog (by norm_num))
  let S := range (Nat.floor (2 * V) + 1)
  let f (p : ℕ) : ℂ := archivedGaussianVaughanWeightedPrimes W V p *
    (archivedGaussianVaughanKernel (p / X) : ℂ)
  have hOutside (p : ℕ) (hp : p ∉ S) : f p = 0 := by
    have hp' : ¬ p ≤ Nat.floor (2 * V) := by simpa only [S, mem_range, Nat.lt_succ_iff] using hp
    have hpr : 2 * V < (p : ℝ) := lt_of_not_ge fun h =>
      hp' ((Nat.le_floor_iff (by positivity : 0 ≤ 2 * V)).mpr h)
    have hW' := hSupport (p / V) ((le_div_iff₀ hV).mpr hpr.le)
    simp [f, archivedGaussianVaughanWeightedPrimes, hW']
  have hCard : (S.card : ℝ) ≤ 3 * X := by
    simp only [S, card_range, Nat.cast_add, Nat.cast_one]
    linarith [Nat.floor_le (by positivity : 0 ≤ 2 * V)]
  let bound := 4 * X * (D / X ^ (3 : ℕ))
  have hBound₀ : 0 ≤ bound := by dsimp [bound]; positivity
  have hTerm (p : ℕ) (hp : p ∈ S) : ‖f p‖ ≤ bound := by
    by_cases hp₀ : p = 0
    · simp [f, hp₀, hBound₀]
    have hp₁ : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp₀)
    let v := (p : ℝ) / X
    have hv : 0 < v := div_pos hp₁ hx
    have hpLim : (p : ℝ) ≤ 2 * V := by
      exact (Nat.cast_le.mpr (Nat.lt_succ_iff.mp (mem_range.mp hp))).trans
        (Nat.floor_le (by positivity))
    have hRatio : v ≤ 2 / L := by
      calc
        _ ≤ (2 * V) / X := div_le_div_of_nonneg_right hpLim hx.le
        _ = _ := by dsimp [V]; field_simp [hL.ne', hx.ne']
    have hLpow : L ^ (7 : ℕ) = ℓ ^ (35 / 2 : ℝ) := by
      dsimp only [L]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]
      norm_num
    have h7 : v ^ (7 : ℕ) ≤ 128 / ℓ ^ (35 / 2 : ℝ) := by
      exact (pow_le_pow_left₀ hv.le hRatio _).trans_eq (by rw [div_pow, hLpow]; norm_num)
    have hSmall' : (128 : ℝ) / ℓ ^ (35 / 2 : ℝ) ≤ c := by
      apply (div_le_iff₀ (Real.rpow_pos_of_pos hℓ _)).mpr
      rw [mul_comm]
      exact (div_le_iff₀ hc).mp hSmall
    have hCost : (c / 128) * ℓ ^ (35 / 2 : ℝ) ≤ c / v ^ (7 : ℕ) := by
      apply (le_div_iff₀ (pow_pos hv _)).mpr
      calc
        _ ≤ ((c / 128) * ℓ ^ (35 / 2 : ℝ)) * (128 / ℓ ^ (35 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left h7 (by positivity)
        _ = _ := by field_simp [ne_of_gt (Real.rpow_pos_of_pos hℓ (35 / 2 : ℝ))]
    have hKernel : |archivedGaussianVaughanKernel v| ≤ D / X ^ (3 : ℕ) := by
      refine (hH v hv (h7.trans hSmall')).trans ?_
      rw [div_eq_mul_inv D (X ^ (3 : ℕ))]
      apply mul_le_mul_of_nonneg_left _ hD.le
      exact (Real.exp_le_exp.mpr (neg_le_neg hCost)).trans hExp
    have hCoeff : ‖archivedGaussianVaughanPrimeCoefficients p‖ ≤ 4 * X :=
      archivedPrimeCoeff_norm_le_fourX hx.le (hpLim.trans (by linarith))
    have hWt := hW (p / V) (by positivity)
    change ‖(archivedGaussianVaughanPrimeCoefficients p * (W (p / V) : ℂ)) *
      (archivedGaussianVaughanKernel v : ℂ)‖ ≤ _
    simp only [norm_mul, norm_real, Real.norm_eq_abs]
    change ‖archivedGaussianVaughanPrimeCoefficients p‖ * |W (p / V)| *
      |archivedGaussianVaughanKernel v| ≤ 4 * X * (D / X ^ (3 : ℕ))
    calc
      _ ≤ (4 * X * 1) * (D / X ^ (3 : ℕ)) := by gcongr
      _ = _ := by rw [mul_one]
  change ‖∑' p, f p‖ ≤ _
  rw [tsum_eq_sum hOutside]
  calc
    _ ≤ ∑ p ∈ S, ‖f p‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, bound := sum_le_sum hTerm
    _ = (S.card : ℝ) * bound := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 3 * X * bound := mul_le_mul_of_nonneg_right hCard hBound₀
    _ = _ := by
      dsimp [bound]
      field_simp [hx.ne']
      ring

#print axioms gaussian_exp_log_power_eventually_inverse
#print axioms archivedGaussianVaughanShortPrimeReading_inv_bound

end
end AlpogeSuperZeta
