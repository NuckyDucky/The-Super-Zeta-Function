import GaussianSquaredRoundingResidual
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Compact support and monotonicity of the averaged squared rounding residual. -/

namespace AlpogeSuperZeta

open MeasureTheory Set

noncomputable section

/-- Averaging by \(2/y\) preserves the linear part, which cancels in the difference. -/
def averagedRoundingResidual (y : ℝ) : ℝ :=
  (2 / y) * (∫ t in 0..y, squaredRoundingResidual t) - squaredRoundingResidual y

theorem squaredRoundingResidual_intervalIntegrable {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable squaredRoundingResidual volume a b := by
  apply MonotoneOn.intervalIntegrable
  apply squaredRoundingResidual_monotoneOn.mono
  rw [uIcc_of_le hab]
  exact fun _ ht => mem_Ici.mpr (ha.trans ht.1)

private theorem residual_integral_eq {y : ℝ} (h₀ : 0 ≤ y) (h₁ : y ≤ 1) :
    (∫ t in 0..y, squaredRoundingResidual t) = y ^ 2 / 6 := by
  calc
    _ = ∫ t in 0..y, t / 3 := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le h₀]
      exact fun t ht => squaredRoundingResidual_eq_div_three ht.1 (ht.2.trans h₁)
    _ = _ := by rw [intervalIntegral.integral_div, integral_id, zero_pow (by decide)]; ring

theorem averagedRoundingResidual_eq_zero {y : ℝ} (h₀ : 0 ≤ y) (h₁ : y ≤ 1) :
    averagedRoundingResidual y = 0 := by
  rw [averagedRoundingResidual, residual_integral_eq h₀ h₁, squaredRoundingResidual_eq_div_three h₀ h₁]
  by_cases h : y = 0
  · simp [h]
  field_simp
  ring

private theorem residual_integral_le_endpoint {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, squaredRoundingResidual t) ≤ (b - a) * squaredRoundingResidual b := by
  have h := intervalIntegral.integral_mono_on hab
    (squaredRoundingResidual_intervalIntegrable ha hab) intervalIntegrable_const
    (fun t ht => squaredRoundingResidual_monotoneOn (ha.trans ht.1) (ha.trans hab) ht.2)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

private theorem residual_integral_ge_endpoint {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) * squaredRoundingResidual a ≤ (∫ t in a..b, squaredRoundingResidual t) := by
  have h := intervalIntegral.integral_mono_on hab intervalIntegrable_const
    (squaredRoundingResidual_intervalIntegrable ha hab)
    (fun t ht => squaredRoundingResidual_monotoneOn ha (ha.trans ht.1) ht.1)
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

private theorem averagedRoundingResidual_sub_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    averagedRoundingResidual b - averagedRoundingResidual a =
      (2 / b) * ((∫ t in a..b, squaredRoundingResidual t) -
        (b - a) / a * (∫ t in 0..a, squaredRoundingResidual t)) -
        (squaredRoundingResidual b - squaredRoundingResidual a) := by
  have hb := ha.trans_le hab
  unfold averagedRoundingResidual
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (squaredRoundingResidual_intervalIntegrable le_rfl ha.le)
    (squaredRoundingResidual_intervalIntegrable ha.le hab)]
  field_simp
  ring

private theorem residual_gap_integral_eq {a b v : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, squaredRoundingResidual v - squaredRoundingResidual t) =
      (b - a) * squaredRoundingResidual v - (∫ t in a..b, squaredRoundingResidual t) := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (squaredRoundingResidual_intervalIntegrable ha hab), intervalIntegral.integral_const, smul_eq_mul]

private theorem residual_gap_le_log {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a * squaredRoundingResidual b - (∫ t in 0..a, squaredRoundingResidual t) ≤
      1 / 2 + Real.log a / 3 := by
  let g (t : ℝ) := squaredRoundingResidual b - squaredRoundingResidual t
  have hg {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) : IntervalIntegrable g volume u v :=
    intervalIntegrable_const.sub (squaredRoundingResidual_intervalIntegrable hu huv)
  have hfront : (∫ t in 0..1, g t) ≤ 1 / 2 := by
    have h := intervalIntegral.integral_mono_on zero_le_one (hg le_rfl zero_le_one)
      intervalIntegrable_const fun t ht => sub_le_iff_le_add.mpr
        ((squaredRoundingResidual_le_half (zero_le_one.trans (ha.trans hab))).trans
          (le_add_of_nonneg_right (squaredRoundingResidual_nonneg ht.1)))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h
  have hInv : IntervalIntegrable (fun t : ℝ => t⁻¹ / 3) volume 1 a := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ha]
    exact (continuousOn_id.inv₀ fun _ ht => (one_pos.trans_le ht.1).ne').div_const 3
  have hback : (∫ t in 1..a, g t) ≤ Real.log a / 3 := by
    calc
      _ ≤ ∫ t in 1..a, t⁻¹ / 3 := by
        apply intervalIntegral.integral_mono_on ha (hg zero_le_one ha) hInv
        intro t ht
        exact (squaredRoundingResidual_sub_le_reciprocal (one_pos.trans_le ht.1)
          (ht.2.trans hab)).trans (div_le_div_of_nonneg_right
            (sub_le_self _ (inv_nonneg.mpr (zero_le_one.trans (ha.trans hab)))) (by norm_num))
      _ = _ := by
        rw [intervalIntegral.integral_div, integral_inv_of_pos one_pos (one_pos.trans_le ha), div_one]
  have h := add_le_add hfront hback
  rw [intervalIntegral.integral_add_adjacent_intervals (hg le_rfl zero_le_one) (hg zero_le_one ha)]
    at h
  dsimp only [g] at h
  rw [residual_gap_integral_eq le_rfl (zero_le_one.trans ha), sub_zero] at h
  exact h

private theorem residual_gap_ge_sixth {a : ℝ} (ha : 1 ≤ a) :
    1 / 6 ≤ a * squaredRoundingResidual a - (∫ t in 0..a, squaredRoundingResidual t) := by
  have h₁ : 1 / 3 ≤ squaredRoundingResidual a := by
    rw [← squaredRoundingResidual_eq_div_three zero_le_one (le_refl (1 : ℝ))]
    exact squaredRoundingResidual_monotoneOn
      (mem_Ici.mpr zero_le_one) (mem_Ici.mpr (zero_le_one.trans ha)) ha
  have h := residual_integral_le_endpoint zero_le_one ha
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (squaredRoundingResidual_intervalIntegrable le_rfl zero_le_one)
    (squaredRoundingResidual_intervalIntegrable zero_le_one ha),
    residual_integral_eq zero_le_one le_rfl]
  linarith

private theorem averagedRoundingResidual_increment {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ averagedRoundingResidual b - averagedRoundingResidual a ∧
      averagedRoundingResidual b - averagedRoundingResidual a ≤
        (a⁻¹ - b⁻¹) * (1 + 2 / 3 * Real.log a) := by
  have ha₀ := one_pos.trans_le ha
  have hb₀ := ha₀.trans_le hab
  have hh : 0 ≤ a⁻¹ - b⁻¹ := sub_nonneg.mpr (inv_anti₀ ha₀ hab)
  let I := ∫ t in 0..a, squaredRoundingResidual t
  let J := ∫ t in a..b, squaredRoundingResidual t
  have hformula (v : ℝ) :
      (2 / b) * ((b - a) * v - (b - a) / a * I) =
        2 * (a⁻¹ - b⁻¹) * (a * v - I) := by
    field_simp
  have hf₀ : (a⁻¹ - b⁻¹) / 3 ≤ (2 / b) * (J - (b - a) / a * I) := by
    calc
      _ = 2 * (a⁻¹ - b⁻¹) * (1 / 6) := by ring
      _ ≤ 2 * (a⁻¹ - b⁻¹) * (a * squaredRoundingResidual a - I) :=
        mul_le_mul_of_nonneg_left (residual_gap_ge_sixth ha) (by positivity)
      _ = _ := (hformula (squaredRoundingResidual a)).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_right
        (residual_integral_ge_endpoint ha₀.le hab) _) (by positivity)
  have hf₁ : (2 / b) * (J - (b - a) / a * I) ≤
      (a⁻¹ - b⁻¹) * (1 + 2 / 3 * Real.log a) := by
    calc
      _ ≤ (2 / b) * ((b - a) * squaredRoundingResidual b - (b - a) / a * I) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right (residual_integral_le_endpoint ha₀.le hab) _)
          (by positivity)
      _ = _ := hformula (squaredRoundingResidual b)
      _ ≤ 2 * (a⁻¹ - b⁻¹) * (1 / 2 + Real.log a / 3) :=
        mul_le_mul_of_nonneg_left (residual_gap_le_log ha hab) (by positivity)
      _ = _ := by ring
  have hR₀ := squaredRoundingResidual_monotoneOn ha₀.le hb₀.le hab
  have hR₁ := squaredRoundingResidual_sub_le_reciprocal ha₀ hab
  rw [averagedRoundingResidual_sub_eq ha₀ hab]
  exact ⟨sub_nonneg.mpr (hR₁.trans hf₀), sub_le_iff_le_add.mpr
    (hf₁.trans (le_add_of_nonneg_right (sub_nonneg.mpr hR₀)))⟩

theorem averagedRoundingResidual_monotoneOn : MonotoneOn averagedRoundingResidual (Ici 0) := by
  intro a ha b hb hab
  by_cases ha₁ : 1 ≤ a
  · exact sub_nonneg.mp (averagedRoundingResidual_increment ha₁ hab).1
  rw [averagedRoundingResidual_eq_zero ha (le_of_not_ge ha₁)]
  by_cases hb₁ : 1 ≤ b
  · have h := sub_nonneg.mp (averagedRoundingResidual_increment le_rfl hb₁).1
    rwa [averagedRoundingResidual_eq_zero zero_le_one le_rfl] at h
  rw [averagedRoundingResidual_eq_zero hb (le_of_not_ge hb₁)]

theorem averagedRoundingResidual_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ averagedRoundingResidual y := by
  simpa only [averagedRoundingResidual_eq_zero le_rfl zero_le_one] using
    averagedRoundingResidual_monotoneOn (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hy) hy

theorem averagedRoundingResidual_le_half {y : ℝ} (hy : 0 ≤ y) : averagedRoundingResidual y ≤ 1 / 2 := by
  rcases hy.lt_or_eq with h | rfl
  · have hI := residual_integral_le_endpoint le_rfl hy
    have hA : (2 / y) * (∫ t in 0..y, squaredRoundingResidual t) ≤ 2 * squaredRoundingResidual y := by
      calc
        _ ≤ (2 / y) * ((y - 0) * squaredRoundingResidual y) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
        _ = _ := by field_simp; ring
    have hR := squaredRoundingResidual_le_half hy
    unfold averagedRoundingResidual
    linarith
  rw [averagedRoundingResidual_eq_zero le_rfl zero_le_one]
  norm_num

/-- The step between two prime addresses is controlled by their reciprocal difference. -/
theorem averagedRoundingResidual_sub_le_log {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hx : 1 ≤ x) (hbx : b ≤ x) :
    averagedRoundingResidual b - averagedRoundingResidual a ≤
      (a⁻¹ - b⁻¹) * (1 + 2 / 3 * Real.log x) := by
  have hb := ha.trans_le hab
  have hh : 0 ≤ a⁻¹ - b⁻¹ := sub_nonneg.mpr (inv_anti₀ ha hab)
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  by_cases ha₁ : 1 ≤ a
  · exact (averagedRoundingResidual_increment ha₁ hab).2.trans
      (mul_le_mul_of_nonneg_left (by linarith [Real.log_le_log ha (hab.trans hbx)]) hh)
  rw [averagedRoundingResidual_eq_zero ha.le (le_of_not_ge ha₁)]
  by_cases hb₁ : 1 ≤ b
  · have h := (averagedRoundingResidual_increment le_rfl hb₁).2
    rw [averagedRoundingResidual_eq_zero zero_le_one le_rfl, sub_zero, inv_one, Real.log_one] at h
    calc
      _ ≤ 1 - b⁻¹ := by linarith
      _ ≤ a⁻¹ - b⁻¹ := sub_le_sub_right (by simpa using inv_anti₀ ha (le_of_not_ge ha₁)) _
      _ ≤ _ := le_mul_of_one_le_right hh (by linarith)
  rw [averagedRoundingResidual_eq_zero hb.le (le_of_not_ge hb₁), zero_sub, neg_zero]
  positivity

#print axioms averagedRoundingResidual_eq_zero
#print axioms averagedRoundingResidual_monotoneOn
#print axioms averagedRoundingResidual_le_half
#print axioms averagedRoundingResidual_sub_le_log

end

end AlpogeSuperZeta
