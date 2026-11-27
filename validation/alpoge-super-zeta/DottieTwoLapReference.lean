import SuperZeta.Oriented.OrderedStages
import FlankReferences

namespace DottieOriented

open Complex SuperZeta.Reciprocal LiuConnection FlankReferences

theorem two_lap_arg {f : ℂ → ℂ} {p : ℂ}
    (hf : DifferentiableAt ℂ f p) (hfix : f p = p)
    (hangle : arg (deriv f p) = Real.pi / 6 ∨ arg (deriv f p) = -(Real.pi / 6)) :
    arg (deriv (f ∘ f) p) = 2 * arg (deriv f p) := by
  have hne : deriv f p ≠ 0 := by
    intro h
    rw [h, arg_zero] at hangle
    rcases hangle with hangle | hangle <;> linarith [Real.pi_pos]
  have houter : HasDerivAt f (deriv f p) (f p) := by
    rw [hfix]
    exact hf.hasDerivAt
  rw [(houter.comp p hf.hasDerivAt).deriv, two_mul]
  apply (arg_mul_eq_add_arg_iff hne hne).2
  rcases hangle with ha | ha <;> rw [ha] <;>
    exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem sixth_reference_eq_twice_thirds {w : ℂ} (hw : w ≠ 1) :
    reference (1 / 6 : ℝ) w = ((2 : ℂ) ^ w - 1) * reference (1 / 3 : ℝ) w := by
  rw [reference_at_thirds (Or.inl rfl) hw, reference]
  rw [show (1 - 1 / 6 : ℝ) = 5 / 6 by norm_num, sixth_pair hw]
  ring

/-- Repeating a marked lap changes the symmetric shift from thirds to sixths. -/
theorem two_lap_reference_eq {f : ℂ → ℂ} {p w : ℂ}
    (hf : DifferentiableAt ℂ f p) (hfix : f p = p)
    (hangle : arg (deriv f p) = Real.pi / 6 ∨ arg (deriv f p) = -(Real.pi / 6))
    (hw : w ≠ 1) :
    reference (1 / 2 - arg (deriv (f ∘ f) p) / Real.pi) w =
      ((2 : ℂ) ^ w - 1) * reference (1 / 3 : ℝ) w := by
  rw [two_lap_arg hf hfix hangle]
  rcases hangle with ha | ha
  · rw [ha, show (1 / 2 - (2 * (Real.pi / 6)) / Real.pi : ℝ) = 1 / 6 by
      field_simp [Real.pi_ne_zero]
      ring]
    exact sixth_reference_eq_twice_thirds hw
  · rw [ha, show (1 / 2 - (2 * -(Real.pi / 6)) / Real.pi : ℝ) = 5 / 6 by
      field_simp [Real.pi_ne_zero]
      ring]
    calc
      reference (5 / 6 : ℝ) w = reference (1 / 6 : ℝ) w := by
        simp only [reference, show (1 - 5 / 6 : ℝ) = 1 / 6 by norm_num,
          show (1 - 1 / 6 : ℝ) = 5 / 6 by norm_num]
        rw [add_comm]
      _ = _ := sixth_reference_eq_twice_thirds hw

theorem cap_two_lap_reference_eq (y : ℝ) (p : ℂ) {w : ℂ}
    (hfix : capReturn y p = p)
    (hangle : nativeAngle y p = Real.pi / 6 ∨ nativeAngle y p = -(Real.pi / 6))
    (hw : w ≠ 1) :
    reference (1 / 2 - arg (deriv (capReturn y ∘ capReturn y) p) / Real.pi) w =
      ((2 : ℂ) ^ w - 1) * reference (1 / 3 : ℝ) w := by
  have hdiff : Differentiable ℂ (scalarReturn (I * (y : ℂ))) := by
    unfold scalarReturn
    fun_prop
  apply two_lap_reference_eq ((hdiff.iterate 320) p) hfix hangle hw

theorem two_lap_sixth_reference_norm_le {w : ℂ} {M : ℝ}
    (hw : w ≠ 1) (hstrip : w.re ≤ 1) (hM : ‖reference (1 / 3 : ℝ) w‖ ≤ M) :
    ‖reference (1 / 6 : ℝ) w‖ ≤ 3 * M := by
  have htwo : ‖(2 : ℂ) ^ w‖ ≤ 2 := by
    calc
      _ = (2 : ℝ) ^ w.re := norm_natCast_cpow_of_pos (n := 2) (by decide) w
      _ ≤ (2 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hstrip
      _ = 2 := Real.rpow_one _
  have hphase : ‖(2 : ℂ) ^ w - 1‖ ≤ 3 := by
    calc
      _ ≤ ‖(2 : ℂ) ^ w‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 := by rw [norm_one]; linarith
  rw [sixth_reference_eq_twice_thirds hw, norm_mul]
  exact (mul_le_mul_of_nonneg_right hphase (norm_nonneg _)).trans
    (mul_le_mul_of_nonneg_left hM (by norm_num))

#check @cap_two_lap_reference_eq
#print axioms two_lap_arg
#print axioms sixth_reference_eq_twice_thirds
#print axioms two_lap_reference_eq
#print axioms cap_two_lap_reference_eq
#print axioms two_lap_sixth_reference_norm_le

end DottieOriented
