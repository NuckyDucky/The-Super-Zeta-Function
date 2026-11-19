import FlankReferences

/-! Successive clockwise arcs reuse any finite endpoint as a starting zero.
    Here b=1/4 is the 45-degree endpoint, and b=1/6 is the 60-degree start. -/
namespace DottieOriented.ReferenceReset

open Complex DottieOriented.LiuConnection DottieOriented.FlankReferences

noncomputable section

def resetFactor (w : ℂ) : ℂ := (2 : ℂ)^(-w) * ((3 : ℂ)^w - 1)

theorem resetFactor_entire (w : ℂ) : AnalyticAt ℂ resetFactor w := by
  unfold resetFactor
  simp only [cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0),
    cpow_def_of_ne_zero (by norm_num : (3:ℂ) ≠ 0)]
  fun_prop

theorem reset_identity {w : ℂ} (hw : w ≠ 1) :
    reference (1/6 : ℝ) w = resetFactor w * reference (1/4 : ℝ) w := by
  simp only [reference, resetFactor, show (1-1/6 : ℝ) = 5/6 by norm_num,
    show (1-1/4 : ℝ) = 3/4 by norm_num, sixth_pair hw, quarter_pair hw]
  rw [cpow_neg (2:ℂ) w]
  have h₂ : (2 : ℂ)^w ≠ 0 := cpow_ne_zero_iff.mpr (.inl (by norm_num))
  field_simp [h₂]
  ring

theorem endpoint_reenters {w : ℂ} (hw : w ≠ 1) (hend : reference (1/4 : ℝ) w = 0) :
    reference (1/6 : ℝ) w = 0 := by
  rw [reset_identity hw, hend, mul_zero]

theorem starting_zero_iff {w : ℂ} (hw : w ≠ 1) :
    reference (1/6 : ℝ) w = 0 ↔ (3 : ℂ)^w = 1 ∨ reference (1/4 : ℝ) w = 0 := by
  have h₂ : (2 : ℂ)^(-w) ≠ 0 := cpow_ne_zero_iff.mpr (.inl (by norm_num))
  rw [reset_identity hw, resetFactor]
  simp [mul_eq_zero, h₂, sub_eq_zero]

end
end DottieOriented.ReferenceReset
