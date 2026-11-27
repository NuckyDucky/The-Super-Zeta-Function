import DedekindMixedThetaSampleModel
import Mathlib.Analysis.Complex.Schwarz

namespace FieldTarget

open Complex Metric Set Asymptotics
open scoped Topology

noncomputable section

/-- A center value and a logarithmic slope give an entire reference. -/
def contourExponentialModel (a b c z : ℂ) : ℂ := a * Complex.exp (b * (z - c))

theorem contourExponentialModel_regular {a : ℂ} (ha : a ≠ 0) (b c : ℂ) :
    Differentiable ℂ (contourExponentialModel a b c) ∧
      ∀ z : ℂ, contourExponentialModel a b c z ≠ 0 := by
  constructor
  · unfold contourExponentialModel
    fun_prop
  · intro z
    exact mul_ne_zero ha (Complex.exp_ne_zero _)

/-- The constant and linear errors can be measured from approximate model
parameters. Both vanish when the reference matches the exact center data. -/
theorem contourExponentialModel_center {F : ℂ → ℂ} {a b c d : ℂ}
    (ha : a ≠ 0) (hF : HasDerivAt F d c) :
    let G := fun z => F z / contourExponentialModel a b c z - 1
    G c = F c / a - 1 ∧ HasDerivAt G ((d - b * F c) / a) c := by
  have hlin : HasDerivAt (fun z : ℂ => b * (z - c)) b c := by
    simpa using ((hasDerivAt_id c).sub_const c).const_mul b
  have hexp : HasDerivAt (fun z : ℂ => Complex.exp (b * (z - c))) b c := by
    simpa using! (Complex.hasDerivAt_exp (b * (c - c))).comp c hlin
  have hP : HasDerivAt (contourExponentialModel a b c) (a * b) c := by
    simpa [contourExponentialModel] using! (hasDerivAt_const c a).mul hexp
  refine ⟨by simp [contourExponentialModel], ?_⟩
  have h := (hF.div hP (by simpa [contourExponentialModel] using ha)).sub_const (1 : ℂ)
  convert h using 1
  simp only [contourExponentialModel, sub_self, mul_zero, Complex.exp_zero, mul_one]
  field_simp [ha]

/-- After removing the constant and linear errors, the Schwarz bound gives
quadratic decay from the enclosing circle to the sample disk. -/
theorem contour_error_le_from_center_data {G : ℂ → ℂ} {c z d : ℂ} {R M e₀ e₁ : ℝ}
    (hz : z ∈ ball c R) (hG : DifferentiableOn ℂ G (ball c R))
    (hM : ∀ u ∈ ball c R, ‖G u‖ ≤ M)
    (hD : HasDerivAt G d c) (he₀ : ‖G c‖ ≤ e₀) (he₁ : ‖d‖ ≤ e₁) :
    ‖G z‖ ≤ e₀ + ‖z - c‖ * e₁ + (M + e₀ + R * e₁) * (‖z - c‖ / R) ^ 2 := by
  let H := fun u : ℂ => G u - G c - (u - c) * d
  have hHc : H c = 0 := by simp [H]
  have hH : DifferentiableOn ℂ H (ball c R) := by
    exact (hG.sub (differentiableOn_const (G c))).sub
      ((differentiableOn_id.sub (differentiableOn_const c)).mul (differentiableOn_const d))
  have han : (fun u => H u - H c) =o[𝓝 c] (fun u => ‖u - c‖ ^ (1 : ℕ)) := by
    simpa only [hHc, sub_zero, H, pow_one, smul_eq_mul] using hD.isLittleO.norm_right
  have hE₁ : 0 ≤ e₁ := (norm_nonneg _).trans he₁
  have hHnorm (u : ℂ) (hu : u ∈ ball c R) :
      ‖H u‖ ≤ ‖G u‖ + ‖G c‖ + ‖u - c‖ * ‖d‖ := by
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_mul _ _).le)
  have hmap : MapsTo H (ball c R) (closedBall (H c) (M + e₀ + R * e₁)) := by
    intro u hu
    rw [mem_closedBall, dist_eq_norm, hHc, sub_zero]
    have hur : ‖u - c‖ ≤ R := by simpa only [dist_eq_norm] using (mem_ball.mp hu).le
    exact (hHnorm u hu).trans (add_le_add (add_le_add (hM u hu) he₀)
      ((mul_le_mul_of_nonneg_left he₁ (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hur hE₁)))
  have hsmall := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hH hmap han hz
  rw [dist_eq_norm, hHc, sub_zero, dist_eq_norm] at hsmall
  calc
    ‖G z‖ = ‖G c + (z - c) * d + H z‖ := by
      congr 1
      simp only [H]
      abel
    _ ≤ ‖G c + (z - c) * d‖ + ‖H z‖ := norm_add_le _ _
    _ ≤ (‖G c‖ + ‖z - c‖ * ‖d‖) + ‖H z‖ :=
      add_le_add ((norm_add_le _ _).trans_eq (by rw [norm_mul])) le_rfl
    _ ≤ _ := add_le_add
      (add_le_add he₀ (mul_le_mul_of_nonneg_left he₁ (norm_nonneg _))) hsmall

#check @contour_error_le_from_center_data
#print axioms contourExponentialModel_regular
#print axioms contourExponentialModel_center
#print axioms contour_error_le_from_center_data

end

end FieldTarget
