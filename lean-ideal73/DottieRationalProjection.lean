import DottieCompletedReferencePhase
import DottieHeightPerturbation

/-! Reduce positivity of the original Dottie reference unit to one real
signed sum at an exact rational phase and height. -/

open Complex

namespace QuarticModel

open private completed_projection_scale_pos projection_scale_pos from DottieCompletedReferencePhase

private theorem phase_projection_error (D D₀ : ℂ) (φ ψ : ℝ) :
    |(Complex.exp ((φ : ℂ)*I)*D).re - (Complex.exp ((ψ : ℂ)*I)*D₀).re| ≤
      ‖D-D₀‖ + |φ-ψ| * ‖D₀‖ := by
  let a := Complex.exp ((φ : ℂ)*I)
  let b := Complex.exp ((ψ : ℂ)*I)
  have h : a*D-b*D₀ = a*(D-D₀)+(a-b)*D₀ := by ring
  rw [← Complex.sub_re]
  refine (Complex.abs_re_le_norm _).trans ?_
  change ‖a*D-b*D₀‖ ≤ _
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, show ‖a‖ = 1 from Complex.norm_exp_ofReal_mul_I _, one_mul]
  exact add_le_add_right (mul_le_mul_of_nonneg_right (dottie_unit_phase_distance φ ψ) (norm_nonneg D₀)) _

/-- The real signed sum to evaluate at the exact rational inputs. -/
noncomputable def dottieRationalReferenceProjection : ℝ :=
  (Complex.exp ((3.9229252 : ℂ)*I) *
    signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieRationalReferencePoint).re

private theorem positive_of_rational_projection {S C : ℝ} {D D₀ : ℂ}
    (hphase : ∃ φ : ℝ, 3.92292369 < φ ∧ φ < 3.92292670 ∧
      S = C * |(Complex.exp ((φ : ℂ)*I)*D).re|)
    (hscale : 0 < C) (hD : ‖D-D₀‖ < 1/200) (hD₀ : ‖D₀‖ ≤ 33276)
    (hpositive : (1:ℝ)/10 < (Complex.exp ((3.9229252 : ℂ)*I)*D₀).re) : 0 < S := by
  obtain ⟨φ, hl, hu, hS⟩ := hphase
  have hφ : |φ-3.9229252| ≤ 0.0000016 := by
    apply abs_le.mpr
    constructor <;> linarith only [hl, hu]
  have hp := mul_le_mul hφ hD₀ (norm_nonneg _) (by norm_num)
  have he := phase_projection_error D D₀ φ 3.9229252
  rw [show ((↑(3.9229252 : ℝ)) : ℂ) = 3.9229252 by norm_num] at he
  have hmove : |(Complex.exp ((φ : ℂ)*I)*D).re -
      (Complex.exp ((3.9229252 : ℂ)*I)*D₀).re| < 3/50 := by
    linarith only [he, hp, hD]
  have h := (abs_lt.mp hmove).1
  exact projection_scale_pos hS hscale (by linarith only [h, hpositive])

/-- One rationally addressed signed sum suffices for positivity in the
original completion scale. The theorem uses the certified error `< 3/50`. -/
theorem dottieCircleReference_pos_of_rational_projection
    (h : (1:ℝ)/10 < dottieRationalReferenceProjection) : 0 < dottieCircleReference :=
  positive_of_rational_projection dottieCircleReference_eq_completed_phase
    completed_projection_scale_pos dottie_reference_rational_height_error
    dottie_reference_rational_norm_bound h

#print axioms dottieCircleReference_pos_of_rational_projection

end QuarticModel
