import DottieSharpCircleMoments
import DottieGammaRatio
import DottieCompletedReferencePhase
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Express the original sharp-circle margin in relative completion units.
The reference amplitude cancels before any directed enclosure is applied. -/

namespace QuarticModel

open Complex Finset SuperZeta.StirlingCorrection
open scoped ComplexConjugate
open private sum_dottieSharpSide from DottieSharpCircleMoments
set_option autoImplicit false

private theorem dottie_sharp_reference_factor_ne_zero :
    dottieSharpFactor dottieReferencePoint ≠ 0 := by
  have hb : (archivedThetaScale : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have hg : Gamma dottieReferencePoint ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by norm_num [dottieReferencePoint,Complex.mul_re])
  exact div_ne_zero (mul_ne_zero (cpow_ne_zero_iff.mpr (Or.inl hb)) hg)
    (ofReal_ne_zero.mpr archivedDottieCompletionScale_pos.ne')

noncomputable def dottieSharpReferenceAmplitude : ℝ :=
  ‖dottieSharpFactor dottieReferencePoint‖

noncomputable def dottieSharpReferenceUnit : ℂ :=
  dottieSharpFactor dottieReferencePoint / (dottieSharpReferenceAmplitude : ℂ)

noncomputable def dottieSharpRelativeFactor (w : ℂ) : ℂ :=
  dottieSharpFactor w / dottieSharpFactor dottieReferencePoint

theorem dottie_sharp_reference_amplitude_pos : 0 < dottieSharpReferenceAmplitude :=
  norm_pos_iff.mpr dottie_sharp_reference_factor_ne_zero

theorem dottie_sharp_reference_unit_phase_interval :
    ∃ phase : ℝ, 3.92292369 < phase ∧ phase < 3.92292670 ∧
      dottieSharpReferenceUnit = Complex.exp ((phase : ℂ)*I) := by
  obtain ⟨phase,hlo,hhi,hphase,_⟩ := dottieCircleReference_eq_completed_phase_and_unit
  refine ⟨phase,hlo,hhi,?_⟩
  let A := archivedDottieCompletionScale
  let C := (archivedThetaScale : ℂ)^dottieReferencePoint*Gamma dottieReferencePoint
  have hA : 0 < A := archivedDottieCompletionScale_pos
  change (C/(A : ℂ))/((‖C/(A : ℂ)‖ : ℝ) : ℂ) = _
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA,Complex.ofReal_div]
  calc
    _ = C/(‖C‖ : ℂ) := by
      field_simp [ofReal_ne_zero.mpr hA.ne']
    _ = _ := hphase

theorem dottie_sharp_amplitude_factorization (w : ℂ) :
    dottieSharpFactor w =
      (dottieSharpReferenceAmplitude : ℂ)*dottieSharpReferenceUnit*dottieSharpRelativeFactor w := by
  unfold dottieSharpReferenceUnit dottieSharpRelativeFactor
  field_simp [dottie_sharp_reference_factor_ne_zero,
    ofReal_ne_zero.mpr dottie_sharp_reference_amplitude_pos.ne']

noncomputable def dottieRelativeReferenceProjection : ℝ :=
  |(dottieSharpReferenceUnit *
    signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint).re|

theorem dottie_circle_reference_eq_relative_projection :
    dottieCircleReference = 2*dottieSharpReferenceAmplitude*dottieRelativeReferenceProjection := by
  let z := dottieReferencePoint
  let H := signedDirichletPolynomial archivedLatticeCoeff 276824064 z
  have hpoint : archivedRightCenter dottieHeight - (1/64 : ℂ) = z := by
    apply Complex.ext <;> norm_num [z,dottieReferencePoint,archivedRightCenter,Complex.mul_re,
      Complex.mul_im]
  have hmirror : 1-conj z = z := by
    apply Complex.ext <;> norm_num [z,dottieReferencePoint,Complex.mul_re,Complex.mul_im]
  rw [dottieCircleReference,hpoint,hmirror,Finset.sum_add_distrib,← map_sum,sum_dottieSharpSide]
  change ‖dottieSharpFactor z*H+conj (dottieSharpFactor z*H)‖ = _
  have he (v : ℂ) : v+conj v = ((2*v.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [two_mul]
  have hf : dottieSharpFactor z =
      (dottieSharpReferenceAmplitude : ℂ)*dottieSharpReferenceUnit := by
    unfold dottieSharpReferenceUnit
    rw [mul_comm,div_mul_cancel₀ _ (ofReal_ne_zero.mpr dottie_sharp_reference_amplitude_pos.ne')]
  rw [he,hf,mul_assoc,Complex.mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero,
    Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg dottie_sharp_reference_amplitude_pos.le]
  norm_num [dottieRelativeReferenceProjection,Complex.mul_re,H,z]
  ring

/-- Convert the relative Gamma certificate to the exact relative factor
used by the sharp-circle polynomial on either reflected address. -/
theorem dottie_sharp_relative_factor_with_error {w : ℂ}
    (hw : 0 < w.re) (hwi : 1 ≤ |w.im|) :
    ∃ error : ℂ, ‖error‖ ≤ 1/(3*|dottieReferencePoint.im|)+1/(3*|w.im|) ∧
      dottieSharpRelativeFactor w = Complex.exp (
        (Real.log archivedThetaScale : ℂ)*(w-dottieReferencePoint) +
        (dottieStirlingLeading w-dottieStirlingLeading dottieReferencePoint) + error) := by
  let z := dottieReferencePoint
  let b : ℂ := archivedThetaScale
  have hb : b ≠ 0 := ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have hz : 0 < z.re := by norm_num [z,dottieReferencePoint,Complex.mul_re]
  have hzi : 1 ≤ |z.im| := by
    have he : z.im = dottieHeight-1/512 := by
      norm_num [z,dottieReferencePoint,Complex.mul_im]
    rw [he]
    linarith only [dottieHeight_enclosure.1,le_abs_self (dottieHeight-1/512)]
  obtain ⟨e,he,hΓ⟩ := dottie_gamma_ratio_with_error hz hw hzi hwi
  refine ⟨e,he,?_⟩
  have hscale : (archivedDottieCompletionScale : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr archivedDottieCompletionScale_pos.ne'
  have hfac : dottieSharpRelativeFactor w = b^(w-z)*(Gamma w/Gamma z) := by
    unfold dottieSharpRelativeFactor dottieSharpFactor
    change (b^w*Gamma w/(archivedDottieCompletionScale : ℂ))/
      (b^z*Gamma z/(archivedDottieCompletionScale : ℂ)) = _
    rw [Complex.cpow_sub w z hb]
    field_simp [hscale,cpow_ne_zero_iff.mpr (Or.inl hb),Gamma_ne_zero_of_re_pos hz]
  rw [hfac,hΓ,Complex.cpow_def_of_ne_zero hb,← Complex.ofReal_log archivedThetaScale_pos.le,
    ← Complex.exp_add]
  congr 1
  ring

/-- Enclose the difference of the Stirling exponents using small differences
at the reference point. This avoids subtracting two large interval values. -/
theorem dottie_stirling_relative_linearization {z w : ℂ} (hz : 0 < z.re)
    (hsmall : ‖(w-z)/z‖ ≤ 1/2) :
    ‖dottieStirlingLeading w-dottieStirlingLeading z -
      ((w-z)*Complex.log z+(w-z-1/2)*((w-z)/z))‖ ≤
        ‖w-1/2‖*‖(w-z)/z‖^2 := by
  let q := (w-z)/z
  change ‖q‖ ≤ 1/2 at hsmall
  have hz₀ : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hq₀ : 0 < (1+q).re := by
    rw [add_re,one_re]
    linarith only [(abs_le.mp (Complex.abs_re_le_norm q)).1,hsmall]
  have hq₁ : 1+q ≠ 0 := by
    intro h
    simp [h] at hq₀
  have hqz : z*q = w-z := by
    dsimp only [q]
    rw [mul_comm,div_mul_cancel₀ _ hz₀]
  have hw : z*(1+q) = w := by rw [mul_add,mul_one,hqz]; ring
  have harg_z := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have harg_q := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hq₀))
  have hlog : Complex.log w = Complex.log z+Complex.log (1+q) := by
    rw [← hw]
    exact Complex.log_mul hz₀ hq₁ ⟨by linarith only [harg_z.1,harg_q.1],
      by linarith only [harg_z.2,harg_q.2]⟩
  have he : dottieStirlingLeading w-dottieStirlingLeading z -
      ((w-z)*Complex.log z+(w-z-1/2)*q) = (w-1/2)*(Complex.log (1+q)-q) := by
    rw [dottieStirlingLeading,dottieStirlingLeading,hlog]
    linear_combination hqz
  have hq_lt : ‖q‖ < 1 := hsmall.trans_lt (by norm_num)
  have hi : (1-‖q‖)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (div_le_iff₀ (sub_pos.mpr hq_lt)).2
    linarith only [hsmall]
  have hlog_norm := Complex.norm_log_one_add_sub_self_le hq_lt
  have herror : ‖Complex.log (1+q)-q‖ ≤ ‖q‖^2 := by
    exact hlog_norm.trans (by nlinarith only [mul_le_mul_of_nonneg_left hi (sq_nonneg ‖q‖)])
  change ‖dottieStirlingLeading w-dottieStirlingLeading z -
    ((w-z)*Complex.log z+(w-z-1/2)*q)‖ ≤ ‖w-1/2‖*‖q‖^2
  rw [he,norm_mul]
  exact mul_le_mul_of_nonneg_left herror (norm_nonneg _)

/-- Stable exponential input for replaying the sharp-circle ratio. -/
theorem dottie_sharp_relative_factor_stable {w : ℂ} (hw : 0 < w.re) (hwi : 1 ≤ |w.im|)
    (hsmall : ‖(w-dottieReferencePoint)/dottieReferencePoint‖ ≤ 1/2) :
    let z := dottieReferencePoint
    let δ := w-z
    let q := δ/z
    ∃ error : ℂ, ‖error‖ ≤ 1/(3*|z.im|)+1/(3*|w.im|)+‖w-1/2‖*‖q‖^2 ∧
      dottieSharpRelativeFactor w = Complex.exp (
        (Real.log archivedThetaScale : ℂ)*δ+δ*Complex.log z+(δ-1/2)*q+error) := by
  let z := dottieReferencePoint
  let δ := w-z
  let q := δ/z
  let E := dottieStirlingLeading w-dottieStirlingLeading z -
    (δ*Complex.log z+(δ-1/2)*q)
  obtain ⟨e,he,hΓ⟩ := dottie_sharp_relative_factor_with_error hw hwi
  have hz : 0 < z.re := by norm_num [z,dottieReferencePoint,Complex.mul_re]
  have hb : ‖E‖ ≤ ‖w-1/2‖*‖q‖^2 := dottie_stirling_relative_linearization hz hsmall
  refine ⟨e+E,(norm_add_le _ _).trans (add_le_add he hb),?_⟩
  rw [hΓ]
  congr 1
  dsimp only [E,δ,z]
  ring

noncomputable def dottieRelativeSharpModelIm (w : ℂ) : ℝ :=
  (dottieSharpReferenceUnit *
    (dottieSharpRelativeFactor w*dottieSharpMomentsPolynomial w -
      dottieSharpRelativeFactor (1-conj w)*dottieSharpMomentsPolynomial (1-conj w))).im

private theorem dottie_sharp_model_im_eq_relative (w : ℂ) :
    (dottieSharpMomentsCompletion w).im = dottieSharpReferenceAmplitude*dottieRelativeSharpModelIm w := by
  rw [dottieSharpMomentsCompletion,add_im,conj_im,dottie_sharp_amplitude_factorization w,
    dottie_sharp_amplitude_factorization (1-conj w)]
  have hmul (v : ℂ) : ((dottieSharpReferenceAmplitude : ℂ)*v).im =
      dottieSharpReferenceAmplitude*v.im := by simp [Complex.mul_im]
  rw [show (dottieSharpReferenceAmplitude : ℂ)*dottieSharpReferenceUnit*dottieSharpRelativeFactor w*
        dottieSharpMomentsPolynomial w =
      (dottieSharpReferenceAmplitude : ℂ)*
        (dottieSharpReferenceUnit*(dottieSharpRelativeFactor w*dottieSharpMomentsPolynomial w)) by ring,
    show (dottieSharpReferenceAmplitude : ℂ)*dottieSharpReferenceUnit*
        dottieSharpRelativeFactor (1-conj w)*dottieSharpMomentsPolynomial (1-conj w) =
      (dottieSharpReferenceAmplitude : ℂ)*(dottieSharpReferenceUnit*
        (dottieSharpRelativeFactor (1-conj w)*dottieSharpMomentsPolynomial (1-conj w))) by ring,
    hmul,hmul,dottieRelativeSharpModelIm,mul_sub,sub_im]
  ring

private theorem dottie_sharp_factor_norm_eq_relative (w : ℂ) :
    ‖dottieSharpFactor w‖ = dottieSharpReferenceAmplitude*‖dottieSharpRelativeFactor w‖ := by
  unfold dottieSharpRelativeFactor
  rw [norm_div]
  change _ = dottieSharpReferenceAmplitude*(‖dottieSharpFactor w‖/dottieSharpReferenceAmplitude)
  rw [mul_comm,div_mul_cancel₀ _ dottie_sharp_reference_amplitude_pos.ne']

/-- Any upper bound in relative completion units, including the exact
Taylor allowance, supplies the original normalized imaginary margin. -/
theorem dottie_sharp_margin_of_relative_model {m : ℝ} {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048))
    (hmodel : dottieRelativeSharpModelIm w +
        (‖dottieSharpRelativeFactor w‖+‖dottieSharpRelativeFactor (1-conj w)‖)/10^11 ≤
      -(2*m*(w.re-1/2)*dottieRelativeReferenceProjection)) :
    (dottieSharpPrefix w).im ≤ -(m*((w.re-1/2)*dottieCircleReference)) := by
  have hE := dottie_sharp_circle_completed_moments_error hw
  rw [dottie_sharp_factor_norm_eq_relative w,
    dottie_sharp_factor_norm_eq_relative (1-conj w)] at hE
  have hI := ((le_abs_self (dottieSharpPrefix w-dottieSharpMomentsCompletion w).im).trans
    (abs_im_le_norm _)).trans hE
  rw [sub_im,dottie_sharp_model_im_eq_relative] at hI
  rw [dottie_circle_reference_eq_relative_projection]
  nlinarith only [hI,mul_le_mul_of_nonneg_left hmodel dottie_sharp_reference_amplitude_pos.le]

/-- A cover of the original angular interval carries the relative-model
bound to every point of the original measuring circle. -/
theorem dottie_sharp_sphere_margin_of_angle_model {m : ℝ}
    (h : ∀ θ ∈ Set.Ioc (0 : ℝ) (2*Real.pi),
      let w := circleMap (archivedRightCenter dottieHeight) (31/2048) θ
      dottieRelativeSharpModelIm w +
          (‖dottieSharpRelativeFactor w‖+‖dottieSharpRelativeFactor (1-conj w)‖)/10^11 ≤
        -(2*m*(w.re-1/2)*dottieRelativeReferenceProjection)) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(m*((w.re-1/2)*dottieCircleReference)) := by
  intro w hw
  have hcover : circleMap (archivedRightCenter dottieHeight) (31/2048) ''
      Set.Ioc (0 : ℝ) (2*Real.pi) =
      Metric.sphere (archivedRightCenter dottieHeight) (31/2048) := by
    rw [image_circleMap_Ioc,abs_of_nonneg (by norm_num)]
  have ⟨θ,hθ,hEq⟩ : w ∈ circleMap (archivedRightCenter dottieHeight) (31/2048) ''
      Set.Ioc (0 : ℝ) (2*Real.pi) := hcover ▸ hw
  exact dottie_sharp_margin_of_relative_model hw (hEq ▸ h θ hθ)

#print axioms dottie_circle_reference_eq_relative_projection
#print axioms dottie_sharp_reference_unit_phase_interval
#print axioms dottie_sharp_relative_factor_with_error
#print axioms dottie_stirling_relative_linearization
#print axioms dottie_sharp_relative_factor_stable
#print axioms dottie_sharp_margin_of_relative_model
#print axioms dottie_sharp_sphere_margin_of_angle_model

end QuarticModel
