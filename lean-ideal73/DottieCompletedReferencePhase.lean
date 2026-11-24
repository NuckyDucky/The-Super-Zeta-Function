import DottieSignedMoments
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Enclose the phase of the full completion prefactor at the exact original
reference point. This leaves only the signed polynomial in the projection. -/

open Complex Finset

namespace QuarticModel

open SuperZeta.StirlingCorrection
open private log_two_enclosure from DottieReferencePhaseEnclosure
open private normalized_exp from DottieGammaPhase

private theorem binary_log_bound {r : ℝ} (hr : 0 < r) (m K : ℕ)
    (hx : |1-r/2^m| < 1) :
    |Real.log r - (m * Real.log 2 - ∑ k ∈ range K, (1-r/2^m)^(k+1)/(k+1))| ≤
      |1-r/2^m|^(K+1)/(1-|1-r/2^m|) := by
  have he : (2:ℝ)^m * (r/2^m) = r := mul_div_cancel₀ _ (by positivity)
  have hl : Real.log r = m * Real.log 2 + Real.log (r/2^m) := by
    conv_lhs => rw [← he]
    rw [Real.log_mul (by positivity : (2:ℝ)^m ≠ 0) (by positivity), Real.log_pow]
  have h := Real.abs_log_sub_add_sum_range_le hx K
  rw [show (1:ℝ)-(1-r/2^m) = r/2^m by ring] at h
  rw [hl, show (m:ℝ)*Real.log 2+Real.log (r/2^m) -
      ((m:ℝ)*Real.log 2 - ∑ k ∈ range K, (1-r/2^m)^(k+1)/(k+1)) =
      Real.log (r/2^m) + ∑ k ∈ range K, (1-r/2^m)^(k+1)/(k+1) by ring]
  simpa only [add_comm] using h

private theorem log_discriminant_enclosure :
    30.90853456234470711944 < Real.log 26509772707289 ∧
      Real.log 26509772707289 < 30.90853456234470711945 := by
  have h := binary_log_bound (r := 26509772707289) (by norm_num) 45 40 (by norm_num)
  norm_num1 at h
  obtain ⟨h₀,h₁⟩ := abs_le.mp h
  constructor <;> linarith [log_two_enclosure.1, log_two_enclosure.2]

private theorem log_pi_enclosure :
    1.14472988584940017414 < Real.log Real.pi ∧ Real.log Real.pi < 1.14472988584940017415 := by
  constructor
  · have h := binary_log_bound (r := 3.14159265358979323846) (by norm_num) 2 40 (by norm_num)
    norm_num1 at h
    have hp := Real.log_lt_log (by norm_num) Real.pi_gt_d20
    linarith [(abs_le.mp h).1, log_two_enclosure.1]
  · have h := binary_log_bound (r := 3.14159265358979323847) (by norm_num) 2 40 (by norm_num)
    norm_num1 at h
    have hp := Real.log_lt_log Real.pi_pos Real.pi_lt_d20
    linarith [(abs_le.mp h).2, log_two_enclosure.2]

private theorem log_scale_enclosure :
    14.30953739532295338557 < Real.log archivedThetaScale ∧
      Real.log archivedThetaScale < 14.30953739532295338559 := by
  unfold archivedThetaScale
  rw [Real.log_div (by positivity) Real.pi_ne_zero, Real.log_sqrt (by norm_num)]
  constructor <;> linarith [log_discriminant_enclosure.1, log_discriminant_enclosure.2,
    log_pi_enclosure.1, log_pi_enclosure.2]

/-- Express the same reference unit using the unscaled signed Dirichlet sum.
The phase of the original Gamma and conductor prefactors is certified. -/
theorem dottieCircleReference_eq_completed_phase_and_unit :
    ∃ phase : ℝ, 3.92292369 < phase ∧ phase < 3.92292670 ∧
      ((archivedThetaScale : ℂ)^dottieReferencePoint * Gamma dottieReferencePoint) /
        (‖(archivedThetaScale : ℂ)^dottieReferencePoint * Gamma dottieReferencePoint‖ : ℂ) =
          Complex.exp ((phase : ℂ)*I) ∧
      dottieCircleReference =
        (2 * ‖Gamma dottieReferencePoint‖ / archivedDottieCompletionScale *
          ‖(archivedThetaScale : ℂ)^dottieReferencePoint‖) *
        |(Complex.exp ((phase : ℂ)*I) *
          signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint).re| := by
  let t := dottieHeight-1/512
  let z := dottieReferencePoint
  let b : ℂ := (archivedThetaScale : ℂ)^z
  let θ := t*Real.log archivedThetaScale-2*Real.pi*10307936267084
  have hlo : 4526119322477.943440190398 < t := by
    dsimp [t]
    linarith [dottieHeight_enclosure.1]
  have hhi : t < 4526119322477.943440204807 := by
    dsimp [t]
    linarith [dottieHeight_enclosure.2]
  have ht : 0 < t := by linarith
  have hprod₀ := mul_le_mul hlo.le log_scale_enclosure.1.le (by norm_num) ht.le
  have hprod₁ := mul_le_mul hhi.le log_scale_enclosure.2.le
    (by linarith [log_scale_enclosure.1] : 0 ≤ Real.log archivedThetaScale) (by norm_num)
  have hθ₀ : 6.138785 < θ := by
    dsimp [θ]
    linarith only [hprod₀, Real.pi_lt_d20]
  have hθ₁ : θ < 6.138786 := by
    dsimp [θ]
    linarith only [hprod₁, Real.pi_gt_d20]
  have hb₀ : (archivedThetaScale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have hb : b ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hb₀)
  have hbphase : b / (‖b‖ : ℂ) = Complex.exp ((θ : ℂ)*I) := by
    dsimp only [b]
    rw [Complex.cpow_def_of_ne_zero hb₀, normalized_exp]
    have hz : z.im = t := by simp [z, t, dottieReferencePoint, Complex.mul_im]
    rw [← Complex.ofReal_log archivedThetaScale_pos.le,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hz,
      mul_comm (Real.log archivedThetaScale) t]
    have hp : ((↑(t*Real.log archivedThetaScale) : ℂ)*I) =
        (θ : ℂ)*I + (10307936267084 : ℕ)*(2*(Real.pi : ℂ)*I) := by
      dsimp only [θ]
      push_cast
      ring
    rw [hp, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  obtain ⟨φ, hφ₀, hφ₁, hunit, hS⟩ := dottieCircleReference_eq_gamma_phase_projection
  let phase := φ+θ-2*Real.pi
  have hE : Complex.exp ((φ : ℂ)*I) * b = (‖b‖ : ℂ) * Complex.exp ((phase : ℂ)*I) := by
    have hbe := (div_eq_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb))).mp hbphase
    conv_lhs => rw [hbe, ← mul_assoc, ← Complex.exp_add]
    have h : (φ : ℂ)*I + (θ : ℂ)*I = (phase : ℂ)*I + 2*(Real.pi : ℂ)*I := by
      dsimp only [phase]
      push_cast
      ring
    rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, mul_comm]
  refine ⟨phase, by dsimp [phase]; linarith [Real.pi_lt_d20],
    by dsimp [phase]; linarith [Real.pi_gt_d20], ?_, ?_⟩
  · change b * Gamma z / (‖b * Gamma z‖ : ℂ) = _
    rw [norm_mul,Complex.ofReal_mul]
    calc
      _ = (Gamma z/(‖Gamma z‖ : ℂ))*(b/(‖b‖ : ℂ)) := by ring
      _ = _ := by
        rw [hunit,← mul_div_assoc]
        exact (div_eq_iff (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hb))).2
          (hE.trans (mul_comm _ _))
  rw [hS, dottieReferencePolynomial_eq_scaled_dirichlet, ← mul_assoc]
  change (2 * ‖Gamma z‖ / archivedDottieCompletionScale) *
      |((Complex.exp ((φ : ℂ)*I) * b) * signedDirichletPolynomial archivedLatticeCoeff 276824064 z).re| =
      (2 * ‖Gamma z‖ / archivedDottieCompletionScale * ‖b‖) *
      |(Complex.exp ((phase : ℂ)*I) * signedDirichletPolynomial archivedLatticeCoeff 276824064 z).re|
  rw [hE, mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    abs_mul, abs_of_nonneg (norm_nonneg _)]
  ring

theorem dottieCircleReference_eq_completed_phase :
    ∃ phase : ℝ, 3.92292369 < phase ∧ phase < 3.92292670 ∧
      dottieCircleReference =
        (2 * ‖Gamma dottieReferencePoint‖ / archivedDottieCompletionScale *
          ‖(archivedThetaScale : ℂ)^dottieReferencePoint‖) *
        |(Complex.exp ((phase : ℂ)*I) *
          signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint).re| := by
  obtain ⟨φ,hlo,hhi,_,he⟩ := dottieCircleReference_eq_completed_phase_and_unit
  exact ⟨φ,hlo,hhi,he⟩

/-- The reference Taylor polynomial in the exact factorial-divided moments
at `1/2+iT_D`, evaluated at displacement `−i/512`. -/
noncomputable def dottieReferenceTaylorPolynomial : ℂ :=
  ∑ k ∈ range 17,
    signedMoment archivedLatticeCoeff 276824064 (1/2 + (dottieHeight : ℂ)*I) k *
      (-(1/512 : ℂ)*I)^k

private theorem projection_pos {D P : ℂ} {φ : ℝ}
    (herror : ‖D-P‖ < 3/10^30) (hre : |P.re| ≤ 4/5) (him : 1 ≤ P.im)
    (hφ₀ : 3.92292 < φ) (hφ₁ : φ < 3.92293) :
    0 < (Complex.exp ((φ : ℂ)*I)*D).re := by
  have reError := (Complex.abs_re_le_norm (D-P)).trans_lt herror
  have imError := (Complex.abs_im_le_norm (D-P)).trans_lt herror
  rw [Complex.sub_re] at reError
  rw [Complex.sub_im] at imError
  have hRe : |D.re| ≤ 81/100 := by
    calc
      |D.re| = |D.re-P.re + P.re| := by rw [sub_add_cancel]
      _ ≤ |D.re-P.re|+|P.re| := abs_add_le ..
      _ ≤ _ := by linarith
  have hIm : 99/100 ≤ D.im := by
    have hi := (abs_lt.mp imError).1
    linarith
  let x := φ-Real.pi
  have hx₀ : 0.78 < x := by dsimp [x]; linarith [Real.pi_lt_d20]
  have hx₁ : x < 4/5 := by dsimp [x]; linarith [Real.pi_gt_d20]
  have hxpos : 0 < x := by linarith
  have hsin : Real.sin φ ≤ -(2/3) := by
    rw [show φ=x+Real.pi by dsimp [x]; ring, Real.sin_add_pi]
    have h := Real.sin_gt_sub_cube hxpos
    have hcube := pow_le_pow_left₀ hxpos.le hx₁.le 3
    linarith
  have hcos : |Real.cos φ| ≤ 3/4 := by
    by_contra! hb
    have hsq := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3/4) hb.le 2
    have hss := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2/3)
      (by linarith only [hsin] : (2:ℝ)/3 ≤ -(Real.sin φ)) 2
    rw [sq_abs] at hsq
    rw [neg_sq] at hss
    linarith [Real.sin_sq_add_cos_sq φ]
  have hc := mul_le_mul hcos hRe (abs_nonneg _) (by norm_num)
  rw [← abs_mul] at hc
  have hcosprod := (neg_le_neg hc).trans (neg_abs_le (Real.cos φ * D.re))
  have hsinprod := mul_le_mul (by linarith only [hsin] : (2:ℝ)/3 ≤ -(Real.sin φ)) hIm
    (by norm_num) (by linarith only [hsin])
  rw [Complex.mul_re, Complex.exp_re, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, sub_zero, mul_one, add_zero,
    Real.exp_zero, one_mul]
  linarith

private theorem projection_scale_pos {S C y : ℝ} (hs : S = C*|y|) (hc : 0 < C) (hy : 0 < y) :
    0 < S := by
  rw [hs, abs_of_pos hy]
  exact mul_pos hc hy

private theorem positive_of_phase_projection {S C : ℝ} {D P : ℂ}
    (hphase : ∃ φ : ℝ, 3.92292369 < φ ∧ φ < 3.92292670 ∧
      S = C * |(Complex.exp ((φ : ℂ)*I)*D).re|)
    (hscale : 0 < C) (herror : ‖D-P‖ < 3/10^30)
    (hre : |P.re| ≤ 4/5) (him : 1 ≤ P.im) : 0 < S := by
  obtain ⟨φ, hφ₀, hφ₁, hunit⟩ := hphase
  exact projection_scale_pos hunit hscale
    (projection_pos herror hre him (by linarith only [hφ₀]) (by linarith only [hφ₁]))

private theorem completed_projection_scale_pos :
    0 < (2 * ‖Gamma dottieReferencePoint‖ / archivedDottieCompletionScale *
      ‖(archivedThetaScale : ℂ)^dottieReferencePoint‖) := by
  have hΓ : 0 < ‖Gamma dottieReferencePoint‖ := by
    apply norm_pos_iff.mpr (Gamma_ne_zero_of_re_pos _)
    norm_num [dottieReferencePoint, Complex.mul_re]
  have hb : (archivedThetaScale : ℂ)^dottieReferencePoint ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'))
  exact mul_pos (div_pos (mul_pos (by norm_num : (0:ℝ) < 2) hΓ) archivedDottieCompletionScale_pos)
    (norm_pos_iff.mpr hb)

private theorem dottie_reference_taylor_error :
    ‖signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint -
      dottieReferenceTaylorPolynomial‖ < 3/10^30 :=
  dottie_reference_taylor_absolute_error

/-- Two coarse statements about the exact signed moments suffice for
positivity of the original Dottie reference unit. -/
theorem dottieCircleReference_pos_of_moments
    (hre : |dottieReferenceTaylorPolynomial.re| ≤ 4/5)
    (him : 1 ≤ dottieReferenceTaylorPolynomial.im) : 0 < dottieCircleReference :=
  positive_of_phase_projection dottieCircleReference_eq_completed_phase
    completed_projection_scale_pos dottie_reference_taylor_error hre him

#print axioms dottieCircleReference_eq_completed_phase_and_unit
#print axioms dottieCircleReference_eq_completed_phase
#print axioms dottieCircleReference_pos_of_moments

end QuarticModel
