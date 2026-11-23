import DottieSharpAffineExponent
import DottieDividedSinh

/-! Keep the factor `2 * (w.re - 1/2)` exact when pairing the two reflected
terms of the sharp-prefix Taylor model. -/

namespace QuarticModel

open Complex Finset SuperZeta.StirlingCorrection
open scoped ComplexConjugate
set_option autoImplicit false

private noncomputable def dottieHorner (z : ℂ) : ℕ → (ℕ → ℂ) → ℂ
  | 0, _ => 0
  | n+1, f => f 0 + z*dottieHorner z n (fun k => f (k+1))

private theorem dottieHorner_eq_sum (z : ℂ) (n : ℕ) (f : ℕ → ℂ) :
    dottieHorner z n f = ∑ k ∈ range n, f k*z^k := by
  induction n generalizing f with
  | zero => simp [dottieHorner]
  | succ n ih =>
    rw [dottieHorner,ih,Finset.mul_sum,Finset.sum_range_succ']
    simp only [pow_zero,mul_one]
    rw [add_comm (f 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring

/-- Horner evaluation at the two arguments `v+x` and `v-x`. The second
coordinate is the divided odd part, including at `x=0`. -/
noncomputable def dottieReflectedHorner (v x : ℂ) : ℕ → (ℕ → ℂ) → ℂ × ℂ
  | 0, _ => (0,0)
  | n+1, f =>
    let p := dottieReflectedHorner v x n (fun k => f (k+1))
    (f 0 + v*p.1 + x^2*p.2, p.1 + v*p.2)

theorem dottie_reflected_horner_spec (v x : ℂ) (n : ℕ) (f : ℕ → ℂ) :
    let p := dottieReflectedHorner v x n f
    (∑ k ∈ range n, f k*(v+x)^k) = p.1+x*p.2 ∧
      (∑ k ∈ range n, f k*(v-x)^k) = p.1-x*p.2 := by
  rw [← dottieHorner_eq_sum,← dottieHorner_eq_sum]
  induction n generalizing f with
  | zero => simp [dottieHorner,dottieReflectedHorner]
  | succ n ih =>
    obtain ⟨hPos,hNeg⟩ := ih (fun k => f (k+1))
    constructor
    · simp only [dottieHorner,dottieReflectedHorner,hPos]
      ring
    · simp only [dottieHorner,dottieReflectedHorner,hNeg]
      ring

private theorem exponential_difference (c x y a b : ℂ) (hx : x ≠ 0) :
    exp ((x+y)*c)*(a+x*b)-exp ((-x+y)*c)*(a-x*b) =
      2*x*(exp (y*c)*(cosh (x*c)*b+(sinh (x*c)/x)*a)) := by
  rw [show (x+y)*c = y*c+x*c by ring,
    show (-x+y)*c = y*c+ -(x*c) by ring,
    Complex.exp_add (y*c) (x*c),Complex.exp_add (y*c) (-(x*c)),Complex.cosh,Complex.sinh]
  field_simp [hx]
  ring

noncomputable def dottieSharpFactoredProjection (w : ℂ) : ℝ :=
  let x := ((w.re-1/2 : ℝ) : ℂ)
  let y := ((w.im-dottieReferencePoint.im : ℝ) : ℂ)*I
  let v := ((w.im-dottieHeight : ℝ) : ℂ)*I
  let c := dottieSharpExponentSlope
  let p := dottieReflectedHorner v x 17
    (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter)
  (dottieSharpReferenceUnit*(exp (y*c)*(cosh (x*c)*p.2+(sinh (x*c)/x)*p.1))).im

theorem dottie_sharp_divided_sinh_radius {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    let x := ((w.re-1/2 : ℝ) : ℂ)
    let c := dottieSharpExponentSlope
    ‖sinh (x*c)/x-dottieDividedSinhPolynomial c x‖ ≤ 92*(2:ℝ)^24/(25 : ℕ).factorial := by
  let x := ((w.re-1/2 : ℝ) : ℂ)
  let c := dottieSharpExponentSlope
  have hgap := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hx : 0 < w.re-1/2 := by linarith only [hgap]
  have hx₀ : x ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hd := (dottie_sharp_affine_domain_on_circle hw).1
  have hnorm : ‖x‖ ≤ 1/25 := by
    change ‖((w.re-1/2 : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs]
    have h := abs_re_le_norm (w-dottieReferencePoint)
    simp only [sub_re,show dottieReferencePoint.re = 1/2 by
      norm_num [dottieReferencePoint,Complex.mul_re]] at h
    exact h.trans hd
  have hcs : ‖c‖ ≤ 46 := dottie_sharp_exponent_slope_norm
  have hzc : ‖x*c‖ ≤ 2 := by
    rw [norm_mul]
    have h := mul_le_mul hnorm hcs (norm_nonneg _) (by norm_num)
    linarith only [h]
  exact dottie_divided_sinh_radius hx₀ hcs hzc

private noncomputable def dottieSharpAffineFactor (w : ℂ) : ℂ :=
  exp ((w-dottieReferencePoint)*dottieSharpExponentSlope)

private theorem dottie_factored_projection_eq (w : ℂ) (hx : w.re ≠ 1/2) :
    (dottieSharpReferenceUnit *
      (dottieSharpAffineFactor w*dottieSharpMomentsPolynomial w-
        dottieSharpAffineFactor (1-conj w)*dottieSharpMomentsPolynomial (1-conj w))).im =
      (2*(w.re-1/2))*dottieSharpFactoredProjection w := by
  let x := ((w.re-1/2 : ℝ) : ℂ)
  let y := ((w.im-dottieReferencePoint.im : ℝ) : ℂ)*I
  let v := ((w.im-dottieHeight : ℝ) : ℂ)*I
  let c := dottieSharpExponentSlope
  let p := dottieReflectedHorner v x 17
    (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter)
  have hz : x ≠ 0 := ofReal_ne_zero.mpr (sub_ne_zero.mpr hx)
  have hPos : w-dottieReferencePoint = x+y := by
    apply Complex.ext <;> norm_num [x,y,dottieReferencePoint,Complex.mul_re,Complex.mul_im]
  have hNeg : (1-conj w)-dottieReferencePoint = -x+y := by
    apply Complex.ext <;> norm_num [x,y,dottieReferencePoint,Complex.mul_re,Complex.mul_im]
    ring
  have hvPos : w-dottieSharpCenter = v+x := by
    apply Complex.ext <;> norm_num [x,v,dottieSharpCenter,Complex.mul_re,Complex.mul_im]
  have hvNeg : (1-conj w)-dottieSharpCenter = v-x := by
    apply Complex.ext <;> norm_num [x,v,dottieSharpCenter,Complex.mul_re,Complex.mul_im]
    ring
  obtain ⟨hPPos,hPNeg⟩ := dottie_reflected_horner_spec v x 17
    (signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter)
  have hpolyPos : dottieSharpMomentsPolynomial w = p.1+x*p.2 := by
    rw [dottieSharpMomentsPolynomial,hvPos]
    exact hPPos
  have hpolyNeg : dottieSharpMomentsPolynomial (1-conj w) = p.1-x*p.2 := by
    rw [dottieSharpMomentsPolynomial,hvNeg]
    exact hPNeg
  simp only [dottieSharpAffineFactor,hPos,hNeg,hpolyPos,hpolyNeg]
  rw [exponential_difference c x y p.1 p.2 hz]
  change (dottieSharpReferenceUnit * (2*x*(exp (y*c)*
      (cosh (x*c)*p.2+(sinh (x*c)/x)*p.1)))).im =
    (2*(w.re-1/2))*(dottieSharpReferenceUnit * (exp (y*c)*
      (cosh (x*c)*p.2+(sinh (x*c)/x)*p.1))).im
  rw [show dottieSharpReferenceUnit * (2*x*(exp (y*c)*
      (cosh (x*c)*p.2+(sinh (x*c)/x)*p.1))) =
    (2*x)*(dottieSharpReferenceUnit * (exp (y*c)*
      (cosh (x*c)*p.2+(sinh (x*c)/x)*p.1))) by ring]
  simp [x,Complex.mul_re,Complex.mul_im]

private theorem dottie_factored_model_error {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    dottieRelativeSharpModelIm w ≤
      (2*(w.re-1/2))*dottieSharpFactoredProjection w+
        (18/10^12)*(‖dottieSharpMomentsPolynomial w‖+
          ‖dottieSharpMomentsPolynomial (1-conj w)‖) := by
  let r := 1-conj w
  let P := dottieSharpMomentsPolynomial
  let A := dottieSharpAffineFactor
  let R := dottieSharpRelativeFactor
  let U := dottieSharpReferenceUnit
  have hU : ‖U‖ = 1 := by
    obtain ⟨φ,_,_,hφ⟩ := dottie_sharp_reference_unit_phase_interval
    change ‖dottieSharpReferenceUnit‖ = 1
    rw [hφ,norm_exp_ofReal_mul_I]
  obtain ⟨hw₀,hr₀⟩ := dottie_sharp_affine_domain_on_circle hw
  have hw₁ : ‖R w-A w‖ ≤ 18/10^12 := dottie_sharp_relative_factor_sub_affine hw₀
  have hr₁ : ‖R r-A r‖ ≤ 18/10^12 := dottie_sharp_relative_factor_sub_affine hr₀
  have hgap := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hx : w.re ≠ 1/2 := (by linarith only [hgap] : (1/2 : ℝ) < w.re).ne'
  have he : U*(R w*P w-R r*P r)-U*(A w*P w-A r*P r) =
      U*((R w-A w)*P w-(R r-A r)*P r) := by ring
  have hb : ‖U*(R w*P w-R r*P r)-U*(A w*P w-A r*P r)‖ ≤
      (18/10^12)*(‖P w‖+‖P r‖) := by
    rw [he,norm_mul,hU,one_mul]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul,norm_mul,mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right hw₁ (norm_nonneg _))
      (mul_le_mul_of_nonneg_right hr₁ (norm_nonneg _))
  have hp := ((le_abs_self (U*(R w*P w-R r*P r)-U*(A w*P w-A r*P r)).im).trans
    (abs_im_le_norm _)).trans hb
  rw [sub_im] at hp
  change dottieRelativeSharpModelIm w - (U*(A w*P w-A r*P r)).im ≤ _ at hp
  have hconst : (U*(A w*P w-A r*P r)).im =
      (2*(w.re-1/2))*dottieSharpFactoredProjection w := dottie_factored_projection_eq w hx
  rw [hconst] at hp
  linarith only [hp]

/-- Upper reading including the two affine factor errors and the two
original degree-16 Taylor errors, divided by the exact horizontal distance. -/
noncomputable def dottieSharpFactoredUpper (w : ℂ) : ℝ :=
  dottieSharpFactoredProjection w+
    ((18/10^12)*(‖dottieSharpMomentsPolynomial w‖+
      ‖dottieSharpMomentsPolynomial (1-conj w)‖)+18/10^11)/(2*(w.re-1/2))

/-- Only the normalized, factored projection and the two polynomial norms
are needed on the measuring circle. -/
theorem dottie_sharp_margin_of_factored_projection {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048))
    (hmodel : dottieSharpFactoredUpper w ≤ -(190.37*dottieRelativeReferenceProjection)) :
    (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) := by
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hp : 0 < 2*(w.re-1/2) := by linarith only [hx]
  unfold dottieSharpFactoredUpper at hmodel
  have hscaled := mul_le_mul_of_nonneg_left hmodel hp.le
  rw [mul_add,mul_div_cancel₀ _ hp.ne'] at hscaled
  have herror := dottie_factored_model_error hw
  have hnorm := dottie_sharp_pair_norm_le_eighteen hw
  apply dottie_sharp_margin_of_relative_model hw
  have ht := div_le_div_of_nonneg_right hnorm (by norm_num : (0:ℝ) ≤ 10^11)
  nlinarith only [hscaled,herror,ht]

#print axioms dottie_reflected_horner_spec
#print axioms dottie_sharp_divided_sinh_radius
#print axioms dottie_factored_projection_eq
#print axioms dottie_sharp_margin_of_factored_projection

end QuarticModel
