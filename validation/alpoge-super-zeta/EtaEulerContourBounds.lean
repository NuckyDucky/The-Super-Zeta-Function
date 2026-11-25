import EtaEulerDisk
import Mathlib.Data.Nat.Choose.Sum

/-! Two finite center estimates suffice for the eta contour. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex Metric Set

def exponentScale (j : ℕ) : ℂ := ↑(-2 * Real.log ((j:ℝ)+1))

def exponentialTerm (j : ℕ) (s : ℂ) : ℂ := Complex.exp (exponentScale j * s)

private theorem power_as_exp (j : ℕ) (s : ℂ) :
    ((j:ℂ)+1)^(-(2*s)) = exponentialTerm j s := by
  have hp : 0 < (j:ℝ)+1 := by positivity
  have h0 : ((((j:ℝ)+1:ℝ):ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  rw [show (j:ℂ)+1 = ((((j:ℝ)+1:ℝ):ℂ)) by push_cast; rfl,
    Complex.cpow_def_of_ne_zero h0, ← Complex.ofReal_log hp.le]
  congr 1
  push_cast [exponentialTerm, exponentScale]
  ring

private theorem expTerm_hasDeriv (j : ℕ) (s : ℂ) :
    HasDerivAt (exponentialTerm j) (exponentScale j * exponentialTerm j s) s := by
  have h := (((hasDerivAt_id s).const_mul (exponentScale j)).cexp)
  rw [mul_comm (exponentScale j)]
  simpa only [exponentialTerm, id_eq, mul_one] using h

def etaDiskDerivative (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range 128, ∑ j ∈ Finset.range (k+1),
    EtaMellin.binomialWeight k j * (exponentScale j * exponentialTerm j s)

theorem deriv_etaDiskApprox (s : ℂ) : deriv etaDiskApprox s = etaDiskDerivative s := by
  have he : etaDiskApprox = fun z => ∑ k ∈ Finset.range 128, ∑ j ∈ Finset.range (k+1),
      EtaMellin.binomialWeight k j * exponentialTerm j z := by
    funext z
    simp only [etaDiskApprox, EtaMellin.etaEulerSum, power_as_exp]
  rw [he]
  apply HasDerivAt.deriv
  apply HasDerivAt.sum
  intro k _
  apply HasDerivAt.sum
  intro j _
  exact (expTerm_hasDeriv j s).const_mul _

private def secondReading (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range 128, ∑ j ∈ Finset.range (k+1),
    EtaMellin.binomialWeight k j * (exponentScale j * (exponentScale j * exponentialTerm j s))

private theorem etaDiskDerivative_hasDeriv (s : ℂ) : HasDerivAt etaDiskDerivative (secondReading s) s := by
  apply HasDerivAt.sum
  intro k _
  apply HasDerivAt.sum
  intro j _
  exact ((expTerm_hasDeriv j s).const_mul (exponentScale j)).const_mul _

private theorem log_damping (u : ℝ) (hu : 0 ≤ u) : u^2 * Real.exp (-u) ≤ 1 := by
  have he : 2 ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have hx : u ≤ Real.exp (u/2) := by
    calc
      u ≤ 2 * Real.exp (u/2-1) := by linarith only [Real.add_one_le_exp (u/2-1)]
      _ = Real.exp (u/2)*(2/Real.exp 1) := by rw [Real.exp_sub]; ring
      _ ≤ _ := mul_le_of_le_one_right (Real.exp_pos _).le
        ((div_le_one (Real.exp_pos _)).mpr he)
  calc
    _ ≤ Real.exp (u/2)^2 * Real.exp (-u) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu hx _) (Real.exp_pos _).le
    _ = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have h : ((2:ℕ):ℝ)*(u/2) + -u = 0 := by push_cast; ring
      rw [h, Real.exp_zero]

private theorem term_second_bound (j : ℕ) {s : ℂ} (hs : 1/3 ≤ 2*s.re) :
    ‖exponentScale j * (exponentScale j * exponentialTerm j s)‖ ≤ 36 := by
  let L := Real.log ((j:ℝ)+1)
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j])
  have hA : (-2*L)*s.re ≤ -(L/3) := by
    nlinarith only [mul_nonneg hL (sub_nonneg.mpr hs)]
  have hnorm : ‖exponentScale j‖ = 2*L := by
    simp only [exponentScale, norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg hL, L]
  have hterm : ‖exponentialTerm j s‖ = Real.exp ((-2*L)*s.re) := by
    simp only [exponentialTerm, norm_exp, exponentScale, mul_re, ofReal_re, ofReal_im,
      zero_mul, sub_zero, L]
  rw [norm_mul, norm_mul, hnorm, hterm]
  calc
    _ ≤ (2*L)*(2*L*Real.exp (-(L/3))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hA) (by positivity)) (by positivity)
    _ = 36*((L/3)^2*Real.exp (-(L/3))) := by ring
    _ ≤ _ := by linarith only [log_damping (L/3) (by positivity)]

private theorem norm_weight_sum (k : ℕ) :
    (∑ j ∈ Finset.range (k+1), ‖EtaMellin.binomialWeight k j‖) = (1:ℝ)/2 := by
  have h (j : ℕ) : ‖EtaMellin.binomialWeight k j‖ = (k.choose j:ℝ)/2^(k+1) := by
    simp only [EtaMellin.binomialWeight, norm_real, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (k.choose j)),
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  simp_rw [h]
  rw [← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat, pow_succ]
  field_simp [pow_ne_zero k (by norm_num : (2:ℝ) ≠ 0)]

private theorem secondReading_bound {s : ℂ} (hs : 1/3 ≤ 2*s.re) :
    ‖secondReading s‖ ≤ 2304 := by
  unfold secondReading
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _k ∈ Finset.range 128, (18:ℝ) := by
      refine Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans ?_
      calc
        _ ≤ ∑ j ∈ Finset.range (k+1), ‖EtaMellin.binomialWeight k j‖ * 36 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (term_second_bound j hs) (norm_nonneg _)
        _ = 18 := by rw [← Finset.sum_mul, norm_weight_sum]; norm_num
    _ = _ := by norm_num

theorem etaDiskApprox_deriv_variation {s : ℂ} (hs : s ∈ closedBall firstCenter firstRadius) :
    ‖deriv etaDiskApprox s - deriv etaDiskApprox firstCenter‖ ≤ 2304/4096 := by
  have hB (u : ℂ) (hu : u ∈ closedBall firstCenter firstRadius) :
      ‖deriv etaDiskDerivative u‖ ≤ 2304 := by
    rw [(etaDiskDerivative_hasDeriv u).deriv]
    have hR := (Complex.abs_re_le_norm (u-firstCenter)).trans (by
      simpa only [dist_eq_norm] using mem_closedBall.mp hu)
    change |u.re-1/4| ≤ (1:ℝ)/4096 at hR
    exact secondReading_bound (by linarith only [(abs_le.mp hR).1])
  have hC : firstCenter ∈ closedBall firstCenter firstRadius := mem_closedBall_self (by norm_num)
  have hd := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u _ => (etaDiskDerivative_hasDeriv u).differentiableAt)
    hB (convex_closedBall firstCenter firstRadius) hC hs
  simp only [deriv_etaDiskApprox]
  exact hd.trans (by
    have hdist := (mem_closedBall.mp hs)
    rw [dist_eq_norm] at hdist
    calc
      _ ≤ 2304*firstRadius := mul_le_mul_of_nonneg_left hdist (by norm_num)
      _ = _ := by norm_num [firstRadius])

def etaDiskDirection : ℂ := ⟨15/4, -1/4⟩

private theorem etaDiskDirection_norm : (15:ℝ)/4 ≤ ‖etaDiskDirection‖ :=
  (le_abs_self etaDiskDirection.re).trans (Complex.abs_re_le_norm _)

theorem eta_contour_inputs_of_finite_center
    (hval : ‖etaDiskApprox firstCenter‖ ≤ 3/10^6)
    (hslope : ‖deriv etaDiskApprox firstCenter - etaDiskDirection‖ ≤ 1/20) :
    etaDiskDirection ≠ 0 ∧
      ‖doubledEta firstCenter / etaDiskDirection‖ ≤ 1/10^6 ∧
      ∀ s ∈ closedBall firstCenter firstRadius,
        ‖1 - deriv doubledEta s / etaDiskDirection‖ ≤ 1/4 := by
  have ha := etaDiskDirection_norm
  have hap : 0 < ‖etaDiskDirection‖ := lt_of_lt_of_le (by norm_num) ha
  have ha0 : etaDiskDirection ≠ 0 := norm_ne_zero_iff.mp hap.ne'
  refine ⟨ha0, ?_, ?_⟩
  · have h := etaDiskApprox_error (s := firstCenter) (by norm_num)
    have hn := norm_add_le (doubledEta firstCenter - etaDiskApprox firstCenter) (etaDiskApprox firstCenter)
    rw [sub_add_cancel] at hn
    rw [norm_div]
    apply (div_le_iff₀ hap).mpr
    linarith only [hn,h,hval,ha]
  · intro s hs
    have h1 := etaDiskApprox_deriv_error hs
    have h2 := etaDiskApprox_deriv_variation hs
    have h := norm_add_le (deriv doubledEta s-deriv etaDiskApprox s)
      (deriv etaDiskApprox s-deriv etaDiskApprox firstCenter)
    rw [sub_add_sub_cancel] at h
    have h' := norm_add_le (deriv doubledEta s-deriv etaDiskApprox firstCenter)
      (deriv etaDiskApprox firstCenter-etaDiskDirection)
    rw [sub_add_sub_cancel] at h'
    rw [show (1:ℂ)-deriv doubledEta s/etaDiskDirection =
      (etaDiskDirection-deriv doubledEta s)/etaDiskDirection by field_simp [ha0],
      norm_div, norm_sub_rev]
    apply (div_le_iff₀ hap).mpr
    linarith only [h,h',h1,h2,hslope,ha]

theorem firstContour_read_of_finite_center
    (hsamples : MellinFixed.checkTableRange 576 1728 = true)
    (hval : ‖etaDiskApprox firstCenter‖ ≤ 3/10^6)
    (hslope : ‖deriv etaDiskApprox firstCenter - etaDiskDirection‖ ≤ 1/20) :
    ∃ ρ ∈ ball firstCenter firstRadius,
      nativeCross ρ = 0 ∧ deriv nativeCross ρ ≠ 0 ∧ riemannZeta (2*ρ) = 0 ∧
      (∀ s ∈ closedBall firstCenter firstRadius, nativeCross s = 0 ↔ s = ρ) ∧
      (∀ p : ℂ → ℂ, Differentiable ℂ p →
        weightedCircle firstCenter firstRadius nativeCross p = p ρ) := by
  obtain ⟨ha, hcenter, hdefect⟩ := eta_contour_inputs_of_finite_center hval hslope
  exact firstContour_read_of_checked_range_and_eta hsamples ha hcenter hdefect

#print axioms etaDiskApprox_deriv_variation
#print axioms eta_contour_inputs_of_finite_center
#print axioms firstContour_read_of_finite_center

end DottieOriented.NativeSpectrum
end
