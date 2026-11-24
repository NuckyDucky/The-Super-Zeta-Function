import NativeDottieContour
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Jacobian

/-! Enclose the normalized correction gap on the whole disk from four
integrals at its center. The Taylor remainder is bounded in Lean. -/
noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex MeasureTheory Set Filter Metric
open scoped Topology BigOperators

private def logRay (b : Bool) (s : ℂ) (u : ℝ) : ℂ :=
  Complex.exp (-(2*s)*(u:ℂ)) * kernel b (Real.exp u)

private def gapRay (s : ℂ) (u : ℝ) : ℂ := logRay false s u - logRay true s u

/-- The single logarithm used by the quadrature is the difference of the
two determinant logarithms, with their common reference removed. -/
theorem logGap_on_ray (x : ℝ) :
    kernel false x - kernel true x =
      (Real.log ((3+4*(Real.sinh x^2+x^2)-4*x*Real.sinh x) /
        (3+4*(Real.sinh x^2+x^2)+4*x*Real.sinh x)) : ℂ) := by
  unfold kernel realKernel
  rw [← Complex.ofReal_sub, ← Real.log_div
    (div_ne_zero (determinant_ray_pos false x).ne' (reference_ray_pos x).ne')
    (div_ne_zero (determinant_ray_pos true x).ne' (reference_ray_pos x).ne')]
  have hminus : (3:ℝ)*determinantRay false x = 3+4*(Real.sinh x^2+x^2)-4*x*Real.sinh x := by
    norm_num [determinantRay, referenceRay, rayOffset, sineSign]
    ring
  have hplus : (3:ℝ)*determinantRay true x = 3+4*(Real.sinh x^2+x^2)+4*x*Real.sinh x := by
    norm_num [determinantRay, referenceRay, rayOffset, sineSign]
    ring
  rw [← hminus, ← hplus, mul_div_mul_left _ _ (by norm_num : (3:ℝ) ≠ 0)]
  congr 2
  field_simp [(reference_ray_pos x).ne', (determinant_ray_pos true x).ne']

def normalizedGap (s : ℂ) : ℂ := ∫ u, gapRay s u

def centerCoefficient (k : ℕ) : ℂ :=
  ∫ u : ℝ, ((-2:ℂ)*(u:ℂ))^k/(k.factorial:ℂ) * gapRay firstCenter u

private def prefactor (s : ℂ) : ℂ :=
  2*s*Complex.sin ((Real.pi:ℂ)*s)/(Real.pi:ℂ)

private theorem logRay_mellin (b : Bool) (s : ℂ) :
    mellin (kernel b) (-(2*s)) = ∫ u, logRay b s u := by
  unfold mellin
  rw [← Real.range_exp, ← Set.image_univ,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun u _ => (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn,
    setIntegral_univ]
  apply integral_congr_ae
  filter_upwards with u
  rw [abs_of_pos (Real.exp_pos _), Complex.real_smul, Complex.ofReal_exp, smul_eq_mul, ← mul_assoc]
  have he : Complex.exp (u:ℂ) * (Complex.exp (u:ℂ))^(-(2*s)-1) =
      (Complex.exp (u:ℂ))^(1+(-(2*s)-1)) := by
    rw [cpow_add _ _ (Complex.exp_ne_zero _), cpow_one]
  rw [he]
  rw [show (1:ℂ)+(-(2*s)-1) = -(2*s) by ring, cpow_def_of_ne_zero (Complex.exp_ne_zero _)]
  rw [Complex.log_exp (by simpa using Real.pi_pos) (by simpa using Real.pi_pos.le)]
  rw [logRay, mul_comm (u:ℂ) (-(2*s))]

private theorem logRay_continuous (b : Bool) (s : ℂ) : Continuous (logRay b s) :=
  (continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
    ((kernel_continuous b).comp Real.continuous_exp)

private theorem seed_bound (b : Bool) (u : ℝ) :
    ‖logRay b firstCenter u‖ ≤ 16 * Real.exp (-|u|) := by
  have hex : ‖Complex.exp (-(2*firstCenter)*(u:ℂ))‖ = Real.exp (-u/2) := by
    rw [Complex.norm_exp]
    congr 1
    norm_num [firstCenter, Complex.mul_re, Complex.add_re]
    ring
  rw [logRay, norm_mul, hex]
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
    have ht := kernel_tail_bound b (Real.exp_pos u).le
    have he : Real.exp (-Real.exp u / 2) ≤ Real.exp (-u/2) := by
      apply Real.exp_le_exp.mpr
      linarith [Real.add_one_le_exp u]
    calc
      _ ≤ Real.exp (-u/2)*((128/9)*Real.exp (-Real.exp u/2)) :=
        mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
      _ ≤ (128/9)*(Real.exp (-u/2)*Real.exp (-u/2)) := by
        rw [← mul_left_comm]
        gcongr
      _ ≤ _ := by
        rw [← Real.exp_add, show -u/2 + -u/2 = -u by ring]
        exact mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  · have h := le_of_not_ge hu
    rw [abs_of_nonpos h, neg_neg]
    have ht := kernel_small_bound b (Real.exp_pos u).le (Real.exp_le_one_iff.mpr h)
    calc
      _ ≤ Real.exp (-u/2)*((16/3)*(Real.exp u)^2) :=
        mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
      _ = (16/3)*Real.exp (3*u/2) := by
        rw [pow_two, mul_left_comm, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ 16*Real.exp u := by
        exact mul_le_mul (by norm_num) (Real.exp_le_exp.mpr (by linarith))
          (Real.exp_pos _).le (by norm_num)

private theorem gapSeed_bound (u : ℝ) :
    ‖gapRay firstCenter u‖ ≤ 32 * Real.exp (-|u|) := by
  exact (norm_sub_le _ _).trans (by linarith [seed_bound false u, seed_bound true u])

private def envelope (u : ℝ) : ℝ := Real.exp (-|u|/4)

set_option maxHeartbeats 800000 in
private theorem envelope_int : Integrable envelope := by
  have hP : IntegrableOn envelope (Ioi (0:ℝ)) := by
    refine (integrableOn_exp_mul_Ioi (a := -1/4) (by norm_num) 0).congr_fun ?_ measurableSet_Ioi
    intro u hu
    unfold envelope
    rw [abs_of_nonneg (mem_Ioi.mp hu).le]
    exact congrArg Real.exp (by ring)
  have hN : IntegrableOn envelope (Iic (0:ℝ)) := by
    refine (integrableOn_exp_mul_Iic (a := 1/4) (by norm_num) 0).congr_fun ?_ measurableSet_Iic
    intro u hu
    unfold envelope
    rw [abs_of_nonpos (mem_Iic.mp hu)]
    exact congrArg Real.exp (by ring)
  rw [← integrableOn_univ, ← Set.union_compl_self (Ioi (0:ℝ)), compl_Ioi]
  exact hP.union hN

private theorem envelope_total : (∫ u, envelope u) = 8 := by
  have he : envelope = fun u => Real.exp ((-1/4:ℝ)*|u|) := by
    funext u
    unfold envelope
    exact congrArg Real.exp (by ring)
  have h := integral_comp_abs (f := fun u => Real.exp ((-1/4:ℝ)*u))
  rw [integral_exp_mul_Ioi (by norm_num : (-1/4:ℝ) < 0)] at h
  rw [he]
  norm_num at h ⊢
  exact h

private theorem logRay_shift (b : Bool) (s : ℂ) (u : ℝ) :
    logRay b s u = Complex.exp ((s-firstCenter)*((-2:ℂ)*(u:ℂ))) * logRay b firstCenter u := by
  simp only [logRay, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

private theorem gapRay_shift (s : ℂ) (u : ℝ) :
    gapRay s u = Complex.exp ((s-firstCenter)*((-2:ℂ)*(u:ℂ))) * gapRay firstCenter u := by
  simp only [gapRay, logRay_shift false s u, logRay_shift true s u, mul_sub]

private theorem exponent_bound {h : ℂ} (hh : ‖h‖ ≤ firstRadius) (u : ℝ) :
    ‖h*((-2:ℂ)*(u:ℂ))‖ ≤ (2*firstRadius)*|u| := by
  rw [norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ firstRadius * (2*|u|) := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by ring

private theorem exponent_quarter {h : ℂ} (hh : ‖h‖ ≤ firstRadius) (u : ℝ) :
    ‖h*((-2:ℂ)*(u:ℂ))‖ ≤ |u|/4 :=
  (exponent_bound hh u).trans (by
    change 2*(1/4096:ℝ)*|u| ≤ |u|/4
    linarith only [abs_nonneg u])

private theorem logRay_int (b : Bool) {s : ℂ} (hs : ‖s-firstCenter‖ ≤ firstRadius) :
    Integrable (logRay b s) := by
  apply (envelope_int.const_mul (16:ℝ)).mono' (logRay_continuous b s).aestronglyMeasurable
  filter_upwards with u
  rw [logRay_shift, norm_mul]
  calc
    _ ≤ Real.exp (|u|/4) * (16 * Real.exp (-|u|)) :=
      mul_le_mul
        ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr (exponent_quarter hs u)))
        (seed_bound b u) (norm_nonneg _) (Real.exp_pos _).le
    _ = 16*Real.exp (-(3/4)*|u|) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    _ ≤ (16:ℝ)*envelope u := by
      unfold envelope
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [abs_nonneg u])) (by norm_num)

private theorem coefficient_int (k : ℕ) :
    Integrable (fun u : ℝ => ((-2:ℂ)*(u:ℂ))^k/(k.factorial:ℂ)*gapRay firstCenter u) := by
  have hcont : Continuous (fun u => gapRay firstCenter u) :=
    (logRay_continuous false firstCenter).sub (logRay_continuous true firstCenter)
  have hp : Continuous (fun u : ℝ => ((-2:ℂ)*(u:ℂ))^k/(k.factorial:ℂ)) := by fun_prop
  apply (envelope_int.const_mul ((4:ℝ)^k*32)).mono' (hp.mul hcont).aestronglyMeasurable
  filter_upwards with u
  have hp := Real.pow_div_factorial_le_exp (|u|/2) (by positivity) k
  have hh : (2*|u|)^k / (k.factorial:ℝ) ≤ 4^k * Real.exp (|u|/2) := by
    calc
      _ = 4^k * ((|u|/2)^k/(k.factorial:ℝ)) := by
        rw [← mul_div_assoc, ← mul_pow]
        rw [show (4:ℝ)*(|u|/2) = 2*|u| by ring]
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  rw [norm_mul, norm_div, norm_pow, norm_mul, norm_neg, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
  calc
    _ ≤ (4^k*Real.exp (|u|/2)) * (32*Real.exp (-|u|)) :=
      mul_le_mul hh (gapSeed_bound _) (norm_nonneg _) (by positivity)
    _ = 4^k*32*Real.exp (-|u|/2) := by
      rw [show (4:ℝ)^k*Real.exp (|u|/2)*(32*Real.exp (-|u|)) =
        4^k*32*(Real.exp (|u|/2)*Real.exp (-|u|)) by ring, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 4^k*32*envelope u := by
      unfold envelope
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith [abs_nonneg u])) (by positivity)

private theorem gap_factor {s : ℂ} (hs : s ∈ closedBall firstCenter firstRadius) :
    correctionGap s = prefactor s * normalizedGap s := by
  have hr : ‖s-firstCenter‖ ≤ firstRadius := by simpa only [mem_closedBall, dist_eq_norm] using hs
  have hRe : s.re < 1 := by
    have h := (firstDisk_in_strip hs).2
    linarith
  change correction false s - correction true s =
    prefactor s * (∫ u, logRay false s u - logRay true s u)
  rw [correction_integral false hRe, correction_integral true hRe, logRay_mellin, logRay_mellin]
  rw [integral_sub (logRay_int false hr) (logRay_int true hr), mul_sub]
  rfl

private def polynomial (h : ℂ) : ℂ := ∑ k ∈ Finset.range 4, h^k * centerCoefficient k

private def polynomialRay (h : ℂ) (u : ℝ) : ℂ :=
  ∑ k ∈ Finset.range 4, h^k * (((-2:ℂ)*(u:ℂ))^k/(k.factorial:ℂ)*gapRay firstCenter u)

private theorem polyInt (h : ℂ) : Integrable (polynomialRay h) := by
  unfold polynomialRay
  exact integrable_finset_sum _ fun k _ => (coefficient_int k).const_mul _

private theorem polyIntegral (h : ℂ) : (∫ u, polynomialRay h u) = polynomial h := by
  unfold polynomialRay polynomial centerCoefficient
  rw [integral_finset_sum _ (fun k _ => (coefficient_int k).const_mul (h^k))]
  simp_rw [integral_const_mul]

private theorem remainder_bound {s : ℂ} (hs : ‖s-firstCenter‖ ≤ firstRadius) (u : ℝ) :
    ‖gapRay s u - polynomialRay (s-firstCenter) u‖ ≤
      (12288*(2*firstRadius)^4)*envelope u := by
  let h := s-firstCenter
  let z := h*((-2:ℂ)*(u:ℂ))
  have poly : polynomialRay h u =
      (∑ k ∈ Finset.range 4, z^k/(k.factorial:ℂ))*gapRay firstCenter u := by
    rw [polynomialRay, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp only [z, mul_pow]
    ring
  have hq : ‖z‖ ≤ |u|/4 := exponent_quarter hs u
  have hnorm : ‖z‖ ≤ (2*firstRadius)*|u| := exponent_bound hs u
  have hp : |u|^4 ≤ 384*Real.exp (|u|/2) := by
    have he := Real.pow_div_factorial_le_exp (|u|/2) (by positivity) 4
    norm_num [div_pow, Nat.factorial] at he
    linarith only [he]
  rw [show s-firstCenter = h from rfl, poly, gapRay_shift, ← sub_mul, norm_mul]
  calc
    _ ≤ (‖z‖^4*Real.exp ‖z‖)*(32*Real.exp (-|u|)) :=
      mul_le_mul (Complex.norm_exp_sub_sum_le_norm_mul_exp z 4) (gapSeed_bound _)
        (norm_nonneg _) (by positivity)
    _ ≤ ((2*firstRadius)^4*|u|^4*Real.exp (|u|/4))*(32*Real.exp (-|u|)) := by
      rw [← mul_pow]
      gcongr
    _ ≤ ((2*firstRadius)^4*(384*Real.exp (|u|/2))*Real.exp (|u|/4))*(32*Real.exp (-|u|)) := by
      gcongr
    _ = _ := by
      unfold envelope
      rw [show (2*firstRadius)^4*(384*Real.exp (|u|/2))*Real.exp (|u|/4)*(32*Real.exp (-|u|))
        = (12288*(2*firstRadius)^4)*(Real.exp (|u|/2)*Real.exp (|u|/4)*Real.exp (-|u|)) by ring,
        ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

theorem firstGap_taylor {s : ℂ} (hs : s ∈ closedBall firstCenter firstRadius) :
    ‖normalizedGap s - polynomial (s-firstCenter)‖ ≤ 98304*(2*firstRadius)^4 := by
  have hr : ‖s-firstCenter‖ ≤ firstRadius := by simpa only [mem_closedBall, dist_eq_norm] using hs
  have hi : Integrable (gapRay s) := (logRay_int false hr).sub (logRay_int true hr)
  rw [normalizedGap, ← polyIntegral, ← integral_sub hi (polyInt _)]
  calc
    _ ≤ ∫ u, ‖gapRay s u - polynomialRay (s-firstCenter) u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u, (12288*(2*firstRadius)^4)*envelope u :=
      integral_mono (hi.sub (polyInt _)).norm (envelope_int.const_mul _)
        (remainder_bound hr)
    _ = _ := by rw [integral_const_mul, envelope_total]; ring

theorem normalized_gap_on_first_disk
    (hzero : (1188:ℝ)/10^9 ≤ ‖centerCoefficient 0‖)
    (hhigh : ∀ k : ℕ, 0 < k → k < 4 → ‖centerCoefficient k‖ ≤ (5:ℝ)/10^6)
    {s : ℂ} (hs : s ∈ closedBall firstCenter firstRadius) :
    (118:ℝ)/10^8 < ‖normalizedGap s‖ := by
  let h := s-firstCenter
  have hr : ‖h‖ ≤ firstRadius := by simpa only [h, mem_closedBall, dist_eq_norm] using hs
  have hsum : polynomial h = centerCoefficient 0 +
      (h * centerCoefficient 1 + (h^2 * centerCoefficient 2 + h^3 * centerCoefficient 3)) := by
    simp only [polynomial, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, pow_zero, one_mul, pow_one]
    ring
  have hk (k : ℕ) (hk₀ : 0 < k) (hk₄ : k < 4) :
      ‖h^k * centerCoefficient k‖ ≤ firstRadius^k*((5:ℝ)/10^6) := by
    rw [norm_mul, norm_pow]
    gcongr
    exact hhigh k hk₀ hk₄
  have hp : ‖polynomial h - centerCoefficient 0‖ ≤
      (firstRadius + firstRadius^2 + firstRadius^3)*((5:ℝ)/10^6) := by
    rw [hsum, add_sub_cancel_left]
    apply (norm_add_le ..).trans
    have h1 := hk 1 (by decide) (by decide)
    have h2 := hk 2 (by decide) (by decide)
    have h3 := hk 3 (by decide) (by decide)
    simp only [pow_one] at h1
    linarith only [h1,h2,h3,norm_add_le (h^2*centerCoefficient 2) (h^3*centerCoefficient 3)]
  have ht := firstGap_taylor hs
  have hh := norm_sub_le (normalizedGap s-polynomial h) (centerCoefficient 0-polynomial h)
  rw [sub_sub_sub_cancel_right, norm_sub_rev (centerCoefficient 0)] at hh
  have hn := norm_sub_norm_le (centerCoefficient 0) (normalizedGap s)
  rw [norm_sub_rev] at hn
  norm_num [firstRadius] at hp ht
  linarith only [hzero, hp, ht, hh, hn]

theorem gap_ne_zero_from_center_coefficients
    (hzero : (1188:ℝ)/10^9 ≤ ‖centerCoefficient 0‖)
    (hhigh : ∀ k : ℕ, 0 < k → k < 4 → ‖centerCoefficient k‖ ≤ (5:ℝ)/10^6)
    {s : ℂ} (hs : s ∈ closedBall firstCenter firstRadius) :
    correctionGap s ≠ 0 := by
  have hnorm := normalized_gap_on_first_disk hzero hhigh hs
  have hm : normalizedGap s ≠ 0 := by intro he; norm_num [he] at hnorm
  have him : 0 < s.im := by
    have h := (Complex.abs_im_le_norm (s-firstCenter)).trans
      (by simpa only [mem_closedBall, dist_eq_norm] using hs)
    change |s.im-7067363/1000000| ≤ firstRadius at h
    have h := (abs_le.mp h).1
    norm_num [firstRadius] at h
    linarith
  have hsin : Complex.sin ((Real.pi:ℂ)*s) ≠ 0 := by
    intro he
    obtain ⟨k,hk⟩ := Complex.sin_eq_zero_iff.mp he
    have hi := congrArg Complex.im hk
    simp [Complex.mul_im, Real.pi_ne_zero, him.ne'] at hi
  rw [gap_factor hs]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    (by intro he; simp [he] at him)) hsin) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hm

def firstContourPoint : ℂ := firstCenter +
  weightedCircle firstCenter firstRadius nativeCross (fun s => s-firstCenter)

/-- Read the first zero from the contour using only central Mellin data to
establish the gap. The cross-product residual and derivative bounds give the
simple-root certificate used by the weighted argument. -/
theorem firstContour_taylor_certificate
    (hzero : (1188:ℝ)/10^9 ≤ ‖centerCoefficient 0‖)
    (hhigh : ∀ k : ℕ, 0 < k → k < 4 → ‖centerCoefficient k‖ ≤ (5:ℝ)/10^6)
    (hcenter : ‖nativeCross firstCenter / firstDirection‖ ≤ 1/10^6)
    (hdefect : ∀ s ∈ closedBall firstCenter firstRadius,
      ‖1 - deriv nativeCross s / firstDirection‖ ≤ 1/4) :
    (∀ s ∈ closedBall firstCenter firstRadius, (118:ℝ)/10^8 < ‖normalizedGap s‖) ∧
    weightedCircle firstCenter firstRadius nativeCross (fun _ => 1) = 1 ∧
    firstContourPoint ∈ ball firstCenter firstRadius ∧ nativeCross firstContourPoint = 0 ∧
    deriv nativeCross firstContourPoint ≠ 0 ∧ riemannZeta (2*firstContourPoint) = 0 ∧
    (∀ s ∈ closedBall firstCenter firstRadius, nativeCross s = 0 → s = firstContourPoint) := by
  obtain ⟨ρ,hρ,hC,hder,hζ,hunique,hcount,hpoint⟩ := firstContour_read
    (fun _ hs => gap_ne_zero_from_center_coefficients hzero hhigh hs) hcenter hdefect
  have he : firstContourPoint = ρ := hpoint
  rw [he]
  exact ⟨fun _ hs => normalized_gap_on_first_disk hzero hhigh hs, hcount, hρ, hC, hder, hζ, hunique⟩

#print axioms logGap_on_ray
#print axioms firstGap_taylor
#print axioms normalized_gap_on_first_disk
#print axioms gap_ne_zero_from_center_coefficients
#print axioms firstContour_taylor_certificate
#check firstContour_taylor_certificate

end DottieOriented.NativeSpectrum
end
