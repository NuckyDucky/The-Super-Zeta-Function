import NativeDottieGapDisk
import NativeDottieMellinExpression
import Mathlib.Tactic.Abel

/-! Truncate the first-disk Mellin coefficients with a numerical error
proved in Lean, and put the finite integrals in real elementary form. -/
noncomputable section

namespace DottieOriented.NativeSpectrum

open Complex MeasureTheory Set
open scoped Interval

private theorem coefficient_left_tail (k : ℕ) {A : ℝ} (hA : A ≤ 0) :
    ‖∫ u in Iic A, centerCoefficientDensity k u‖ ≤ ((32:ℝ)/3)*4^k*Real.exp A := by
  have hi := (centerCoefficientDensity_integrable k).integrableOn (s := Iic A)
  have he : IntegrableOn Real.exp (Iic A) := by
    simpa only [one_mul] using integrableOn_exp_mul_Iic (a := 1) (by norm_num) A
  calc
    _ ≤ ∫ u in Iic A, ‖centerCoefficientDensity k u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Iic A, ((32:ℝ)/3)*4^k*Real.exp u :=
      setIntegral_mono_on hi.norm (he.const_mul _) measurableSet_Iic
        (fun _ hu => centerCoefficientDensity_negMajorant k ((mem_Iic.mp hu).trans hA))
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simpa only [one_mul, div_one] using integral_exp_mul_Iic (a := 1) (by norm_num) A

private theorem exp_increment {B u : ℝ} (hB : 0 ≤ B) (hu : B ≤ u) :
    Real.exp B + (u-B) ≤ Real.exp u := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u-B)) (Real.exp_pos B).le
  have hlin := mul_le_mul_of_nonneg_right (Real.one_le_exp hB) (sub_nonneg.mpr hu)
  rw [← Real.exp_add, show B+(u-B) = u by ring] at h
  nlinarith only [h, hlin]

private theorem coefficient_right_tail (k : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    ‖∫ u in Ioi B, centerCoefficientDensity k u‖ ≤
      ((512:ℝ)/9)*4^k*Real.exp (-Real.exp B/2) := by
  let c : ℝ := (256/9)*4^k*Real.exp ((B-Real.exp B)/2)
  have hi := (centerCoefficientDensity_integrable k).integrableOn (s := Ioi B)
  have he := integrableOn_exp_mul_Ioi (a := -1/2) (by norm_num) B
  calc
    _ ≤ ∫ u in Ioi B, ‖centerCoefficientDensity k u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u in Ioi B, c*Real.exp ((-1/2)*u) := by
      apply setIntegral_mono_on hi.norm (he.const_mul _) measurableSet_Ioi
      intro u hu
      have hBu := (mem_Ioi.mp hu).le
      refine (centerCoefficientDensity_posMajorant k (hB.trans hBu)).trans ?_
      dsimp [c]
      rw [mul_assoc ((256:ℝ)/9*4^k), ← Real.exp_add]
      gcongr
      linarith only [exp_increment hB hBu]
    _ = _ := by
      rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1/2:ℝ) < 0)]
      dsimp [c]
      rw [show (256/9:ℝ)*4^k*Real.exp ((B-Real.exp B)/2)*(-Real.exp ((-1/2)*B)/(-1/2)) =
        (512/9)*4^k*(Real.exp ((B-Real.exp B)/2)*Real.exp ((-1/2)*B)) by ring,
        ← Real.exp_add, show (B-Real.exp B)/2+(-1/2)*B = -Real.exp B/2 by ring]

/-- Tail bound for the actual native correction moment on any finite
interval with left endpoint at most zero and right endpoint at least zero. -/
theorem centerCoefficient_truncation (k : ℕ) {A B : ℝ} (hA : A ≤ 0) (hB : 0 ≤ B) :
    ‖centerCoefficient k - ∫ u in A..B, centerCoefficientDensity k u‖ ≤
      ((32:ℝ)/3)*4^k*Real.exp A + ((512:ℝ)/9)*4^k*Real.exp (-Real.exp B/2) := by
  have hi := centerCoefficientDensity_integrable k
  rw [centerCoefficient, ← intervalIntegral.integral_Iic_add_Ioi
    (b := B) hi.integrableOn hi.integrableOn,
    ← intervalIntegral.integral_Iic_sub_Iic (a := A) (b := B) hi.integrableOn hi.integrableOn]
  have hsum :
      ((∫ u in Iic B, centerCoefficientDensity k u) +
        (∫ u in Ioi B, centerCoefficientDensity k u)) -
        ((∫ u in Iic B, centerCoefficientDensity k u) -
          (∫ u in Iic A, centerCoefficientDensity k u)) =
      (∫ u in Iic A, centerCoefficientDensity k u) +
        (∫ u in Ioi B, centerCoefficientDensity k u) := by abel
  rw [hsum]
  exact (norm_add_le _ _).trans (add_le_add (coefficient_left_tail k hA) (coefficient_right_tail k hB))

theorem centerCoefficient_truncation_first {k : ℕ} (hk : k < 4) :
    ‖centerCoefficient k - ∫ u in (-32:ℝ)..5, centerCoefficientDensity k u‖ ≤ 1/10^11 := by
  have he : (271:ℝ)/100 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have heInv : Real.exp (-1) ≤ (100:ℝ)/271 := by
    calc
      _ = 1 / Real.exp 1 := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / ((271:ℝ)/100) := one_div_le_one_div_of_le (by norm_num) he
      _ = _ := by norm_num
  have hp (n : ℕ) : Real.exp (-(n:ℝ)) ≤ ((100:ℝ)/271)^n := by
    rw [← mul_neg_one, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le heInv n
  have h5 : (128:ℝ) ≤ Real.exp 5 := by
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 271/100) he 5
    rw [← Real.exp_nat_mul] at h
    norm_num at h
    linarith only [h]
  have hR : Real.exp (-Real.exp 5/2) ≤ ((100:ℝ)/271)^64 :=
    (Real.exp_le_exp.mpr (by linarith only [h5] : -Real.exp 5/2 ≤ -(64:ℝ))).trans (hp 64)
  have hL : Real.exp (-32) ≤ ((100:ℝ)/271)^32 := hp 32
  have hpow : (4:ℝ)^k ≤ 4^3 := pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    _ ≤ ((32:ℝ)/3)*4^k*Real.exp (-32) + ((512:ℝ)/9)*4^k*Real.exp (-Real.exp 5/2) :=
      centerCoefficient_truncation k (by norm_num) (by norm_num)
    _ ≤ ((32:ℝ)/3)*4^3*((100:ℝ)/271)^32 + ((512:ℝ)/9)*4^3*((100:ℝ)/271)^64 := by
      gcongr
    _ ≤ _ := by norm_num

private theorem sinh_times_exp_neg (x : ℝ) :
    2*Real.sinh x * Real.exp (-x) = 1-(Real.exp (-x))^2 := by
  rw [Real.sinh_eq, show 2*((Real.exp x-Real.exp (-x))/2)*Real.exp (-x) =
    Real.exp x*Real.exp (-x)-(Real.exp (-x))^2 by ring,
    ← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem finiteLogGap_eq (x : ℝ) :
    finiteLogGap x =
      Real.log ((3+4*(Real.sinh x^2+x^2)-4*x*Real.sinh x) /
        (3+4*(Real.sinh x^2+x^2)+4*x*Real.sinh x)) := by
  unfold finiteLogGap
  dsimp only
  rw [← sinh_times_exp_neg,
    show (2*Real.sinh x*Real.exp (-x))^2+(3+4*x^2)*(Real.exp (-x))^2 -
        2*x*Real.exp (-x)*(2*Real.sinh x*Real.exp (-x)) =
        (3+4*(Real.sinh x^2+x^2)-4*x*Real.sinh x)*(Real.exp (-x))^2 by ring,
    show (2*Real.sinh x*Real.exp (-x))^2+(3+4*x^2)*(Real.exp (-x))^2 +
        2*x*Real.exp (-x)*(2*Real.sinh x*Real.exp (-x)) =
        (3+4*(Real.sinh x^2+x^2)+4*x*Real.sinh x)*(Real.exp (-x))^2 by ring,
    mul_div_mul_right _ _ (pow_ne_zero _ (Real.exp_pos _).ne')]

def component (imaginary : Bool) (z : ℂ) : ℝ :=
  if imaginary then z.im else z.re

theorem finiteCoefficientDensity_eq (imaginary : Bool) (k : ℕ) (u : ℝ) :
    component imaginary (centerCoefficientDensity k u) = finiteCoefficientDensity imaginary k u := by
  rw [centerCoefficientDensity_expLog, finiteCoefficientDensity, finiteLogGap_eq]
  set z := -(2*firstCenter)*(u:ℂ)
  have he : z.re = -u/2 := by
    norm_num [z, firstCenter, Complex.mul_re, Complex.add_re]
    ring
  have hi : z.im = -(7067363/500000*u) := by
    norm_num [z, firstCenter, Complex.mul_im, Complex.add_im]
  have hr : ((-2:ℂ)*(u:ℂ))^k/(k.factorial:ℂ) =
      (((-2*u)^k/(k.factorial:ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [hr]
  cases imaginary
  · simp only [component, Bool.false_eq_true, if_false, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, Complex.exp_re, he, hi,
      Real.cos_neg]
    ring
  · simp only [component, if_true, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_mul, zero_add, add_zero, Complex.exp_im, he, hi, Real.sin_neg]
    ring

theorem finiteCoefficient_integral_error (imaginary : Bool) {k : ℕ} (hk : k < 4) :
    |component imaginary (centerCoefficient k) - ∫ u in (-32:ℝ)..5, finiteCoefficientDensity imaginary k u|
      ≤ 1/10^11 := by
  have h := centerCoefficient_truncation_first hk
  rw [← funext (finiteCoefficientDensity_eq imaginary k), intervalIntegral.integral_of_le (by norm_num)]
  rw [intervalIntegral.integral_of_le (by norm_num)] at h
  have hint := (centerCoefficientDensity_integrable k).integrableOn (s := Ioc (-32:ℝ) 5)
  cases imaginary
  · simp only [component, Bool.false_eq_true, if_false]
    have he : (∫ u in Ioc (-32:ℝ) 5, (centerCoefficientDensity k u).re) =
        (∫ u in Ioc (-32:ℝ) 5, centerCoefficientDensity k u).re := integral_re hint
    rw [he, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans h
  · simp only [component, if_true]
    have he : (∫ u in Ioc (-32:ℝ) 5, (centerCoefficientDensity k u).im) =
        (∫ u in Ioc (-32:ℝ) 5, centerCoefficientDensity k u).im := integral_im hint
    rw [he, ← Complex.sub_im]
    exact (Complex.abs_im_le_norm _).trans h

/-- These eight real integral inequalities imply exactly the four
complex coefficient premises used by the first-disk proof. -/
theorem centerCoefficients_of_finite
    (hreal : finiteCoefficient false 0 ≤ -11565/10^10)
    (himag : finiteCoefficient true 0 ≤ -2740/10^10)
    (hrest : ∀ k : ℕ, 0 < k → k < 4 →
      |finiteCoefficient false k| ≤ 271/10^8 ∧
      |finiteCoefficient true k| ≤ 405/10^8) :
    (1188:ℝ)/10^9 ≤ ‖centerCoefficient 0‖ ∧
      ∀ k : ℕ, 0 < k → k < 4 → ‖centerCoefficient k‖ ≤ (5:ℝ)/10^6 := by
  have herr (b : Bool) (k : ℕ) (hk : k < 4) :
      |component b (centerCoefficient k)-finiteCoefficient b k| ≤ 1/10^11 :=
    finiteCoefficient_integral_error b hk
  constructor
  · have er := (abs_le.mp (herr false 0 (by decide))).2
    have ei := (abs_le.mp (herr true 0 (by decide))).2
    simp only [component, Bool.false_eq_true, if_false, if_true] at er ei
    have hr : (115649:ℝ)/10^11 ≤ -(centerCoefficient 0).re := by linarith only [er, hreal]
    have hi : (27399:ℝ)/10^11 ≤ -(centerCoefficient 0).im := by linarith only [ei, himag]
    apply (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [pow_le_pow_left₀ (by norm_num) hr 2, pow_le_pow_left₀ (by norm_num) hi 2]
  · intro k hk₀ hk₄
    obtain ⟨hr, hi⟩ := hrest k hk₀ hk₄
    have habs (b : Bool) :
        |component b (centerCoefficient k)| ≤ |finiteCoefficient b k| + 1/10^11 := by
      calc
        _ = |finiteCoefficient b k + (component b (centerCoefficient k)-finiteCoefficient b k)| := by
          congr 1
          ring
        _ ≤ _ := (abs_add_le _ _).trans (add_le_add_left (herr b k hk₄) _)
    have hr' : |(centerCoefficient k).re| ≤ (271001:ℝ)/10^11 := by
      have h := habs false
      simp only [component, Bool.false_eq_true, if_false] at h
      linarith only [h, hr]
    have hi' : |(centerCoefficient k).im| ≤ (405001:ℝ)/10^11 := by
      have h := habs true
      simp only [component, if_true] at h
      linarith only [h, hi]
    apply (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hr₂ := pow_le_pow_left₀ (abs_nonneg _) hr' 2
    have hi₂ := pow_le_pow_left₀ (abs_nonneg _) hi' 2
    rw [sq_abs] at hr₂ hi₂
    nlinarith only [hr₂, hi₂]

theorem firstDisk_correctionGap_lower_of_finite
    (hreal : finiteCoefficient false 0 ≤ -11565/10^10)
    (himag : finiteCoefficient true 0 ≤ -2740/10^10)
    (hrest : ∀ k : ℕ, 0 < k → k < 4 →
      |finiteCoefficient false k| ≤ 271/10^8 ∧ |finiteCoefficient true k| ≤ 405/10^8)
    {s : ℂ} (hs : s ∈ Metric.closedBall firstCenter firstRadius) :
    (11600:ℝ) < ‖correctionGap s‖ := by
  obtain ⟨hzero, hhigh⟩ := centerCoefficients_of_finite hreal himag hrest
  exact firstDisk_correctionGap_lower hzero hhigh hs

#print axioms centerCoefficient_truncation
#print axioms centerCoefficient_truncation_first
#print axioms finiteLogGap_eq
#print axioms finiteCoefficientDensity_eq
#print axioms finiteCoefficient_integral_error
#print axioms centerCoefficients_of_finite
#print axioms firstDisk_correctionGap_lower_of_finite

end DottieOriented.NativeSpectrum
end
