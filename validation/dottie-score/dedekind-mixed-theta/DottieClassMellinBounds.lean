import DottieCompletedProductSign
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace FieldTarget

open Complex MeasureTheory Set SuperZeta.StirlingCorrection

noncomputable section

/-- After the substitution `t = exp v`, this is the folded Mellin weight
with respect to `dt`. -/
def classMellinWeight (w : ℂ) (v : ℝ) : ℂ :=
  (Complex.exp ((w - 1) * (v : ℂ)) + Complex.exp (-w * (v : ℂ))) / 2

private theorem classMellinWeight_re (w : ℂ) (v : ℝ) :
    (classMellinWeight w v).re =
      (Real.exp ((w.re - 1) * v) + Real.exp (-w.re * v)) / 2 *
        Real.cos (w.im * v) := by
  simp [classMellinWeight, Complex.exp_re, Complex.mul_re,
    Complex.mul_im, Real.cos_neg, neg_mul]
  ring

private theorem classMellinWeight_im (w : ℂ) (v : ℝ) :
    (classMellinWeight w v).im =
      (Real.exp ((w.re - 1) * v) - Real.exp (-w.re * v)) / 2 *
        Real.sin (w.im * v) := by
  simp [classMellinWeight, Complex.exp_im, Complex.mul_re,
    Complex.mul_im, Real.sin_neg, neg_mul]
  ring

theorem classMellinWeight_bounds {w : ℂ} {v : ℝ} (hv : 0 ≤ v)
    (hhalf : 1 / 2 ≤ w.re) (hone : w.re ≤ 1) :
    ‖classMellinWeight w v‖ ≤ 1 ∧
      Real.exp (-v / 2) - w.im ^ 2 * v ^ 2 / 2 ≤ (classMellinWeight w v).re ∧
      |(classMellinWeight w v).im| ≤ |w.im| * (w.re - 1 / 2) * v ^ 2 := by
  let x := w.re - 1 / 2
  let a := Real.exp ((w.re - 1) * v)
  let b := Real.exp (-w.re * v)
  let m := (a + b) / 2
  have hx : 0 ≤ x := sub_nonneg.mpr hhalf
  have ha : a ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hv)
  have hb : b ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hv)
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have hb0 : 0 ≤ b := (Real.exp_pos _).le
  have hm0 : 0 ≤ m := by dsimp [m]; linarith
  have hm1 : m ≤ 1 := by dsimp [m]; linarith
  have hml : Real.exp (-v / 2) ≤ m := by
    have hm : m = Real.exp (-v / 2) * Real.cosh (x * v) := by
      dsimp [m, a, b, x]
      rw [Real.cosh_eq]
      rw [show (w.re - 1) * v = -v / 2 + (w.re - 1 / 2) * v by ring,
        show -w.re * v = -v / 2 + -((w.re - 1 / 2) * v) by ring,
        Real.exp_add, Real.exp_add]
      ring
    rw [hm]
    exact le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_cosh _)
  have hab : b = a * Real.exp (-(2 * x * v)) := by
    dsimp [a, b, x]
    rw [← Real.exp_add]
    congr 1
    ring
  have hdiff : 0 ≤ a - b ∧ a - b ≤ 2 * x * v := by
    have hd : 0 ≤ 2 * x * v := by positivity
    have he : Real.exp (-(2 * x * v)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hne : 0 ≤ 1 - Real.exp (-(2 * x * v)) := sub_nonneg.mpr he
    have hlow := Real.add_one_le_exp (-(2 * x * v))
    constructor
    · rw [hab, ← mul_one_sub]
      positivity
    · rw [hab, ← mul_one_sub]
      exact (mul_le_of_le_one_left hne ha).trans (by linarith only [hlow])
  refine ⟨?_, ?_, ?_⟩
  · rw [classMellinWeight, norm_div]
    have hn := norm_add_le (Complex.exp ((w - 1) * (v : ℂ))) (Complex.exp (-w * (v : ℂ)))
    simp only [Complex.norm_exp, Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hn
    have hn' : ‖Complex.exp ((w - 1) * (v : ℂ)) + Complex.exp (-w * (v : ℂ))‖ ≤ a + b := hn
    rw [show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact (div_le_iff₀ (by norm_num)).2 (by linarith only [ha, hb, hn'])
  · rw [classMellinWeight_re]
    change _ ≤ m * Real.cos (w.im * v)
    have hcos := mul_le_mul_of_nonneg_left (Real.one_sub_sq_div_two_le_cos (x := w.im * v)) hm0
    have his := mul_le_mul_of_nonneg_right hm1 (show 0 ≤ (w.im * v) ^ 2 / 2 by positivity)
    nlinarith only [hcos, his, hml]
  · rw [classMellinWeight_im]
    change |(a - b) / 2 * Real.sin (w.im * v)| ≤ |w.im| * x * v ^ 2
    have hnonneg : 0 ≤ (a - b) / 2 := by linarith only [hdiff.1]
    have hsin := Real.abs_sin_le_abs (x := w.im * v)
    rw [abs_mul, abs_of_nonneg hv] at hsin
    rw [abs_mul, abs_of_nonneg hnonneg]
    calc
      _ ≤ (x * v) * (|w.im| * v) :=
        mul_le_mul (by linarith only [hdiff.2]) hsin (abs_nonneg _) (mul_nonneg hx hv)
      _ = _ := by ring

theorem classMellin_log_sq_le {t : ℝ} (ht : 0 ≤ t) :
    (Real.log (1 + t)) ^ 2 ≤ (5 / 7) * t := by
  let v := Real.log (1 + t)
  have hv : 0 ≤ v := Real.log_nonneg (by linarith only [ht])
  have he := Real.sum_le_exp_of_nonneg hv 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at he
  have hsquare := mul_nonneg (sq_nonneg (v - 3 / 2)) (show 0 ≤ v + 3 by linarith)
  have hcubic : (27 / 4) * v - 27 / 4 ≤ v ^ 3 := by nlinarith only [hsquare]
  have hquad : 0 ≤ 23 / 32 - (99 / 160) * v + v ^ 2 / 6 := by
    nlinarith only [sq_nonneg (v - 297 / 160)]
  have hpoly : 0 ≤ 1 - 9 / 10 * v + v ^ 2 / 6 + v ^ 3 / 24 := by
    linarith only [hcubic, hquad]
  have hnonneg := mul_nonneg hv hpoly
  have hExp : Real.exp v = 1 + t := Real.exp_log (by linarith only [ht])
  rw [hExp] at he
  change v ^ 2 ≤ _
  nlinarith only [he, hnonneg]

private theorem exp_rate_zeroth {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-r * t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, Real.exp (-r * t)) = 1 / r := by
  simp only [neg_mul, one_div]
  constructor
  · exact (integrableOn_Ioi_comp_mul_left_iff (fun t ↦ Real.exp (-t)) 0 hr).2 (by
      rw [mul_zero]
      exact integrableOn_exp_neg_Ioi 0)
  · rw [integral_comp_mul_left_Ioi (fun t ↦ Real.exp (-t)) 0 hr, mul_zero,
      integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one]

private theorem exp_rate_first {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ ↦ t * Real.exp (-r * t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, t * Real.exp (-r * t)) = 1 / r ^ 2 := by
  constructor
  · simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (by norm_num) (by norm_num) hr
  · have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1) (by norm_num)
      (by norm_num) hr
    have hGamma : Real.Gamma (1 + 1 : ℝ) = 1 := by
      simpa using Real.Gamma_nat_eq_factorial 1
    simp only [Real.rpow_one, div_one, hGamma, mul_one] at h
    rw [show -(1 + 1 : ℝ) = -2 by norm_num, Real.rpow_neg hr.le, Real.rpow_two] at h
    simpa only [one_div] using h

/-- The folded class integral, in the coordinate `t = exp v - 1`. -/
def classMellinReading (F : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (F t : ℂ) * classMellinWeight w (Real.log (1 + t))

/-- The exponential theta envelope gives a uniform class-reading bound
on the real-part range used by the outer Cauchy disk. -/
theorem classMellinReading_norm_le_twenty_thirds {H : ℝ → ℝ} (hm : Measurable H)
    (hH : ∀ t > 0, |H t| ≤ Real.exp (-(13 / 10) * t))
    {w : ℂ} (hlo : -2 ≤ w.re) (hhi : w.re ≤ 3) :
    ‖classMellinReading H w‖ ≤ 20 / 3 := by
  let W := fun t : ℝ ↦ classMellinWeight w (Real.log (1 + t))
  let B := fun t : ℝ ↦ 2 * Real.exp (-(3 / 10) * t)
  have hWmeas : Measurable W := by
    have hv : Measurable (fun t : ℝ ↦ (Real.log (1 + t) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp
        (measurable_const.add measurable_id))
    exact ((Complex.continuous_exp.measurable.comp (measurable_const.mul hv)).add
        (Complex.continuous_exp.measurable.comp (measurable_const.mul hv))).div_const _
  have hPoly (t : ℝ) (ht : 0 < t) : ‖W t‖ ≤ (1 + t)^2 := by
    let v := Real.log (1 + t)
    have hv : 0 ≤ v := Real.log_nonneg (by linarith only [ht])
    have h₁ : ‖Complex.exp ((w - 1) * (v : ℂ))‖ ≤ Real.exp (2 * v) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [mul_re, sub_re, one_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right (by linarith only [hhi]) hv
    have h₂ : ‖Complex.exp (-w * (v : ℂ))‖ ≤ Real.exp (2 * v) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      simp only [mul_re, neg_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right (by linarith only [hlo]) hv
    change ‖(Complex.exp ((w - 1) * (v : ℂ)) + Complex.exp (-w * (v : ℂ))) / 2‖ ≤ _
    rw [norm_div, Complex.norm_ofNat]
    calc
      _ ≤ (‖Complex.exp ((w - 1) * (v : ℂ))‖ + ‖Complex.exp (-w * (v : ℂ))‖) / 2 :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
      _ ≤ Real.exp (2 * v) := by linarith only [h₁, h₂]
      _ = _ := by
        rw [two_mul, Real.exp_add, show Real.exp v = 1 + t from Real.exp_log (by linarith only [ht])]
        ring
  have hMajor (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : ‖(H t : ℂ) * W t‖ ≤ B t := by
    have ht' : 0 < t := ht
    have he := Real.sum_le_exp_of_nonneg ht'.le 3
    norm_num [Finset.sum_range_succ, Nat.factorial] at he
    have hPow : (1 + t)^2 ≤ 2 * Real.exp t := by nlinarith only [he]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ Real.exp (-(13 / 10) * t) * (1 + t)^2 :=
        mul_le_mul (hH t ht') (hPoly t ht') (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (-(13 / 10) * t) * (2 * Real.exp t) :=
        mul_le_mul_of_nonneg_left hPow (Real.exp_pos _).le
      _ = B t := by
        dsimp [B]
        rw [← mul_assoc, mul_comm (Real.exp (-(13 / 10) * t)) 2, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  obtain ⟨hExp, hVal⟩ := exp_rate_zeroth (r := 3 / 10) (by norm_num)
  have hB : IntegrableOn B (Ioi 0) := hExp.const_mul 2
  have hInt : IntegrableOn (fun t ↦ (H t : ℂ) * W t) (Ioi 0) := by
    refine Integrable.mono' hB
      ((Complex.continuous_ofReal.measurable.comp hm).mul hWmeas).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hMajor t ht
  change ‖∫ t : ℝ in Ioi 0, (H t : ℂ) * W t‖ ≤ _
  calc
    _ ≤ ∫ t : ℝ in Ioi 0, ‖(H t : ℂ) * W t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 0, B t :=
      setIntegral_mono_on hInt.norm hB measurableSet_Ioi hMajor
    _ = _ := by
      dsimp [B]
      rw [integral_const_mul, hVal]
      norm_num

/-- Retain the height in the real-part loss from the cosine term. -/
theorem classMellin_integral_bounds_with_height {U D : ℝ → ℝ}
    (hU : Measurable U) (hD : Measurable D)
    (hUbound : ∀ t > 0, 0 ≤ U t ∧ U t ≤ (54 / 55) * Real.exp (-(13 / 10) * t))
    (hDbound : ∀ t > 0, (5 / 16) * Real.exp (-(4 / 3) * t) ≤ D t ∧
      D t ≤ (63 / 110) * Real.exp (-(13 / 10) * t))
    {w : ℂ} (hhalf : 1 / 2 ≤ w.re) (hone : w.re ≤ 1) :
    ‖classMellinReading U w‖ ≤ 108 / 143 ∧
      15 / 88 - (225 / 1859) * w.im ^ 2 ≤ (classMellinReading D w).re ∧
      |(classMellinReading D w).im| ≤ |w.im| * (w.re - 1 / 2) / 4 := by
  let W := fun t : ℝ ↦ classMellinWeight w (Real.log (1 + t))
  let E := fun t : ℝ ↦ Real.exp (-(13 / 10) * t)
  let R := fun t : ℝ ↦ Real.exp (-(11 / 6) * t)
  let X := fun t : ℝ ↦ t * E t
  let d := |w.im| * (w.re - 1 / 2)
  have hd : 0 ≤ d := mul_nonneg (abs_nonneg _) (sub_nonneg.mpr hhalf)
  have hW : Measurable W := by
    have hv : Measurable (fun t : ℝ ↦ (Real.log (1 + t) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp
        (measurable_const.add measurable_id))
    exact ((Complex.continuous_exp.measurable.comp (measurable_const.mul hv)).add
        (Complex.continuous_exp.measurable.comp (measurable_const.mul hv))).div_const _
  have hWb (t : ℝ) (ht : 0 < t) :=
    classMellinWeight_bounds (v := Real.log (1 + t)) (Real.log_nonneg (by linarith)) hhalf hone
  have hE := exp_rate_zeroth (show (0 : ℝ) < 13 / 10 by norm_num)
  have hEi : IntegrableOn E (Ioi 0) := hE.1
  have hEval : (∫ t in Ioi 0, E t) = 10 / 13 := hE.2.trans (by norm_num)
  have hR := exp_rate_zeroth (show (0 : ℝ) < 11 / 6 by norm_num)
  have hRi : IntegrableOn R (Ioi 0) := hR.1
  have hRval : (∫ t in Ioi 0, R t) = 6 / 11 := hR.2.trans (by norm_num)
  have hX := exp_rate_first (show (0 : ℝ) < 13 / 10 by norm_num)
  have hXi : IntegrableOn X (Ioi 0) := hX.1
  have hXval : (∫ t in Ioi 0, X t) = 100 / 169 := hX.2.trans (by norm_num)
  have hD0 (t : ℝ) (ht : 0 < t) : 0 ≤ D t :=
    (by positivity : 0 ≤ (5 / 16) * Real.exp (-(4 / 3) * t)).trans (hDbound t ht).1
  have hnorm {F : ℝ → ℝ} {b : ℝ} (hb : ∀ t > 0, 0 ≤ F t ∧ F t ≤ b * E t)
      (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : ‖(F t : ℂ) * W t‖ ≤ b * E t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb t ht).1]
    exact (mul_le_of_le_one_right (hb t ht).1 (hWb t ht).1).trans (hb t ht).2
  have hInt {F : ℝ → ℝ} {b : ℝ} (hm : Measurable F)
      (hb : ∀ t > 0, 0 ≤ F t ∧ F t ≤ b * E t) :
      IntegrableOn (fun t ↦ (F t : ℂ) * W t) (Ioi 0) := by
    refine Integrable.mono' (hEi.const_mul b)
      ((Complex.continuous_ofReal.measurable.comp hm).mul hW).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hnorm hb t ht
  have hUi := hInt hU hUbound
  have hDi := hInt hD (b := 63 / 110) (fun t ht ↦ ⟨hD0 t ht, (hDbound t ht).2⟩)
  have hdim : IntegrableOn (fun t ↦ ((D t : ℂ) * W t).im) (Ioi 0) := hDi.im
  have hdre : IntegrableOn (fun t ↦ ((D t : ℂ) * W t).re) (Ioi 0) := hDi.re
  have hmoment (t : ℝ) (ht : 0 < t) :
      D t * (Real.log (1 + t)) ^ 2 ≤ (9 / 22) * X t := by
    calc
      _ ≤ D t * ((5 / 7) * t) :=
        mul_le_mul_of_nonneg_left (classMellin_log_sq_le ht.le) (hD0 t ht)
      _ ≤ ((63 / 110) * E t) * ((5 / 7) * t) :=
        mul_le_mul_of_nonneg_right (hDbound t ht).2 (by positivity)
      _ = _ := by dsimp [X]; ring
  have hbaseline (t : ℝ) (ht : 0 < t) :
      (5 / 16) * R t ≤ D t * Real.exp (-Real.log (1 + t) / 2) := by
    have hl := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith)
    have he := Real.exp_le_exp.mpr (show -t / 2 ≤ -Real.log (1 + t) / 2 by linarith)
    calc
      _ = ((5 / 16) * Real.exp (-(4 / 3) * t)) * Real.exp (-t / 2) := by
        dsimp [R]
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := mul_le_mul (hDbound t ht).1 he (Real.exp_pos _).le (hD0 t ht)
  refine ⟨?_, ?_, ?_⟩
  · change ‖∫ t in Ioi 0, (U t : ℂ) * W t‖ ≤ _
    apply (norm_integral_le_integral_norm _).trans
    calc
      _ ≤ ∫ t in Ioi 0, (54 / 55 : ℝ) * E t :=
        setIntegral_mono_on hUi.norm (hEi.const_mul _) measurableSet_Ioi (hnorm hUbound)
      _ = (54 / 55 : ℝ) * (10 / 13) := by rw [integral_const_mul, hEval]
      _ = 108 / 143 := by norm_num
  · change 15 / 88 - (225 / 1859) * w.im ^ 2 ≤
      RCLike.re (∫ t in Ioi 0, (D t : ℂ) * W t)
    rw [← integral_re hDi]
    have hpoint (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
        (5 / 16) * R t - (9 / 44 * w.im ^ 2) * X t ≤ ((D t : ℂ) * W t).re := by
      have hb := mul_le_mul_of_nonneg_left (hWb t ht).2.1 (hD0 t ht)
      have hm := hmoment t ht
      have hh := mul_le_mul_of_nonneg_left hm (sq_nonneg w.im)
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      change D t * (Real.exp (-Real.log (1 + t) / 2) -
        w.im ^ 2 * (Real.log (1 + t)) ^ 2 / 2) ≤ D t * (W t).re at hb
      nlinarith only [hb, hh, hbaseline t ht]
    calc
      (15 / 88 : ℝ) - (225 / 1859) * w.im ^ 2 =
          (5 / 16) * (6 / 11) - (9 / 44 * w.im ^ 2) * (100 / 169) := by ring
      _ = ∫ t in Ioi 0, (5 / 16) * R t - (9 / 44 * w.im ^ 2) * X t := by
        rw [integral_sub (hRi.const_mul _) (hXi.const_mul _), integral_const_mul,
          integral_const_mul, hRval, hXval]
      _ ≤ _ := setIntegral_mono_on ((hRi.const_mul _).sub (hXi.const_mul _)) hdre
        measurableSet_Ioi hpoint
  · change |RCLike.im (∫ t in Ioi 0, (D t : ℂ) * W t)| ≤ d / 4
    rw [← integral_im hDi]
    apply (abs_integral_le_integral_abs).trans
    calc
      _ ≤ ∫ t in Ioi 0, (d * (9 / 22)) * X t :=
        setIntegral_mono_on hdim.abs (hXi.const_mul _) measurableSet_Ioi (fun t ht ↦ by
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul,
            abs_of_nonneg (hD0 t ht)]
          calc
            _ ≤ D t * (d * (Real.log (1 + t)) ^ 2) :=
              mul_le_mul_of_nonneg_left (hWb t ht).2.2 (hD0 t ht)
            _ = d * (D t * (Real.log (1 + t)) ^ 2) := by ring
            _ ≤ d * ((9 / 22) * X t) := mul_le_mul_of_nonneg_left (hmoment t ht) hd
            _ = _ := by ring)
      _ = (d * (9 / 22)) * (100 / 169) := by rw [integral_const_mul, hXval]
      _ ≤ _ := by nlinarith only [hd]

#print axioms classMellinWeight_bounds
#print axioms classMellin_log_sq_le

theorem classMellin_integral_bounds_to_half {U D : ℝ → ℝ} (hU : Measurable U) (hD : Measurable D)
    (hUbound : ∀ t > 0, 0 ≤ U t ∧ U t ≤ (54 / 55) * Real.exp (-(13 / 10) * t))
    (hDbound : ∀ t > 0, (5 / 16) * Real.exp (-(4 / 3) * t) ≤ D t ∧
      D t ≤ (63 / 110) * Real.exp (-(13 / 10) * t))
    {w : ℂ} (hhalf : 1 / 2 ≤ w.re) (hone : w.re ≤ 1) (him : |w.im| ≤ 1 / 2) :
    ‖classMellinReading U w‖ ≤ 4 / 5 ∧
      1 / 8 ≤ (classMellinReading D w).re ∧
      |(classMellinReading D w).im| ≤ |w.im| * (w.re - 1 / 2) / 4 := by
  obtain ⟨hU', hD', hphase⟩ := classMellin_integral_bounds_with_height hU hD hUbound hDbound hhalf hone
  have hi := pow_le_pow_left₀ (abs_nonneg _) him 2
  rw [sq_abs] at hi
  exact ⟨hU'.trans (by norm_num), by nlinarith only [hi, hD'], hphase⟩

theorem classMellin_integral_bounds {U D : ℝ → ℝ} (hU : Measurable U) (hD : Measurable D)
    (hUbound : ∀ t > 0, 0 ≤ U t ∧ U t ≤ (54 / 55) * Real.exp (-(13 / 10) * t))
    (hDbound : ∀ t > 0, (5 / 16) * Real.exp (-(4 / 3) * t) ≤ D t ∧
      D t ≤ (63 / 110) * Real.exp (-(13 / 10) * t))
    {w : ℂ} (hhalf : 1 / 2 ≤ w.re) (hone : w.re ≤ 1) (him : |w.im| ≤ 1 / 4) :
    ‖classMellinReading U w‖ ≤ 4 / 5 ∧
      1 / 8 ≤ (classMellinReading D w).re ∧
      |(classMellinReading D w).im| ≤ |w.im| * (w.re - 1 / 2) / 4 :=
  classMellin_integral_bounds_to_half hU hD hUbound hDbound hhalf hone (him.trans (by norm_num))

#print axioms classMellin_integral_bounds_with_height
#print axioms classMellin_integral_bounds_to_half
#print axioms classMellin_integral_bounds

end
#print axioms classMellinReading_norm_le_twenty_thirds

end FieldTarget
