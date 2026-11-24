import NativeDottieMellinFinite
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Complex.ExponentialBounds

/-! A uniform complex neighborhood for the exact Dottie Mellin kernel. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

private def evenDet (z : ℂ) : ℂ := 3 + 4 * (Complex.sinh z ^ 2 + z ^ 2)
private def oddDet (z : ℂ) : ℂ := 4 * z * Complex.sinh z

private theorem exp_sector {u : ℂ} (hu : |u.im| ≤ 1/16) :
    0 < (Complex.exp u).re ∧ |(Complex.exp u).im| ≤ (Complex.exp u).re / 15 := by
  have hu2 : u.im ^ 2 ≤ (1/16 : ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hu 2
  have hc : (15/16 : ℝ) ≤ Real.cos u.im := by
    linarith only [Real.one_sub_sq_div_two_le_cos (x := u.im), hu2]
  have hs := (Real.abs_sin_le_abs (x := u.im)).trans hu
  rw [Complex.exp_re, Complex.exp_im, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact ⟨mul_pos (Real.exp_pos _) (by linarith only [hc]),
    by
      calc
        Real.exp u.re * |Real.sin u.im| ≤ Real.exp u.re * (1/16) :=
          mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
        _ ≤ Real.exp u.re * Real.cos u.im / 15 := by
          linarith only [mul_le_mul_of_nonneg_left hc (Real.exp_pos u.re).le]⟩

private theorem sinh_coordinates (z : ℂ) :
    (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im ∧
    (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  have h := Complex.sinh_add (z.re : ℂ) ((z.im : ℂ) * Complex.I)
  rw [Complex.re_add_im, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos] at h
  constructor
  · rw [h]
    simp [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.sinh_ofReal_re, Complex.cos_ofReal_re]
  · rw [h]
    simp [Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.sin_ofReal_re]

private theorem re_sq_of_sector {z : ℂ} (hz : |z.im| ≤ (3/8)*z.re) :
    (3/4)*‖z‖^2 ≤ (z^2).re := by
  have hy : z.im^2 ≤ ((3/8)*z.re)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hz 2
  rw [Complex.sq_norm, Complex.normSq_apply, pow_two z, Complex.mul_re]
  nlinarith only [hy, sq_nonneg z.re]

private theorem small_det {z : ℂ} (hx : 0 < z.re) (hx4 : z.re ≤ 4)
    (hy : |z.im| ≤ z.re/15) :
    0 < ‖evenDet z‖ ∧ ‖oddDet z‖ ≤ (2/3)*‖evenDet z‖ := by
  have hy4 : |z.im| ≤ 4/15 := by linarith only [hy, hx4]
  have hy2 : z.im^2 ≤ (4/15:ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hy4 2
  have hc : (24/25:ℝ) ≤ Real.cos z.im := by
    linarith only [Real.one_sub_sq_div_two_le_cos (x := z.im), hy2]
  have hs : 0 ≤ Real.sinh z.re := Real.sinh_nonneg_iff.mpr hx.le
  have hcosh := (Real.cosh_pos z.re).le
  have hex : Real.exp (-z.re) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le)
  have hxsinh : z.re ≤ Real.sinh z.re := Real.self_le_sinh_iff.mpr hx.le
  have hprod : z.re * Real.cosh z.re ≤ (z.re+1)*Real.sinh z.re := by
    have he := mul_le_mul_of_nonneg_left hex hx.le
    have heq := congrArg (fun y : ℝ => z.re*y) (Real.cosh_sub_sinh z.re)
    dsimp only at heq
    linarith only [he, heq, hxsinh, mul_sub z.re (Real.cosh z.re) (Real.sinh z.re)]
  have hsinh := sinh_coordinates z
  have hre : (24/25)*Real.sinh z.re ≤ (Complex.sinh z).re := by
    rw [hsinh.1, mul_comm (24/25 : ℝ)]
    exact mul_le_mul_of_nonneg_left hc hs
  have him : |(Complex.sinh z).im| ≤ Real.sinh z.re/3 := by
    rw [hsinh.2, abs_mul, abs_of_nonneg hcosh]
    calc
      _ ≤ Real.cosh z.re * (z.re/15) := mul_le_mul_of_nonneg_left
        (Real.abs_sin_le_abs.trans hy) hcosh
      _ = z.re * Real.cosh z.re / 15 := by ring
      _ ≤ (z.re+1)*Real.sinh z.re/15 := div_le_div_of_nonneg_right hprod (by norm_num)
      _ ≤ _ := by
        have hm := mul_le_mul_of_nonneg_right (show z.re+1 ≤ 5 by linarith only [hx4]) hs
        linarith only [hm]
  have hrz := re_sq_of_sector (z := z) (by linarith only [hy, hx])
  have hrs := re_sq_of_sector (z := Complex.sinh z) (by linarith only [hre, him, hs])
  have ha : 3 + 3*(‖Complex.sinh z‖^2+‖z‖^2) ≤ ‖evenDet z‖ := by
    apply le_trans _ (Complex.re_le_norm (evenDet z))
    dsimp only [evenDet]
    norm_num [Complex.add_re, Complex.mul_re]
    linarith only [hrz, hrs]
  have hb : ‖oddDet z‖ = 4*‖z‖*‖Complex.sinh z‖ := by
    norm_num [oddDet, norm_mul]
  rw [hb]
  constructor
  · nlinarith only [ha, sq_nonneg ‖z‖, sq_nonneg ‖Complex.sinh z‖]
  · nlinarith only [ha, sq_nonneg (‖z‖-‖Complex.sinh z‖)]

private theorem exp_neg_four_le : Real.exp (-4) ≤ 1/50 := by
  have e : (27/10:ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have h := pow_le_pow_left₀ (show (0:ℝ) ≤ 27/10 by norm_num) e 4
  have heq : Real.exp 4 = Real.exp 1 ^ 4 := by
    norm_num [← Real.exp_nat_mul]
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  linarith only [heq, h]

private theorem scaled_det (z : ℂ) :
    let b := Complex.exp (-z)
    evenDet z * b^2 = 1+b^2+4*(z*b)^2+b^4 ∧
    oddDet z * b^2 = 2*(z*b)*(1-b^2) := by
  let b := Complex.exp (-z)
  have he : Complex.exp z * b = 1 := by
    rw [show b = Complex.exp (-z) by rfl, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hs : Complex.sinh z * b = (1-b^2)/2 := by
    calc
      Complex.sinh z * b = (Complex.exp z*b-b*b)/2 := by
        change ((Complex.exp z-b)/2)*b = _
        ring
      _ = _ := by rw [he, pow_two]
  constructor
  · change evenDet z * b^2 = _
    calc
      _ = 3*b^2 + 4*((Complex.sinh z*b)^2+(z*b)^2) := by unfold evenDet; ring
      _ = _ := by rw [hs]; ring
  · change oddDet z * b^2 = _
    calc
      _ = 4*(z*b)*(Complex.sinh z*b) := by unfold oddDet; ring
      _ = _ := by rw [hs]; ring

private theorem large_det {z : ℂ} (hx : 4 ≤ z.re) (hy : |z.im| ≤ z.re/15) :
    0 < ‖evenDet z‖ ∧ ‖oddDet z‖ ≤ (2/3)*‖evenDet z‖ := by
  let b := Complex.exp (-z)
  have hb : ‖b‖ = Real.exp (-z.re) := by simp only [b, Complex.norm_exp, Complex.neg_re]
  have hne : b ≠ 0 := Complex.exp_ne_zero _
  have hbn : ‖b‖ ≤ 1/50 := by
    rw [hb]
    exact (Real.exp_le_exp.mpr (by linarith only [hx] : -z.re ≤ -4)).trans exp_neg_four_le
  have hz : ‖z‖ ≤ (16/15)*z.re := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg (by linarith only [hx] : 0 ≤ z.re)] at h
    linarith only [h, hy]
  have hzexp : z.re*Real.exp (-z.re) ≤ 4*Real.exp (-4) := by
    have hlin : z.re ≤ 4*Real.exp (z.re-4) := by
      linarith only [Real.add_one_le_exp (z.re-4), hx]
    calc
      _ ≤ (4*Real.exp (z.re-4))*Real.exp (-z.re) :=
        mul_le_mul_of_nonneg_right hlin (Real.exp_pos _).le
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add, show z.re-4 + -z.re = -4 by ring]
  have hzb : ‖z*b‖ ≤ 32/375 := by
    rw [norm_mul, hb]
    have ha := mul_le_mul_of_nonneg_right hz (Real.exp_pos (-z.re)).le
    have hc := mul_le_mul_of_nonneg_left hzexp (show (0:ℝ) ≤ 16/15 by norm_num)
    nlinarith only [ha, hc, exp_neg_four_le]
  have hb2 := pow_le_pow_left₀ (norm_nonneg b) hbn 2
  have hb4 := pow_le_pow_left₀ (norm_nonneg b) hbn 4
  have hzb2 := pow_le_pow_left₀ (norm_nonneg (z*b)) hzb 2
  have hs := scaled_det z
  change evenDet z*b^2 = 1+b^2+4*(z*b)^2+b^4 ∧
    oddDet z*b^2 = 2*(z*b)*(1-b^2) at hs
  have ha : ‖evenDet z*b^2 - 1‖ ≤ 1/10 := by
    have he : evenDet z*b^2-1 = (b^2+4*(z*b)^2)+b^4 := by rw [hs.1]; ring
    rw [he]
    calc
      _ ≤ (‖b^2‖+‖4*(z*b)^2‖)+‖b^4‖ :=
        (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
      _ ≤ _ := by
        rw [norm_mul, norm_pow b 2, norm_pow (z*b) 2, norm_pow b 4]
        rw [show ‖(4:ℂ)‖ = (4:ℝ) by norm_num]
        linarith only [hb2, hb4, hzb2]
  have haLower : (9/10:ℝ) ≤ ‖evenDet z*b^2‖ := by
    have hr : ‖(1:ℂ)‖ ≤ ‖evenDet z*b^2‖ + ‖evenDet z*b^2-1‖ := by
      have ht := norm_add_le (evenDet z*b^2) (1-evenDet z*b^2)
      rwa [show evenDet z*b^2 + (1-evenDet z*b^2) = 1 by ring, norm_sub_rev 1] at ht
    rw [norm_one] at hr
    linarith only [ha, hr]
  have hB : ‖oddDet z*b^2‖ ≤ 1/5 := by
    rw [hs.2]
    have hbG : ‖1-b^2‖ ≤ 1+(1/50:ℝ)^2 := by
      simpa [norm_pow] using (norm_sub_le 1 (b^2)).trans (add_le_add_left
        (show ‖b^2‖ ≤ (1/50:ℝ)^2 by rwa [norm_pow]) ‖(1:ℂ)‖)
    calc
      _ = 2*‖z*b‖*‖1-b^2‖ := by norm_num [norm_mul]
      _ ≤ 2*(32/375)* (1+(1/50:ℝ)^2) := by gcongr
      _ ≤ _ := by norm_num
  have hpos : 0 < ‖b^2‖ := norm_pos_iff.mpr (pow_ne_zero _ hne)
  rw [norm_mul] at haLower hB
  constructor
  · exact pos_of_mul_pos_left (lt_of_lt_of_le (by norm_num : (0:ℝ) < 9/10) haLower) hpos.le
  · refine le_of_mul_le_mul_right ?_ hpos
    nlinarith only [hB, haLower]

private def determinantRatio (z : ℂ) : ℂ := oddDet z / evenDet z

theorem determinantRatio_bound {u : ℂ} (hu : |u.im| ≤ 1/16) :
    0 < ‖evenDet (Complex.exp u)‖ ∧ ‖determinantRatio (Complex.exp u)‖ ≤ 2/3 := by
  obtain ⟨hx, hy⟩ := exp_sector hu
  obtain ⟨ha, hb⟩ := if h : (Complex.exp u).re ≤ 4 then small_det hx h hy
    else large_det (le_of_lt (lt_of_not_ge h)) hy
  refine ⟨ha, ?_⟩
  rw [determinantRatio, norm_div]
  exact (div_le_iff₀ ha).mpr hb

private theorem norm_log_add_le {q : ℂ} (hq : ‖q‖ ≤ 2/3) :
    ‖Complex.log (1+q)‖ ≤ 4/3 := by
  have hq1 : ‖q‖ < 1 := lt_of_le_of_lt hq (by norm_num)
  have hi : (1-‖q‖)⁻¹ ≤ (3:ℝ) := by
    rw [inv_le_iff_one_le_mul₀ (by linarith only [hq1])]
    linarith only [hq]
  have hs := pow_le_pow_left₀ (norm_nonneg q) hq 2
  have hmul := mul_le_mul hs hi (inv_nonneg.mpr (by linarith only [hq1]))
    (by norm_num : (0:ℝ) ≤ (2/3)^2)
  linarith only [Complex.norm_log_one_add_le hq1, hmul, hq]

private def stripLogGap (u : ℂ) : ℂ :=
  let q := determinantRatio (Complex.exp u)
  Complex.log (1-q) - Complex.log (1+q)

theorem norm_stripLogGap_le {u : ℂ} (hu : |u.im| ≤ 1/16) :
    ‖stripLogGap u‖ ≤ 8/3 := by
  have h := (determinantRatio_bound hu).2
  have hneg : ‖-determinantRatio (Complex.exp u)‖ ≤ 2/3 := by rwa [norm_neg]
  unfold stripLogGap
  dsimp only
  rw [sub_eq_add_neg (1:ℂ)]
  have hsum := (norm_sub_le (Complex.log (1 + -determinantRatio (Complex.exp u)))
    (Complex.log (1 + determinantRatio (Complex.exp u)))).trans
    (add_le_add (norm_log_add_le hneg) (norm_log_add_le h))
  exact hsum.trans (by norm_num)

private theorem stripLogGap_differentiableAt {u : ℂ} (hu : |u.im| ≤ 1/16) :
    DifferentiableAt ℂ stripLogGap u := by
  obtain ⟨hA, hq⟩ := determinantRatio_bound hu
  have hn : evenDet (Complex.exp u) ≠ 0 := norm_pos_iff.mp hA
  have hS : Differentiable ℂ (fun z => Complex.sinh (Complex.exp z)) :=
    Complex.differentiable_sinh.comp Complex.differentiable_exp
  have he : Differentiable ℂ (fun z => evenDet (Complex.exp z)) := by
    unfold evenDet
    fun_prop
  have ho : Differentiable ℂ (fun z => oddDet (Complex.exp z)) := by
    unfold oddDet
    fun_prop
  have hd : DifferentiableAt ℂ (fun z => determinantRatio (Complex.exp z)) u :=
    ho.differentiableAt.div he.differentiableAt hn
  have hm : 1 - determinantRatio (Complex.exp u) ∈ Complex.slitPlane := by
    rw [sub_eq_add_neg]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_neg]
    linarith only [hq]
  have hp : 1 + determinantRatio (Complex.exp u) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_of_norm_lt_one (by linarith only [hq])
  have hdm : DifferentiableAt ℂ (fun z => 1 - determinantRatio (Complex.exp z)) u :=
    (differentiableAt_const (1:ℂ)).sub hd
  have hdp : DifferentiableAt ℂ (fun z => 1 + determinantRatio (Complex.exp z)) u :=
    (differentiableAt_const (1:ℂ)).add hd
  exact ((Complex.differentiableAt_log hm).comp u hdm).sub
    ((Complex.differentiableAt_log hp).comp u hdp)

private theorem stripLogGap_ofReal (u : ℝ) :
    stripLogGap (u:ℂ) = (finiteLogGap (Real.exp u):ℂ) := by
  let x := Real.exp u
  let a := 3+4*(Real.sinh x^2+x^2)
  let b := 4*x*Real.sinh x
  have hq : determinantRatio (Complex.exp (u:ℂ)) = ((b/a:ℝ):ℂ) := by
    unfold determinantRatio evenDet oddDet
    simp only [a, b, x, ← Complex.ofReal_exp, ← Complex.ofReal_sinh,
      Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_ofNat]
  have hbound := (determinantRatio_bound (u := (u:ℂ)) (by norm_num)).2
  rw [hq, Complex.norm_real, Real.norm_eq_abs] at hbound
  obtain ⟨hlo,hhi⟩ := abs_le.mp hbound
  have hp : 0 < 1+b/a := by linarith only [hlo]
  have hm : 0 < 1-b/a := by linarith only [hhi]
  have ha : a ≠ 0 := by dsimp only [a]; positivity
  calc
    stripLogGap (u:ℂ) = ((Real.log (1-b/a) - Real.log (1+b/a):ℝ):ℂ) := by
      simp only [stripLogGap, hq, Complex.ofReal_sub, Complex.ofReal_log hp.le,
        Complex.ofReal_log hm.le, Complex.ofReal_one, Complex.ofReal_add]
    _ = _ := by
      rw [← Real.log_div hm.ne' hp.ne', finiteLogGap_eq]
      change ((Real.log ((1-b/a)/(1+b/a)):ℝ):ℂ) = (Real.log ((a-b)/(a+b)):ℂ)
      rw [show (1-b/a) = (a-b)/a by field_simp,
        show (1+b/a) = (a+b)/a by field_simp, div_div_div_cancel_right₀ ha]

def holomorphicMellinDensity (k : ℕ) (u : ℂ) : ℂ :=
  ((-2:ℂ)*u)^k/(k.factorial:ℂ) * Complex.exp (-(2*firstCenter)*u) * stripLogGap u

theorem holomorphicMellinDensity_ofReal (k : ℕ) (u : ℝ) :
    holomorphicMellinDensity k (u:ℂ) = centerCoefficientDensity k u := by
  rw [holomorphicMellinDensity, stripLogGap_ofReal, centerCoefficientDensity_expLog, finiteLogGap_eq]

theorem holomorphicMellinDensity_differentiableAt (k : ℕ) {u : ℂ} (hu : |u.im| ≤ 1/16) :
    DifferentiableAt ℂ (holomorphicMellinDensity k) u := by
  unfold holomorphicMellinDensity
  exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ =>
    ((-2:ℂ)*z)^k/(k.factorial:ℂ) * Complex.exp (-(2*firstCenter)*z)) u).mul
    (stripLogGap_differentiableAt hu)

def mellinStripMajorant (k : ℕ) : ℝ :=
  (66:ℝ)^k/k.factorial * (11/4)^17 * (8/3)

theorem norm_holomorphicMellinDensity_le (k : ℕ) {u : ℂ}
    (hu : |u.im| ≤ 1/16) (hlo : -(513/16) ≤ u.re) (hhi : u.re ≤ 81/16) :
    ‖holomorphicMellinDensity k u‖ ≤ mellinStripMajorant k := by
  have hnr : |u.re| ≤ 513/16 := abs_le.mpr ⟨hlo, by linarith only [hhi]⟩
  have hnu : ‖u‖ ≤ 33 := by linarith only [Complex.norm_le_abs_re_add_abs_im u, hnr, hu]
  have hp : (-(2*firstCenter)*u).re = -u.re/2+(7067363/500000)*u.im := by
    norm_num [firstCenter, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
    ring
  have harg : (-(2*firstCenter)*u).re ≤ 17 := by
    rw [hp]
    linarith only [(abs_le.mp hu).2, hlo]
  have he : Real.exp 17 ≤ (11/4:ℝ)^17 := by
    have h : Real.exp 1 ≤ 11/4 := by linarith only [Real.exp_one_lt_d9]
    rw [show (17:ℝ) = ((17:ℕ):ℝ)*1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le h _
  have hnorm : ‖(-2:ℂ)*u‖ ≤ 66 := by
    rw [norm_mul, show ‖(-2:ℂ)‖ = (2:ℝ) by norm_num]
    linarith only [hnu]
  have he' := (Real.exp_le_exp.mpr harg).trans he
  rw [holomorphicMellinDensity, mellinStripMajorant, norm_mul, norm_mul, norm_div,
    norm_pow, Complex.norm_natCast, Complex.norm_exp]
  gcongr
  exact norm_stripLogGap_le hu

#print axioms determinantRatio_bound
#print axioms norm_stripLogGap_le
#print axioms holomorphicMellinDensity_ofReal
#print axioms holomorphicMellinDensity_differentiableAt
#print axioms norm_holomorphicMellinDensity_le

end DottieOriented.NativeSpectrum
end
