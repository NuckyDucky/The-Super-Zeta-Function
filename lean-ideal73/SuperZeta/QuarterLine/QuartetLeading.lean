import SuperZeta.UnitSpectrum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Real.Pi.Bounds

namespace SuperZeta.QuartetLeading
noncomputable section
open Real QuartetRadius RootBounds UnitSpectrum

/-- The upper first root of the original classified spectrum. -/
def first : ℂ := u (levelHeight 0)

private theorem sin_est {x : ℝ} (h : 0 ≤ x) (h1 : x ≤ 1) :
    let d := x^4*(5/96 : ℝ)
    let l := x-x^3/6-d
    let r := x-x^3/6+d
    let c := 1-x^2/2-d
    let e := 1-x^2/2+d
    2*l*c ≤ sin (2*x) ∧ sin (2*x) ≤ 2*r*e := by
  dsimp
  have s := (abs_le.mp (sin_bound (x := x) (by rw [abs_of_nonneg h]; exact h1)))
  have c := (abs_le.mp (cos_bound (x := x) (by rw [abs_of_nonneg h]; exact h1)))
  rw [abs_of_nonneg h] at s c
  have herror : x^5/100 ≤ x^4*(5/96:ℝ) := by
    nlinarith only [mul_le_mul_of_nonneg_left h1 (pow_nonneg h 4), pow_nonneg h 4]
  have hp : 0 ≤ x-x^3/6-x^4*(5/96 : ℝ) := by
    have hx2 := mul_le_mul_of_nonneg_right h1 h
    have hx3 := mul_le_mul_of_nonneg_right h1 (sq_nonneg x)
    have hx4 := mul_le_mul_of_nonneg_right h1 (pow_nonneg h 3)
    nlinarith
  have hc : 0 ≤ 1-x^2/2-x^4*(5/96 : ℝ) := by
    have hx := pow_le_pow_left₀ h h1 2
    have hy := pow_le_pow_left₀ h h1 4
    nlinarith
  rw [sin_two_mul]
  constructor
  · linarith [mul_le_mul (by linarith : x-x^3/6-x^4*(5/96 : ℝ) ≤ sin x)
                (by linarith : 1-x^2/2-x^4*(5/96 : ℝ) ≤ cos x) hc (by linarith : 0 ≤ sin x)]
  · linarith [mul_le_mul (by linarith : sin x ≤ x-x^3/6+x^4*(5/96 : ℝ))
                (by linarith : cos x ≤ 1-x^2/2+x^4*(5/96 : ℝ)) (by linarith : 0 ≤ cos x)
                (by linarith : 0 ≤ x-x^3/6+x^4*(5/96 : ℝ))]

private theorem exp_lower_data : 6.0860 < exp 1.806 ∧ exp 1.806 < 6.0861 := by
  have h := abs_le.mp (Real.exp_bound (x := 0.806) (n := 10) (by rw [abs_of_nonneg (by norm_num : 0 ≤ (0.806:ℝ))]; norm_num) (by norm_num))
  rw [abs_of_nonneg (by norm_num : 0 ≤ (0.806:ℝ))] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [show (1.806:ℝ)=1+0.806 by norm_num, Real.exp_add]
  constructor
  · nlinarith only [mul_lt_mul_of_pos_right Real.exp_one_gt_d9 (Real.exp_pos 0.806), h.1]
  · nlinarith only [mul_lt_mul_of_pos_right Real.exp_one_lt_d9 (Real.exp_pos 0.806), h.2]

private theorem exp_upper_data : 6.1288 - 0.0001 < exp 1.813 ∧ exp 1.813 < 6.1289 := by
  have h := abs_le.mp (Real.exp_bound (x := 0.813) (n := 10) (by rw [abs_of_nonneg (by norm_num : 0 ≤ (0.813:ℝ))]; norm_num) (by norm_num))
  rw [abs_of_nonneg (by norm_num : 0 ≤ (0.813:ℝ))] at h
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [show (1.813:ℝ)=1+0.813 by norm_num, Real.exp_add]
  constructor
  · nlinarith only [mul_lt_mul_of_pos_right Real.exp_one_gt_d9 (Real.exp_pos 0.813), h.1]
  · nlinarith only [mul_lt_mul_of_pos_right Real.exp_one_lt_d9 (Real.exp_pos 0.813), h.2]

private theorem hyp_data :
    2.9608 < sinh 1.806 ∧ sinh 1.806 < 2.961 ∧ cosh 1.806 < 3.1253 ∧
    2.9827 < sinh 1.813 ∧ sinh 1.813 < 2.983 ∧ 3.1458 < cosh 1.813 := by
  have ⟨a,b⟩ := exp_lower_data
  have ⟨c,d⟩ := exp_upper_data
  have l : 0.16430 < (exp 1.806)⁻¹ := by rw [lt_inv_comm₀ (by norm_num) (exp_pos _)]; linarith
  have r : (exp 1.806)⁻¹ < 0.16436 := by rw [inv_lt_comm₀ (exp_pos _) (by norm_num)]; linarith
  have l' : 0.1631 < (exp 1.813)⁻¹ := by rw [lt_inv_comm₀ (by norm_num) (exp_pos _)]; linarith
  have r' : (exp 1.813)⁻¹ < 0.1632 := by rw [inv_lt_comm₀ (exp_pos _) (by norm_num)]; linarith
  simp only [sinh_eq, cosh_eq, exp_neg]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

private theorem angle_band {y : ℝ} (hl : 1.806 ≤ y) (hr : y ≤ 1.813) :
    π/2+0.648 < θ y ∧ θ y < π/2+0.663 := by
  obtain ⟨sl,_,_,_,sr,_⟩ := hyp_data
  have hslo := Real.sinh_le_sinh.mpr hl
  have hshi := Real.sinh_le_sinh.mpr hr
  have hs : 0 < sinh y := by linarith
  have ha : 0.6053 < a y := (lt_div_iff₀ hs).mpr (by nlinarith only [hl, hshi, sr])
  have hb : a y < 0.6124 := (div_lt_iff₀ hs).mpr (by nlinarith only [hr, hslo, sl])
  have hc : cos (θ y) = -a y := Real.cos_arccos (by linarith) (by linarith)
  have ang0 : 0 ≤ θ y := Real.arccos_nonneg _
  have angπ : θ y ≤ π := Real.arccos_le_pi _
  have sn1 := (sin_est (x := 0.324) (by norm_num) (by norm_num)).2
  have sn2 := (sin_est (x := 0.3315) (by norm_num) (by norm_num)).1
  norm_num at sn1 sn2
  have c1 : cos (π/2+0.648) = -sin 0.648 := by rw [cos_add, cos_pi_div_two, sin_pi_div_two]; ring
  have c2 : cos (π/2+0.663) = -sin 0.663 := by rw [cos_add, cos_pi_div_two, sin_pi_div_two]; ring
  constructor
  · by_contra! h
    have := cos_le_cos_of_nonneg_of_le_pi ang0 (by linarith [Real.pi_gt_three] : π/2+0.648 ≤ π) h
    linarith only [this, hc, c1, ha, sn1]
  · by_contra! h
    have := cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_gt_three] : 0 ≤ π/2+0.663) angπ h
    linarith only [this, hc, c2, hb, sn2]

private theorem sin_sq_angle {y : ℝ} (hy : 0 < y) :
    0 ≤ sin (θ y) ∧ sin (θ y)^2 + (a y)^2 = 1 := by
  have ha : 0 ≤ a y := div_nonneg hy.le (Real.sinh_pos_iff.mpr hy).le
  have hb : a y ≤ 1 := (div_le_one (Real.sinh_pos_iff.mpr hy)).mpr (Real.self_le_sinh_iff.mpr hy.le)
  have hc : cos (θ y) = -a y := Real.cos_arccos (by linarith) (by linarith)
  exact ⟨sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg _) (arccos_le_pi _),
    by simpa only [hc, neg_sq] using sin_sq_add_cos_sq (θ y)⟩

theorem height_interval : 1.806 < levelHeight 0 ∧ levelHeight 0 < 1.813 := by
  obtain ⟨sl,sr,cl,tl,tr,cr⟩ := hyp_data
  have a1 : 0.6098 < a 1.806 := (lt_div_iff₀ (by linarith : 0 < sinh 1.806)).mpr (by linarith)
  have a2 : a 1.813 < 0.608 := (div_lt_iff₀ (by linarith : 0 < sinh 1.813)).mpr (by linarith)
  have a2p : 0 < a 1.813 := div_pos (by norm_num) (by linarith)
  obtain ⟨sp1,ss1⟩ := sin_sq_angle (show (0:ℝ)<1.806 by norm_num)
  obtain ⟨sp2,ss2⟩ := sin_sq_angle (show (0:ℝ)<1.813 by norm_num)
  have s1 : sin (θ 1.806) < 0.7927 := by
    nlinarith only [ss1, sq_nonneg (a 1.806 - 0.6098), a1, sq_nonneg (sin (θ 1.806)-0.7927)]
  have s2 : 0.7938 < sin (θ 1.813) := by
    by_contra! h
    nlinarith only [ss2, mul_self_le_mul_self sp2 h, mul_self_lt_mul_self a2p.le a2]
  have x1 := (mul_le_mul_of_nonneg_right cl.le sp1).trans_lt (mul_lt_mul_of_pos_left s1 (by norm_num : 0 < (3.1253:ℝ)))
  have x2 := mul_lt_mul cr s2.le (by norm_num : 0 < (0.7938:ℝ)) (cosh_pos _).le
  have b1 := (angle_band (y:=1.806) (by norm_num) (by norm_num)).2
  have b2 := (angle_band (y:=1.813) (by norm_num) (by norm_num)).1
  obtain ⟨pos,he⟩ := levelHeight_spec 0
  norm_num at he
  have low : level 1.806 < level (levelHeight 0) := by rw [he]; unfold level; linarith [Real.pi_gt_d4]
  have hi : level (levelHeight 0) < level 1.813 := by rw [he]; unfold level; linarith [Real.pi_lt_d4]
  exact ⟨(level_strictMonoOn.lt_iff_lt (by norm_num [Set.mem_Ioi]) pos).mp low,
         (level_strictMonoOn.lt_iff_lt pos (by norm_num [Set.mem_Ioi])).mp hi⟩

/-- Uniform geometric margin for the specified first upper root. -/
theorem bounds : (5/8 : ℝ) < first.arg ∧ ‖first‖ < 4 := by
  obtain ⟨yl,yr⟩ := height_interval
  obtain ⟨_,he⟩ := levelHeight_spec 0
  have lo := (angle_band yl.le yr.le).1
  have hi := (angle_band yl.le yr.le).2
  change 2 * (θ _ + x _) - π = _ at he
  norm_num at he
  have xr : first.re < 2.494 := by change x _ < _; linarith [Real.pi_lt_d4]
  have xl : 0 < first.re := by change 0 < x _; linarith [Real.pi_gt_d4]
  have yi : first.im = levelHeight 0 := rfl
  have yp : 0 < first.im := by rw [yi]; linarith
  have sn := (sin_est (x:=0.3125) (by norm_num) (by norm_num)).2
  norm_num at sn
  have sn' : sin (5/8 : ℝ) < 0.5861 := by linarith
  have qs : 0 ≤ sin (5/8:ℝ) := sin_nonneg_of_nonneg_of_le_pi (by norm_num) (by linarith [pi_gt_three])
  have qc : 0 < cos (5/8:ℝ) := cos_pos_of_mem_Ioo ⟨by linarith [pi_gt_three], by linarith [pi_gt_three]⟩
  have qc' : 0.8102 < cos (5/8:ℝ) := by
    by_contra! h
    nlinarith only [mul_self_lt_mul_self qs sn', mul_self_le_mul_self qc.le h, sin_sq_add_cos_sq (5/8:ℝ)]
  have tg : tan (5/8:ℝ) < 0.7235 := by rw [tan_eq_sin_div_cos,div_lt_iff₀ qc]; linarith
  constructor
  · apply (strictMonoOn_tan.lt_iff_lt
        (show (5/8:ℝ) ∈ Set.Ioo _ _ from ⟨by linarith [pi_gt_three], by linarith [pi_gt_three]⟩)
        ⟨lt_of_lt_of_le (by linarith [pi_gt_three]) (Complex.arg_nonneg_iff.mpr yp.le),
          Complex.arg_lt_pi_div_two_iff.mpr (Or.inl xl)⟩).mp
    rw [Complex.tan_arg]
    apply tg.trans
    rw [lt_div_iff₀ xl,yi]
    linarith
  · have hn := Complex.sq_norm first
    rw [Complex.normSq_apply] at hn
    rw [← yi] at yr
    nlinarith only [mul_self_lt_mul_self xl.le xr, mul_self_lt_mul_self yp.le yr, hn, sq_nonneg (‖first‖-4)]

theorem first_ne_zero : first ≠ 0 := by
  intro h
  have := bounds.1
  rw [h, Complex.arg_zero] at this
  norm_num at this

/-- Exact modulus of the dominant term at any quarter-line height. -/
theorem norm_leading (t : ℝ) :
    ‖first ^ (-2 * (⟨1/4,t⟩ : ℂ))‖ =
      (Real.sqrt ‖first‖)⁻¹ * Real.exp (2*t*first.arg) := by
  rw [Complex.norm_cpow_of_ne_zero first_ne_zero]
  have hr : (-2 * (⟨1/4,t⟩ : ℂ)).re = -(1/2 : ℝ) := by norm_num [Complex.mul_re, Complex.mul_im]
  have hi : (-2 * (⟨1/4,t⟩ : ℂ)).im = -2*t := by norm_num [Complex.mul_re, Complex.mul_im]
  rw [hr,hi, Real.rpow_neg (norm_nonneg _), ← Real.sqrt_eq_rpow]
  rw [show first.arg * (-2*t) = -(2*t*first.arg) by ring,exp_neg,div_inv_eq_mul]

theorem norm_leading_lower {t : ℝ} (ht : 0 ≤ t) :
    (1/2:ℝ)*Real.exp (5/4*t) ≤ ‖first ^ (-2 * (⟨1/4,t⟩ : ℂ))‖ := by
  rw [norm_leading]
  have hp := Real.sqrt_pos.mpr (norm_pos_iff.mpr first_ne_zero)
  have hq := Real.sq_sqrt (norm_nonneg first)
  have hs : Real.sqrt ‖first‖ < 2 := by nlinarith [bounds.2,sq_nonneg (Real.sqrt ‖first‖ - 2)]
  have hr : (1/2:ℝ) ≤ (Real.sqrt ‖first‖)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hp]
    norm_num
    exact hs.le
  exact mul_le_mul hr (exp_le_exp.mpr (by nlinarith [mul_nonneg ht (sub_nonneg.mpr bounds.1.le)]))
    (exp_pos _).le (inv_nonneg.mpr hp.le)

end
end SuperZeta.QuartetLeading
