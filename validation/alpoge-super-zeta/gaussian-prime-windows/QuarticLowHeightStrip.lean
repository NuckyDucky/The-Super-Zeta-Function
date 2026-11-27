import QuarticPositiveReal
import QuarticPointwise
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A positive real-part margin for the actual completed Gaussian reading
throughout a low-height strip. -/

open Complex Filter MeasureTheory Set

namespace QuarticKernel

open private certified_kernel_even all_exponential_weights_integrable
  theta_eq_quartic_real_formula from QuarticPositiveReal

private theorem theta_half_first_term {u : ℝ} (hu : 4 ≤ u) :
    Real.exp (-u) / 2 ≤ theta u := by
  let q := Real.exp (-u)
  have hq : 0 < q := Real.exp_pos _
  have h4 : (8 : ℝ) ≤ Real.exp 4 := by
    rw [show Real.exp (4 : ℝ) = Real.exp 1 ^ 4 by norm_num [← Real.exp_nat_mul]]
    exact (by norm_num : (8 : ℝ) ≤ 2 ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 4)
  have hsmall : q ≤ 1 / 8 := by
    dsimp only [q]
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) (h4.trans (Real.exp_le_exp.mpr hu))
  have hden : (2 / 3 : ℝ) ≤ (1 - q) ^ 2 :=
    (by norm_num : (2 / 3 : ℝ) ≤ (7 / 8 : ℝ) ^ 2).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith only [hsmall]) 2)
  have hratio : q / (1 - q) ^ 2 ≤ 3 * q / 2 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2 / 3) hden)).2
    have h := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ 3 * q / 2)
    linarith only [h]
  have h := (abs_le.mp (theta_first_term (by linarith only [hu] : 0 < u))).1
  change -(q / (1 - q) ^ 2 - q) ≤ theta u - q at h
  change q / 2 ≤ theta u
  linarith only [h, hratio]

private theorem kernel_floor_on_Icc {x : ℝ} (hx : x ∈ Icc (16 : ℝ) 17) :
    Real.exp (-20) / 2 ≤ kernel x := by
  have h16 : (6560000 : ℝ) ≤ Real.exp 16 := by
    rw [show Real.exp (16 : ℝ) = Real.exp 1 ^ 16 by norm_num [← Real.exp_nat_mul]]
    exact (by norm_num : (6560000 : ℝ) ≤ (27 / 10 : ℝ) ^ 16).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 16)
  have h17 : Real.exp 17 ≤ 32000000 := by
    rw [show Real.exp (17 : ℝ) = Real.exp 1 ^ 17 by norm_num [← Real.exp_nat_mul]]
    exact (pow_le_pow_left₀ (Real.exp_pos 1).le
      (show Real.exp 1 ≤ (11 / 4 : ℝ) by linarith [Real.exp_one_lt_d9]) 17).trans (by norm_num)
  let u := Real.exp x / scale
  have hu₀ : 4 ≤ u := by
    apply (le_div_iff₀ scale_pos).2
    linarith only [scale_lt, h16, Real.exp_le_exp.mpr hx.1]
  have hu₁ : u ≤ 20 := by
    apply (div_le_iff₀ scale_pos).2
    linarith only [QuarticGrid.scale_bounds.1, h17, Real.exp_le_exp.mpr hx.2]
  have hθ := theta_half_first_term hu₀
  have hθ₀ : 0 ≤ theta u := (by positivity : 0 ≤ Real.exp (-u) / 2).trans hθ
  have he : 1 ≤ Real.exp (x / 2) := Real.one_le_exp_iff.mpr (by linarith only [hx.1])
  calc
    Real.exp (-20) / 2 ≤ Real.exp (-u) / 2 :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hu₁)) (by norm_num)
    _ ≤ theta u := hθ
    _ ≤ kernel x := by
      simpa only [kernel, u, one_mul] using mul_le_mul_of_nonneg_right he hθ₀

private noncomputable def foldedPair (z : ℂ) (x : ℝ) : ℂ :=
  (kernel x : ℂ) * (exp (z * (x : ℂ)) + exp (-(z * (x : ℂ))))

private theorem foldedPair_re (z : ℂ) (x : ℝ) :
    (foldedPair z x).re =
      kernel x * (Real.exp (z.re * x) + Real.exp (-(z.re * x))) * Real.cos (z.im * x) := by
  simp only [foldedPair, mul_add, add_re, mul_re, mul_im, exp_re, ofReal_re, ofReal_im,
    mul_zero, zero_mul, sub_zero, add_zero, neg_re, neg_im, Real.cos_neg]
  ring

private theorem foldedPair_real_core {z : ℂ} {x : ℝ}
    (ht : |z.im| ≤ 1 / 20) (hx : x ∈ Icc (0 : ℝ) 20) :
    kernel x ≤ (foldedPair z x).re := by
  have ht' : |z.im * x| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hx.1]
    calc
      |z.im| * x ≤ (1 / 20) * 20 := mul_le_mul ht hx.2 hx.1 (by norm_num)
      _ = 1 := by norm_num
  have hsq : (z.im * x) ^ 2 ≤ 1 := by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ht' 2
  have hc : (1 / 2 : ℝ) ≤ Real.cos (z.im * x) := by
    calc
      _ ≤ 1 - (z.im * x) ^ 2 / 2 := by linarith only [hsq]
      _ ≤ _ := Real.one_sub_sq_div_two_le_cos
  have he : (2 : ℝ) ≤ Real.exp (z.re * x) + Real.exp (-(z.re * x)) := by
    have h := Real.one_le_cosh (z.re * x)
    rw [Real.cosh_eq] at h
    linarith only [h]
  have hphase : 1 ≤ (Real.exp (z.re * x) + Real.exp (-(z.re * x))) * Real.cos (z.im * x) := by
    simpa using mul_le_mul he hc (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity)
  rw [foldedPair_re, mul_assoc]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hphase (certified_kernel_positive hx.1).le

private theorem foldedTerm_norm_tail {z : ℂ} {x : ℝ} (hz : z.re ≤ 1 / 2) (hx : 20 ≤ x) :
    ‖(kernel x : ℂ) * exp (z * (x : ℂ))‖ ≤ 3 * Real.exp (-2 * x) := by
  have hx₀ : 0 ≤ x := by linarith only [hx]
  have hRe : z.re * x ≤ x / 2 := by
    linarith only [mul_le_mul_of_nonneg_right hz hx₀]
  have hExp : x / 2 + -40 * Real.exp (x - 18) + z.re * x ≤ -2 * x := by
    linarith only [hRe, Real.add_one_le_exp (x - 18), hx]
  calc
    _ = kernel x * Real.exp (z.re * x) := by
      simp only [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos (certified_kernel_positive hx₀),
        norm_exp, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    _ ≤ (3 * Real.exp (x / 2) * Real.exp (-40 * Real.exp (x - 18))) * Real.exp (z.re * x) :=
      mul_le_mul_of_nonneg_right (kernel_upper_on_tail (by linarith only [hx])) (Real.exp_pos _).le
    _ = 3 * Real.exp (x / 2 + -40 * Real.exp (x - 18) + z.re * x) := by
      rw [Real.exp_add, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) (by norm_num)

private theorem foldedPair_norm_tail {z : ℂ} {x : ℝ}
    (hlo : -(1 / 2 : ℝ) ≤ z.re) (hhi : z.re ≤ 1 / 2) (hx : 20 ≤ x) :
    ‖foldedPair z x‖ ≤ 6 * Real.exp (-2 * x) := by
  unfold foldedPair
  rw [mul_add, ← neg_mul]
  refine (norm_add_le _ _).trans ?_
  have h := add_le_add (foldedTerm_norm_tail hhi hx)
    (foldedTerm_norm_tail (z := -z) (by simp only [neg_re]; linarith only [hlo]) hx)
  linarith only [h]

/-- The finite positive part of the folded integral beats its full complex
tail uniformly through the closed strip. -/
theorem certified_quartic_mellin_low_strip_floor {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 1 / 20) :
    Real.exp (-20) / 4 ≤ (mellin (fun t : ℝ => (theta (t / scale) : ℂ)) w).re := by
  let z := w - (1 / 2 : ℂ)
  have hzre : z.re = w.re - 1 / 2 := by norm_num [z, Complex.div_re]
  have hzim : z.im = w.im := by norm_num [z, Complex.div_im]
  have hz₀ : -(1 / 2 : ℝ) ≤ z.re := by linarith only [hzre, hlo]
  have hz₁ : z.re ≤ 1 / 2 := by linarith only [hzre, hhi]
  have hzt : |z.im| ≤ 1 / 20 := hzim ▸ ht
  have hp := all_exponential_weights_integrable z
  have hn : IntegrableOn (fun x : ℝ => (kernel x : ℂ) * exp (-(z * (x : ℂ)))) (Ioi 0) := by
    simpa only [neg_mul] using all_exponential_weights_integrable (-z)
  have hf : IntegrableOn (foldedPair z) (Ioi 0) := by
    refine (hp.add hn).congr ?_
    filter_upwards [] with x
    simp only [foldedPair, mul_add, Pi.add_apply]
  rw [mellin_fold_of_even certified_kernel_even w hp hn, SuperZeta.PinchRadius.halfMellin,
    integral_Ici_eq_integral_Ioi]
  have he (x : ℝ) : (2 * (kernel x : ℂ)) * cosh (z * (x : ℂ)) = foldedPair z x := by
    simp only [foldedPair, cosh]
    ring
  change Real.exp (-20) / 4 ≤ (∫ x in Ioi (0 : ℝ), (2 * (kernel x : ℂ)) * cosh
    (z * (x : ℂ))).re
  simp_rw [he]
  rw [← RCLike.re_eq_complex_re, ← integral_re hf]
  let g : ℝ → ℝ := fun x => (foldedPair z x).re
  change Real.exp (-20) / 4 ≤ ∫ x in Ioi (0 : ℝ), g x
  have hg : IntegrableOn g (Ioi 0) := hf.re
  have hcore := hg.mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 20 ⊆ Ioi 0)
  have htail := hg.mono_set (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 20))
  have hsub : Ioc (16 : ℝ) 17 ⊆ Ioc (0 : ℝ) 20 := by
    intro x hx
    exact ⟨(by norm_num : (0 : ℝ) ≤ 16).trans_lt hx.1,
      hx.2.trans (by norm_num : (17 : ℝ) ≤ 20)⟩
  have hpositive (x : ℝ) (hx : x ∈ Ioc (0 : ℝ) 20) : kernel x ≤ g x :=
    foldedPair_real_core hzt ⟨hx.1.le, hx.2⟩
  have hsubfloor (x : ℝ) (hx : x ∈ Ioc (16 : ℝ) 17) :
      Real.exp (-20) / 2 ≤ g x :=
    (kernel_floor_on_Icc ⟨hx.1.le, hx.2⟩).trans (hpositive x (hsub hx))
  have hlow := setIntegral_ge_of_const_le measurableSet_Ioc
    (by simp [Real.volume_Ioc] : volume (Ioc (16 : ℝ) 17) ≠ ⊤)
    hsubfloor (hcore.mono_set hsub)
  have hmono := setIntegral_mono_set hcore (by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
    exact (certified_kernel_positive hx.1.le).le.trans (hpositive x hx))
    (ae_of_all volume hsub)
  have hcoreFloor : Real.exp (-20) / 2 ≤ ∫ x in Ioc (0 : ℝ) 20, g x := by
    have hm : volume.real (Ioc (16 : ℝ) 17) = 1 := by norm_num [Measure.real, Real.volume_Ioc]
    rw [hm, mul_one] at hlow
    exact hlow.trans hmono
  have hnegEnvelope := (exp_neg_integrableOn_Ioi 20 (b := 2) (by norm_num)).const_mul (-6 : ℝ)
  have htailFloor : -3 * Real.exp (-40) ≤ ∫ x in Ioi (20 : ℝ), g x := by
    have h := setIntegral_mono_on hnegEnvelope htail measurableSet_Ioi (fun x hx => by
      have hb := (abs_le.mp ((abs_re_le_norm _).trans (foldedPair_norm_tail hz₀ hz₁ hx.le))).1
      change -6 * Real.exp (-2 * x) ≤ (foldedPair z x).re
      linarith only [hb])
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0)] at h
    norm_num at h
    linarith only [h]
  have hsmall : 3 * Real.exp (-40) ≤ Real.exp (-20) / 4 := by
    have h20 : Real.exp (-20) ≤ 1 / 12 := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by linarith [Real.add_one_le_exp (20 : ℝ)])
    rw [show (-40 : ℝ) = -20 + -20 by norm_num, Real.exp_add]
    nlinarith only [mul_le_mul_of_nonneg_left h20 (Real.exp_pos (-20)).le]
  have hdisj : Disjoint (Ioc (0 : ℝ) 20) (Ioi 20) :=
    Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy)
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 20),
    setIntegral_union hdisj measurableSet_Ioi hcore htail]
  linarith only [hcoreFloor, htailFloor, hsmall]

theorem certified_quartic_completed_low_strip_floor {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 1 / 20) :
    Real.exp (-20) / 4 ≤ (QuarticRealFormula.completed w).re := by
  have hscale : scale = QuarticRealFormula.scale := by
    norm_num [scale, conductorNorm, QuarticRealFormula.scale]
  have he : mellin (fun t : ℝ => (theta (t / scale) : ℂ)) w =
      QuarticRealFormula.completed w := by
    unfold QuarticRealFormula.completed mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht₀ => ?_
    dsimp only
    rw [theta_eq_quartic_real_formula (div_pos ht₀ scale_pos), hscale]
  rw [← he]
  exact certified_quartic_mellin_low_strip_floor hlo hhi ht

theorem certified_quartic_completed_low_strip_ne_zero {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (ht : |w.im| ≤ 1 / 20) :
    QuarticRealFormula.completed w ≠ 0 := by
  intro hz
  have hf := certified_quartic_completed_low_strip_floor hlo hhi ht
  rw [hz, zero_re] at hf
  exact (not_le_of_gt (by positivity : 0 < Real.exp (-20) / 4)) hf

/-- A measuring circle contained in the low strip has a uniform signed
margin with the constant contour weight `-I`. -/
theorem certified_quartic_completed_low_circle_sign {c : ℂ} {r : ℝ}
    (hleft : r ≤ c.re) (hright : c.re + r ≤ 1) (hheight : |c.im| + r ≤ 1 / 20) :
    ∀ w ∈ Metric.sphere c r,
      (-I * QuarticRealFormula.completed w).im ≤ -(Real.exp (-20) / 4) := by
  intro w hw
  have hd := Metric.mem_sphere.mp hw
  rw [dist_eq_norm] at hd
  have hre := abs_le.mp ((abs_re_le_norm (w - c)).trans hd.le)
  rw [sub_re] at hre
  have h₀ : 0 ≤ w.re := by linarith only [hre.1, hleft]
  have h₁ : w.re ≤ 1 := by linarith only [hre.2, hright]
  have hi : |w.im - c.im| ≤ r := by
    simpa only [sub_im] using (abs_im_le_norm (w - c)).trans hd.le
  have ht : |w.im| ≤ 1 / 20 := by
    calc
      |w.im| ≤ |w.im - c.im| + |c.im| := by
        simpa only [sub_add_cancel] using abs_add (w.im - c.im) c.im
      _ ≤ 1 / 20 := by linarith only [hi, hheight]
  rw [neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
  exact neg_le_neg (certified_quartic_completed_low_strip_floor h₀ h₁ ht)

#print axioms certified_quartic_mellin_low_strip_floor
#print axioms certified_quartic_completed_low_strip_floor
#print axioms certified_quartic_completed_low_strip_ne_zero
#print axioms certified_quartic_completed_low_circle_sign

end QuarticKernel
