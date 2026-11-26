import NativeDottieMellinFinite
import MellinStripQuadrature

/-! The rounded sample is zero on the outer part of the fixed Mellin partition. -/

noncomputable section

namespace DottieOriented.NativeSpectrum

private def realRatio (x : ℝ) : ℝ :=
  4*x*Real.sinh x/(3+4*(Real.sinh x^2+x^2))

private theorem ratio_nonneg_le_half {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ realRatio x ∧ realRatio x ≤ 1/2 := by
  have hs : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.mpr hx
  have hd : 0 < 3+4*(Real.sinh x^2+x^2) := by positivity
  unfold realRatio
  exact ⟨by positivity, (div_le_iff₀ hd).mpr (by nlinarith only [sq_nonneg (x-Real.sinh x)])⟩

private theorem abs_finiteLogGap_le_ratio {x : ℝ} (hx : 0 ≤ x) :
    |finiteLogGap x| ≤ 3*realRatio x := by
  obtain ⟨hq0, hq1⟩ := ratio_nonneg_le_half hx
  let q := realRatio x
  have hm : 0 < 1-q := by dsimp only [q]; linarith only [hq1]
  have hp : 0 < 1+q := by dsimp only [q]; linarith only [hq0]
  let a : ℝ := 3+4*(Real.sinh x^2+x^2)
  let b : ℝ := 4*x*Real.sinh x
  have ha : a ≠ 0 := by dsimp only [a]; positivity
  have hdiv : (a-b)/(a+b) = (1-q)/(1+q) := by
    change (a-b)/(a+b) = (1-b/a)/(1+b/a)
    rw [show (1-b/a)=(a-b)/a by field_simp, show (1+b/a)=(a+b)/a by field_simp,
      div_div_div_cancel_right₀ ha]
  have hpos : Real.log (1+q) ≤ q := by
    have h := Real.log_le_sub_one_of_pos hp
    linarith only [h]
  have hneg : -Real.log (1-q) ≤ 2*q := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hm)
    rw [Real.log_inv, show (1-q)⁻¹ - 1 = q/(1-q) by field_simp] at h
    refine h.trans ((div_le_iff₀ hm).mpr ?_)
    have hm' : 1/2 ≤ 1-q := by dsimp only [q]; linarith only [hq1]
    have hq' : 0 ≤ q := hq0
    nlinarith only [mul_le_mul_of_nonneg_right hm' hq']
  have hlog : Real.log (1-q)-Real.log (1+q) ≤ 0 := by
    have hq' : 0 ≤ q := hq0
    have hm' := Real.log_nonpos hm.le (by linarith only [hq'] : 1-q ≤ 1)
    have hp' := Real.log_nonneg (by linarith only [hq'] : 1 ≤ 1+q)
    linarith only [hm',hp']
  rw [finiteLogGap_eq]
  change |Real.log ((a-b)/(a+b))| ≤ _
  rw [hdiv, Real.log_div hm.ne' hp.ne', abs_of_nonpos hlog]
  linarith only [hpos,hneg]

private theorem abs_zeroDensity_le (b : Bool) (u : ℝ) :
    |finiteCoefficientDensity b 0 u| ≤ Real.exp (-u/2)*|finiteLogGap (Real.exp u)| := by
  have hc : |Real.cos (7067363/500000*u)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hs : |-Real.sin (7067363/500000*u)| ≤ 1 := by
    rw [abs_neg]
    exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  cases b
  · simp only [finiteCoefficientDensity, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, one_mul, Bool.false_eq_true, if_false, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans_eq (mul_one _)
  · simp only [finiteCoefficientDensity, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, one_mul, if_true, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans_eq (mul_one _)

private theorem sinh_le_two_mul {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    Real.sinh x ≤ 2*x := by
  have hc (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) : ‖deriv Real.sinh t‖ ≤ 2 := by
    rw [Real.deriv_sinh, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _), Real.cosh_eq]
    have he := Real.exp_le_exp.mpr ht.2
    have he' := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1)
    linarith only [he,he',Real.exp_one_lt_d9]
  have ht := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => Real.differentiable_sinh t) hc (convex_Icc (0:ℝ) 1)
    (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num) (show x ∈ Set.Icc 0 1 from ⟨hx,h1⟩)
  simpa only [Real.sinh_zero, sub_zero, Real.norm_eq_abs, abs_of_nonneg hx,
    abs_of_nonneg (Real.sinh_nonneg_iff.mpr hx)] using ht

theorem left_zeroDensity_enclosure (b : Bool) {u : ℝ} (hu : u ≤ -23) :
    |finiteCoefficientDensity b 0 u| ≤ 1/10^14 := by
  let x := Real.exp u
  have hx : 0 ≤ x := (Real.exp_pos _).le
  have hx1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hu])
  have hq : realRatio x ≤ (8/3)*x^2 := by
    have hd : 0 < 3+4*(Real.sinh x^2+x^2) := by positivity
    rw [realRatio, div_le_iff₀ hd]
    have hb := mul_le_mul_of_nonneg_left (sinh_le_two_mul hx hx1) (show 0 ≤ 4*x by positivity)
    have hn := mul_nonneg (sq_nonneg x) (add_nonneg (sq_nonneg (Real.sinh x)) (sq_nonneg x))
    nlinarith only [hb,hn]
  have hlog := (abs_finiteLogGap_le_ratio hx).trans (show 3*realRatio x ≤ 8*x^2 by linarith only [hq])
  have he : 8*Real.exp (-(69/2)) ≤ (1:ℝ)/10^14 := by
    have hlo : (271/100:ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have h69 : (271/100:ℝ)^69 ≤ Real.exp 69 := by
      rw [show (69:ℝ) = ((69:ℕ):ℝ)*1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) hlo _
    have hsq : ((8:ℝ)*10^14)^2 ≤ (Real.exp (69/2))^2 := by
      rw [pow_two (Real.exp (69/2)), ← Real.exp_add, show (69/2:ℝ)+69/2 = 69 by norm_num]
      exact (show ((8:ℝ)*10^14)^2 ≤ (271/100)^69 by norm_num).trans h69
    have hl := (sq_le_sq₀ (by norm_num) (Real.exp_pos (69/2)).le).mp hsq
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith only [hl]
  calc
    _ ≤ Real.exp (-u/2)*|finiteLogGap (Real.exp u)| := abs_zeroDensity_le b u
    _ ≤ Real.exp (-u/2)*(8*(Real.exp u)^2) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = 8*Real.exp (3*u/2) := by
      rw [pow_two, mul_left_comm, ← mul_assoc (Real.exp (-u/2)), ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ 8*Real.exp (-(69/2)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hu])) (by norm_num)
    _ ≤ _ := he

private theorem ratio_le_exp_tail {x : ℝ} (hx : 50 ≤ x) :
    realRatio x ≤ 4*x*Real.exp (-x) := by
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr (by linarith only [hx])
  have hsq : 4*Real.sinh x^2 ≤ 3+4*(Real.sinh x^2+x^2) := by
    nlinarith only [sq_nonneg x]
  have hr : realRatio x ≤ x/Real.sinh x := by
    rw [realRatio, div_le_div_iff₀ (by positivity : 0 < 3+4*(Real.sinh x^2+x^2)) hs]
    nlinarith only [mul_le_mul_of_nonneg_left hsq hx0]
  have hS : Real.exp x / 4 ≤ Real.sinh x := by
    have hE : Real.exp (-x) ≤ Real.exp x / 2 := by
      rw [le_div_iff₀ (show (0:ℝ) < 2 by norm_num)]
      refine le_of_mul_le_mul_right ?_ (Real.exp_pos x)
      rw [show Real.exp (-x)*2*Real.exp x = 2*(Real.exp (-x)*Real.exp x) by ring,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, ← Real.exp_add]
      linarith only [Real.add_one_le_exp (x+x),hx]
    rw [Real.sinh_eq]
    linarith only [hE]
  refine hr.trans ((div_le_iff₀ hs).mpr ?_)
  calc
    x = (4*x*Real.exp (-x))*(Real.exp x/4) := by
      rw [show (4*x*Real.exp (-x))*(Real.exp x/4) = x*(Real.exp (-x)*Real.exp x) by ring,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_left hS (by positivity)

theorem right_zeroDensity_enclosure (b : Bool) {u : ℝ} (hu : 4 ≤ u) :
    |finiteCoefficientDensity b 0 u| ≤ 1/10^14 := by
  let x := Real.exp u
  have he1 : (27/10:ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have he4 : 50 ≤ Real.exp 4 := by
    rw [show (4:ℝ) = ((4:ℕ):ℝ)*1 by norm_num, Real.exp_nat_mul]
    exact (show (50:ℝ) ≤ (27/10)^4 by norm_num).trans (pow_le_pow_left₀ (by norm_num) he1 _)
  have hx : 50 ≤ x := he4.trans (Real.exp_le_exp.mpr hu)
  have hx0 : 0 ≤ x := (Real.exp_pos _).le
  have hex : x*Real.exp (-x) ≤ 50*Real.exp (-50) := by
    have hc : x ≤ 50*Real.exp (x-50) := by linarith only [Real.add_one_le_exp (x-50),hx]
    calc
      _ ≤ (50*Real.exp (x-50))*Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = _ := by rw [mul_assoc, ← Real.exp_add, show x-50 + -x = -50 by ring]
  have hlim : 600*Real.exp (-50) ≤ (1:ℝ)/10^14 := by
    have h50 : (27/10:ℝ)^50 ≤ Real.exp 50 := by
      rw [show (50:ℝ) = ((50:ℕ):ℝ)*1 by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) he1 _
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith only [h50, show (600:ℝ)*10^14 ≤ (27/10)^50 by norm_num]
  calc
    _ ≤ Real.exp (-u/2)*|finiteLogGap (Real.exp u)| := abs_zeroDensity_le b u
    _ ≤ 1*|finiteLogGap (Real.exp u)| :=
      mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith only [hu])) (abs_nonneg _)
    _ ≤ 3*realRatio x := by simpa only [one_mul] using abs_finiteLogGap_le_ratio hx0
    _ ≤ 600*Real.exp (-50) := by
      have ht := ratio_le_exp_tail hx
      nlinarith only [ht, hex]
    _ ≤ _ := hlim

open SuperZeta.CauchyPanelQuadrature

theorem left_node_zero_enclosure (b : Bool) {i : ℕ} (hi : i < 576) (j : Fin 25) :
    |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ)| ≤ 1/10^14 := by
  have hi' : (i:ℝ) ≤ 575 := by exact_mod_cast Nat.le_of_lt_succ hi
  have hnode : |(node j:ℝ)| ≤ 1 := by exact_mod_cast (rule_certified.1 j).1
  apply left_zeroDensity_enclosure
  norm_num [mellinPanelNode, mellinPanelCenter]
  linarith only [hi',(abs_le.mp hnode).2]

theorem right_node_zero_enclosure (b : Bool) {i : ℕ} (hi : 2304 ≤ i) (j : Fin 25) :
    |finiteCoefficientDensity b 0 (mellinPanelNode i j:ℝ)| ≤ 1/10^14 := by
  have hi' : (2304:ℝ) ≤ i := by exact_mod_cast hi
  have hnode : |(node j:ℝ)| ≤ 1 := by exact_mod_cast (rule_certified.1 j).1
  apply right_zeroDensity_enclosure
  norm_num [mellinPanelNode, mellinPanelCenter]
  linarith only [hi',(abs_le.mp hnode).1]

#print axioms left_zeroDensity_enclosure
#print axioms right_zeroDensity_enclosure
#print axioms left_node_zero_enclosure
#print axioms right_node_zero_enclosure

end DottieOriented.NativeSpectrum
end
