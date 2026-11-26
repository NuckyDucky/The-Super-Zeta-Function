import EtaMellin

/-! Error of a finite geometric expansion under the eta Mellin integral. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.EtaMellin

open Complex Set MeasureTheory

def ratio (x : ℝ) : ℝ := (1 - Real.exp (-x))/2

def fermiPartial (n : ℕ) (x : ℝ) : ℂ :=
  ↑(Real.exp (-x)/2 * ∑ k ∈ Finset.range n, (ratio x)^k)

private def fermiTail (n : ℕ) (x : ℝ) : ℂ := (ratio x)^n • fermi x

private theorem fermi_split (n : ℕ) (x : ℝ) :
    fermi x = fermiPartial n x + fermiTail n x := by
  have geom (v : ℝ) (m : ℕ) : (1-v)*(∑ k ∈ Finset.range m, v^k)+v^m = 1 := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, pow_succ, mul_add]
      linarith only [ih, show (1-v)*v^m+v^m*v = v^m by ring]
  have hf : (1-ratio x) * (Real.exp (-x)/(1+Real.exp (-x))) = Real.exp (-x)/2 := by
    unfold ratio
    field_simp [show 1 + Real.exp (-x) ≠ 0 by positivity]
    ring
  simp only [fermi, fermiTail, fermiPartial, Complex.real_smul, ← ofReal_mul, ← ofReal_add]
  apply congrArg Complex.ofReal
  rw [← hf, mul_assoc, mul_comm (Real.exp (-x)/(1+Real.exp (-x))),
    ← mul_assoc, ← add_mul, geom, one_mul]

private theorem norm_tail_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ‖fermiTail n x‖ ≤ (1/2:ℝ)^n * Real.exp (-x) := by
  have h0 : 0 ≤ ratio x :=
    div_nonneg (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.le))) (by norm_num)
  have h1 : ratio x ≤ 1/2 := by unfold ratio; linarith [Real.exp_pos (-x)]
  rw [fermiTail, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _)]
  exact mul_le_mul (pow_le_pow_left₀ h0 h1 n) (fermi_norm_le x)
    (norm_nonneg _) (by positivity)

private theorem tail_continuous (n : ℕ) : Continuous (fermiTail n) := by
  have h : Continuous fermi := by
    unfold fermi
    exact Complex.continuous_ofReal.comp ((Real.continuous_exp.comp continuous_neg).div
      (continuous_const.add (Real.continuous_exp.comp continuous_neg)) (fun x => by positivity))
  unfold fermiTail
  exact ((by unfold ratio; fun_prop : Continuous ratio).pow n).smul h

theorem mellin_fermi_remainder_bound (n : ℕ) {w : ℂ} (hw : 0 < w.re) :
    ‖mellin fermi w - mellin (fermiPartial n) w‖ ≤ (1/2:ℝ)^n * Real.Gamma w.re := by
  let F (x : ℝ) : ℂ := (x:ℂ) ^ (w-1) • fermiTail n x
  let bound (x : ℝ) : ℝ := (1/2:ℝ)^n * (Real.exp (-x)*x^(w.re-1))
  have hm : IntegrableOn bound (Ioi 0) :=
    (Real.GammaIntegral_convergent hw).const_mul _
  have hF : ContinuousOn F (Ioi 0) := by
    apply ContinuousOn.smul _ (tail_continuous n).continuousOn
    apply continuousOn_of_forall_continuousAt
    intro x hx
    exact (continuousAt_cpow_const (ofReal_mem_slitPlane.mpr (mem_Ioi.mp hx))).comp
      continuous_ofReal.continuousAt
  have hbound : ∀ᵐ x : ℝ ∂volume.restrict (Ioi 0), ‖F x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0:ℝ)))] with x hx
    have hh := norm_tail_le n (mem_Ioi.mp hx)
    simp only [F, norm_smul, norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hx), sub_re, one_re]
    exact (mul_le_mul_of_nonneg_left hh
      (Real.rpow_nonneg (mem_Ioi.mp hx).le _)).trans_eq (by dsimp [bound]; ring)
  have ht : IntegrableOn F (Ioi 0) :=
    hm.mono' (hF.aestronglyMeasurable measurableSet_Ioi) hbound
  have hInt : (∫ x in Ioi 0, F x) =
      mellin fermi w - mellin (fermiPartial n) w := by
    have hf := fermi_convergent hw
    have he : Set.EqOn
        (fun x : ℝ => (x:ℂ) ^ (w-1) • fermi x - F x)
        (fun x : ℝ => (x:ℂ) ^ (w-1) • fermiPartial n x) (Ioi 0) := by
      intro x _
      change (x:ℂ)^(w-1) • fermi x - F x = (x:ℂ)^(w-1) • fermiPartial n x
      conv_lhs => rw [fermi_split n x]
      simp only [F, smul_add, add_sub_cancel_right]
    rw [mellin, mellin, ← setIntegral_congr_fun measurableSet_Ioi he, integral_sub hf ht,
      sub_sub_cancel]
  rw [← hInt]
  calc
    _ ≤ ∫ x in Ioi 0, bound x := norm_integral_le_of_norm_le hm hbound
    _ = _ := by rw [show (fun x => bound x) = fun x => (1/2:ℝ)^n *
        (Real.exp (-x)*x^(w.re-1)) by rfl, integral_const_mul, Real.Gamma_eq_integral hw]

def etaPartial (n : ℕ) (w : ℂ) : ℂ := mellin (fermiPartial n) w / Complex.Gamma w

theorem eta_remainder_bound (n : ℕ) {w : ℂ} (hr : 0 < w.re) (hi : 0 < w.im) :
    ‖eta w - etaPartial n w‖ ≤ (1/2:ℝ)^n * Real.Gamma w.re / ‖Complex.Gamma w‖ := by
  have hg := Complex.Gamma_ne_zero_of_re_pos hr
  have hm := mellin_fermi_remainder_bound n hr
  rw [mellin_fermi_eq_gamma_eta hr hi, mul_comm] at hm
  unfold etaPartial
  rw [← mul_div_cancel_right₀ (eta w) hg, ← sub_div, norm_div]
  exact div_le_div_of_nonneg_right hm (norm_nonneg _)

#print axioms mellin_fermi_remainder_bound
#print axioms eta_remainder_bound

end DottieOriented.NativeSpectrum.EtaMellin
end
