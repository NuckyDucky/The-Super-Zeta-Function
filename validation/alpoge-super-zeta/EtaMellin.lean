import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Analytic.Uniqueness

/-! The Mellin identity for eta on the positive upper quadrant. -/

noncomputable section

namespace DottieOriented.NativeSpectrum.EtaMellin

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

def eta (w : ℂ) : ℂ := (1 - (2:ℂ)^(1-w)) * riemannZeta w

def fermi (x : ℝ) : ℂ := ↑(Real.exp (-x) / (1 + Real.exp (-x)))

private def bose (x : ℝ) : ℂ := ↑(1 / (Real.exp x - 1))

theorem fermi_norm_le (x : ℝ) : ‖fermi x‖ ≤ Real.exp (-x) := by
  rw [fermi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact div_le_self (Real.exp_nonneg _) (by linarith [Real.exp_pos (-x)])

private theorem fermi_cont : Continuous fermi := by
  unfold fermi
  exact Complex.continuous_ofReal.comp ((Real.continuous_exp.comp continuous_neg).div
    (continuous_const.add (Real.continuous_exp.comp continuous_neg)) (fun x => by positivity))

private theorem fermi_top : fermi =O[atTop] (fun x : ℝ => Real.exp (-1*x)) := by
  refine isBigO_iff.mpr ⟨1, Eventually.of_forall fun x => ?_⟩
  simpa only [neg_mul, one_mul, Real.norm_eq_abs, Real.abs_exp] using fermi_norm_le x

private theorem fermi_bottom : fermi =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x ^ (-(0:ℝ))) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with x hx
  simp only [neg_zero, Real.rpow_zero, norm_one, one_mul]
  exact (fermi_norm_le x).trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mem_Ioi.mp hx).le))

theorem fermi_convergent {w : ℂ} (hw : 0 < w.re) : MellinConvergent fermi w :=
  mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ) < 1)
    (fermi_cont.continuousOn.locallyIntegrableOn measurableSet_Ioi) fermi_top fermi_bottom hw

private theorem fermi_mellin_diff {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (mellin fermi) w :=
  mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0:ℝ) < 1)
    (fermi_cont.continuousOn.locallyIntegrableOn measurableSet_Ioi) fermi_top fermi_bottom hw

private theorem bose_ratio {x : ℝ} (hx : 0 < x) :
    (1 / (Real.exp x - 1) : ℝ) = Real.exp (-x) / (1 - Real.exp (-x)) := by
  have hexp := Real.exp_pos x
  have hgt : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  rw [Real.exp_neg]
  have h1 : Real.exp x - 1 ≠ 0 := by linarith
  have h2 : 1 - (Real.exp x)⁻¹ ≠ 0 := by
    have h := inv_lt_one_of_one_lt₀ hgt
    linarith
  field_simp [hexp.ne', h1, h2]

private theorem bose_top : bose =O[atTop] (fun x : ℝ => Real.exp (-1*x)) := by
  refine isBigO_iff.mpr ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ)] with x hx
  have hx' : 0 < x := by linarith
  have hexp : 2 ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hd : Real.exp (-x) ≤ (1:ℝ)/2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hexp
  have hpos : 0 ≤ Real.exp (-x) / (1 - Real.exp (-x)) :=
    div_nonneg (Real.exp_nonneg _) (by linarith)
  rw [bose, Complex.norm_real, Real.norm_eq_abs, bose_ratio hx', abs_of_nonneg hpos]
  simp only [neg_mul, one_mul, Real.norm_eq_abs, Real.abs_exp]
  apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-x))).mpr
  nlinarith [mul_nonneg (Real.exp_pos (-x)).le (sub_nonneg.mpr hd)]

private theorem bose_bottom : bose =O[𝓝[>] (0:ℝ)] (fun x : ℝ => x ^ (-(1:ℝ))) := by
  refine isBigO_iff.mpr ⟨1, ?_⟩
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0:ℝ))] with x hx
  have hx' := mem_Ioi.mp hx
  have h : x ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
  rw [bose, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (hx'.le.trans h)),
    Real.norm_eq_abs, Real.rpow_neg_one, abs_of_nonneg (inv_nonneg.mpr hx'.le),
    one_mul, ← one_div]
  exact one_div_le_one_div_of_le hx' h

private theorem bose_convergent {w : ℂ} (hw : 1 < w.re) : MellinConvergent bose w := by
  have hb : ContinuousOn bose (Ioi 0) := by
    unfold bose
    refine Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.div (Real.continuous_exp.sub continuous_const).continuousOn ?_)
    intro x hx
    have h := Real.one_lt_exp_iff.mpr (mem_Ioi.mp hx)
    linarith
  exact mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ) < 1)
    (hb.locallyIntegrableOn measurableSet_Ioi) bose_top bose_bottom hw

private theorem bose_series {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (1:ℂ) * (Real.exp (-((n:ℝ)+1)*x):ℂ)) (bose x) := by
  have hsmall : ‖(Real.exp (-x):ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, Real.exp_lt_one_iff]
    linarith
  have h := (hasSum_geometric_of_norm_lt_one hsmall).mul_left (Real.exp (-x):ℂ)
  convert h using 1
  · funext n
    rw [one_mul, show -((n:ℝ)+1)*x = ((n+1:ℕ):ℝ)*(-x) by push_cast; ring,
      Real.exp_nat_mul, ofReal_pow, pow_succ, mul_comm]
  · rw [bose, bose_ratio hx]
    simp only [ofReal_div, ofReal_sub, ofReal_one, div_eq_mul_inv, ofReal_mul, ofReal_inv]

private theorem bose_mellin {w : ℂ} (hw : 1 < w.re) :
    mellin bose w = Complex.Gamma w * riemannZeta w := by
  have hp (n : ℕ) : (1:ℂ) = 0 ∨ 0 < (n:ℝ)+1 := Or.inr (by positivity)
  have hsum : Summable (fun n : ℕ => ‖(1:ℂ)‖ / ((n:ℝ)+1)^w.re) := by
    simpa only [norm_one, one_div, Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).mpr (Real.summable_nat_rpow_inv.mpr hw))
  have h := hasSum_mellin hp (by linarith : 0 < w.re)
    (fun _ hx => bose_series (mem_Ioi.mp hx)) hsum
  rw [← h.tsum_eq, zeta_eq_tsum_one_div_nat_add_one_cpow hw, ← tsum_mul_left]
  simp only [mul_one, mul_one_div, ofReal_add, ofReal_natCast, ofReal_one]

private theorem fermi_eq_bose {x : ℝ} (hx : 0 < x) :
    fermi x = bose x - 2*bose (2*x) := by
  have hr : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h0 : 0 < Real.exp (-x) := Real.exp_pos _
  have h1 : 1 - Real.exp (-x) ≠ 0 := by linarith
  have h2 : 1 - Real.exp (-x)^2 ≠ 0 := by nlinarith
  have h3 : 1 + Real.exp (-x) ≠ 0 := by positivity
  have h :
      Real.exp (-x) / (1 + Real.exp (-x)) =
        Real.exp (-x) / (1-Real.exp (-x)) - 2*(Real.exp (-x)^2/(1-Real.exp (-x)^2)) := by
    field_simp [h1,h2,h3]
    ring
  rw [fermi, bose, bose, bose_ratio hx, bose_ratio (by linarith : 0 < 2*x),
    show -(2*x) = (-x)+(-x) by ring, Real.exp_add, ← pow_two]
  exact_mod_cast h

private theorem mellin_sub_convergent {f g : ℝ → ℂ} {w : ℂ}
    (hf : MellinConvergent f w) (hg : MellinConvergent g w) :
    mellin (fun x => f x - g x) w = mellin f w - mellin g w := by
  simp only [mellin, smul_sub]
  exact integral_sub hf hg

private theorem fermi_mellin_right {w : ℂ} (hw : 1 < w.re) :
    mellin fermi w = Complex.Gamma w * eta w := by
  have hB := bose_convergent hw
  have hB2 := (MellinConvergent.comp_mul_left (a := (2:ℝ)) (by norm_num)).mpr hB
  calc
    mellin fermi w = mellin (fun x => bose x - (2:ℂ) • bose (2*x)) w := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
      simp only [smul_eq_mul, fermi_eq_bose (mem_Ioi.mp hx)]
    _ = mellin bose w - (2:ℂ) • mellin (fun x => bose (2*x)) w := by
      rw [mellin_sub_convergent hB (hB2.const_smul (2:ℂ)), mellin_const_smul]
    _ = Complex.Gamma w * eta w := by
      rw [mellin_comp_mul_left _ _ (by norm_num : 0 < (2:ℝ)), bose_mellin hw]
      simp only [Complex.ofReal_ofNat, smul_eq_mul, eta]
      rw [sub_eq_add_neg 1 w, Complex.cpow_add _ _ (by norm_num : (2:ℂ) ≠ 0),
        Complex.cpow_one]
      ring

private def quadrant : Set ℂ := {w | 0 < w.re ∧ 0 < w.im}

private theorem quadrant_open : IsOpen quadrant :=
  (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const continuous_im)

theorem quadrant_convex : Convex ℝ quadrant := by
  intro x hx y hy a b ha hb hab
  have hx' : 0 < x.re ∧ 0 < x.im := hx
  have hy' : 0 < y.re ∧ 0 < y.im := hy
  change 0 < (a • x + b • y).re ∧ 0 < (a • x + b • y).im
  simp only [add_re, add_im, smul_re, smul_im, smul_eq_mul]
  rcases ha.eq_or_lt with h | h
  · have hb' : 0 < b := by linarith
    rw [← h, zero_mul, zero_mul, zero_add, zero_add]
    exact ⟨mul_pos hb' hy'.1, mul_pos hb' hy'.2⟩
  · exact ⟨add_pos_of_pos_of_nonneg (mul_pos h hx'.1) (mul_nonneg hb hy'.1.le),
      add_pos_of_pos_of_nonneg (mul_pos h hx'.2) (mul_nonneg hb hy'.2.le)⟩

private theorem eta_diff_at {w : ℂ} (hw : w ≠ 1) : DifferentiableAt ℂ eta w := by
  unfold eta
  have hA : Differentiable ℂ (fun z : ℂ => 1 - (2:ℂ)^(1-z)) := by
    simp only [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0)]
    fun_prop
  exact hA.differentiableAt.mul (differentiableAt_riemannZeta hw)

theorem mellin_fermi_eq_gamma_eta {w : ℂ} (hr : 0 < w.re) (hi : 0 < w.im) :
    mellin fermi w = Complex.Gamma w * eta w := by
  have hM : AnalyticOnNhd ℂ (mellin fermi) quadrant := by
    have hD : DifferentiableOn ℂ (mellin fermi) quadrant :=
      fun _ hz => (fermi_mellin_diff hz.1).differentiableWithinAt
    exact fun _ hz => hD.analyticAt (quadrant_open.mem_nhds hz)
  have hG : AnalyticOnNhd ℂ (fun z => Complex.Gamma z * eta z) quadrant := by
    have hD : DifferentiableOn ℂ (fun z => Complex.Gamma z * eta z) quadrant := by
      intro z hz
      have hz' : 0 < z.re ∧ 0 < z.im := hz
      have hp : z ≠ 1 := by intro he; simpa [he] using hz'.2
      have hg : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z (by
        intro n he
        have h0 := hz'.1
        rw [he, neg_re, natCast_re] at h0
        linarith [show 0 ≤ (n:ℝ) by positivity])
      exact (hg.mul (eta_diff_at hp)).differentiableWithinAt
    exact fun _ hz => hD.analyticAt (quadrant_open.mem_nhds hz)
  have hz₀ : (2+I:ℂ) ∈ quadrant := by norm_num [quadrant]
  have hEq : mellin fermi =ᶠ[𝓝 (2+I:ℂ)] (fun z => Complex.Gamma z * eta z) := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds
      (show 1 < (2+I:ℂ).re by norm_num)] with z hz
    exact fermi_mellin_right hz
  exact hM.eqOn_of_preconnected_of_eventuallyEq hG quadrant_convex.isPreconnected hz₀ hEq ⟨hr,hi⟩

#print axioms mellin_fermi_eq_gamma_eta

end DottieOriented.NativeSpectrum.EtaMellin
end
