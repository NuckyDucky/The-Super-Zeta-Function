import SuperZeta.QuarterLine.QuartetShiftBounds

namespace SuperZeta.QuartetShiftBounds
noncomputable section
open RootBounds QuartetRadius Real Complex Set
open scoped ComplexConjugate

/-- Both conjugate coordinates satisfy the same path-length estimate to the nth real reference. -/
theorem span {n : ℕ} {t : ℝ} {z : ℂ} (hn : 2 ≤ n) (ht : 0<t)
    (he : level t = 2*π*n) (hre : z.re=x t) (him : |z.im|=t) :
    ‖z - ((π*n:ℝ):ℂ)‖ ≤ 4 + Real.log n := by
  have hn' : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  obtain ⟨h₁,h₂⟩ := horizontal_strip ht he
  have hx : 0 < x t := lt_of_lt_of_le hn' (x_lower (by omega : 0<n) he)
  have hg : Real.log (3*π) ≤ 12/5 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h := Real.sum_le_exp_of_nonneg (by norm_num : 0 ≤ (12/5:ℝ)) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith [Real.pi_lt_d2]
  have hlog := Real.log_le_log (show 0<3*x t by positivity) (show 3*x t ≤ 3*π*n by linarith)
  rw [Real.log_mul (by positivity) hn'.ne'] at hlog
  have h := Complex.norm_le_abs_re_add_abs_im (z-((π*n:ℝ):ℂ))
  simp only [sub_re,sub_im, ofReal_re, ofReal_im, sub_zero,hre, him, abs_of_nonpos (sub_nonpos.mpr h₂)] at h
  linarith [height_le_log hn ht he, Real.pi_lt_d2]

/-- A real comparison point and an endpoint in the angular sector determine a
segment on which every principal complex power has an explicit derivative bound. -/
theorem variation {s z : ℂ} {n : ℕ} (hn : 0<n) (hs : 0 ≤ s.re)
    (hz : (n:ℝ) ≤ z.re) (hangle : |z.im| ≤ 11/20*z.re) :
    ‖z^(-2*s) - ((π*n:ℝ):ℂ)^(-2*s)‖ ≤
      2*‖s‖ * (n:ℝ)^(-2*s.re-1) * Real.exp (11/10*|s.im|) * ‖z-((π*n:ℝ):ℂ)‖ := by
  let r : ℂ := ((π*n:ℝ):ℂ)
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hr : (n:ℝ) ≤ r.re := by
    change (n:ℝ) ≤ π*n
    nlinarith only [mul_nonneg (show 0≤π-1 by linarith [Real.pi_gt_three]) hn'.le]
  have geometry {w : ℂ} (hw : w ∈ segment ℝ r z) :
      (n:ℝ) ≤ w.re ∧ |w.arg| ≤ (11/20:ℝ) := by
    obtain ⟨a,b,ha,hb,hab,rfl⟩ := hw
    have hreal : (n:ℝ) ≤ a*r.re + b*z.re := by
      nlinarith only [mul_le_mul_of_nonneg_left hr ha, mul_le_mul_of_nonneg_left hz hb,
        congrArg (fun y : ℝ => y*n) hab]
    have hrz : (a • r+b • z).re=a*r.re+b*z.re := by simp [smul_re]
    refine ⟨by rwa [hrz], arg_bound_of_slope (by rw [hrz]; linarith) ?_⟩
    simp only [add_im, smul_im, r, ofReal_im, smul_eq_mul, mul_zero, zero_add, abs_mul, abs_of_nonneg hb, hrz]
    have hpos : 0 ≤ a*(π*n) := by positivity
    change _ ≤ 11/20 * (a*(π*n)+b*z.re)
    nlinarith only [hpos, mul_le_mul_of_nonneg_left hangle hb]
  have slit {w : ℂ} (hw : w ∈ segment ℝ r z) : w ∈ slitPlane := Or.inl (hn'.trans_le (geometry hw).1)
  apply Convex.norm_image_sub_le_of_norm_deriv_le (𝕜:=ℂ) (s:=segment ℝ r z)
    (fun w hw => (Complex.hasStrictDerivAt_cpow_const (c:=-2*s) (slit hw)).differentiableAt)
    _ (convex_segment _ _) (left_mem_segment ..) (right_mem_segment ..)
  intro w hw
  rw [Complex.deriv_cpow_const (slit hw), norm_mul, norm_mul, norm_neg]
  norm_num only [Complex.norm_ofNat]
  obtain ⟨hwre,hwarg⟩ := geometry hw
  have hw0 : w ≠ 0 := by intro e; simp [e] at hwre; linarith
  rw [Complex.norm_cpow_of_ne_zero hw0, div_eq_mul_inv, ← Real.exp_neg]
  have pre : (-2*s-1).re = -2*s.re-1 := by simp [mul_re]
  have pim : (-2*s-1).im = -2*s.im := by simp [mul_im]
  rw [pre,pim, mul_assoc (2*‖s‖)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul (Real.rpow_le_rpow_of_nonpos hn' (hwre.trans (re_le_norm w)) (by linarith)) _ (by positivity) (by positivity)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hwarg (abs_nonneg s.im)
  rw [← abs_mul] at h
  linarith only [le_abs_self (w.arg*s.im),h]

theorem endpoint_variation {s z : ℂ} {n : ℕ} {t : ℝ} (hn : 2≤n) (hs : 0≤s.re)
    (ht : 0<t) (he : level t=2*π*n) (hre : z.re=x t) (him : |z.im|=t) :
    ‖z^(-2*s) - ((π*n:ℝ):ℂ)^(-2*s)‖ ≤
      2*‖s‖ * (n:ℝ)^(-2*s.re-1) * Real.exp (11/10*|s.im|) * (4+Real.log n) := by
  have h0 : 0<n := by omega
  have hv := variation (z:=z) h0 hs (by rw [hre]; exact x_lower h0 he)
    (by rw [him,hre]; exact (slope_bound hn ht he).le)
  exact hv.trans (mul_le_mul_of_nonneg_left (span hn ht he hre him) (by positivity))

end
end SuperZeta.QuartetShiftBounds
