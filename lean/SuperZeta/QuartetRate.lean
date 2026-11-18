import SuperZeta.QuartetRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! A summable rate for the logarithmic radial correction. -/
namespace SuperZeta.QuartetRadius

open Real Filter
open scoped Topology
noncomputable section

private theorem exp_neg_le_half {t : ℝ} (ht : 1≤t) : exp (-t) ≤ 1/2 := by
  rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
  linarith [add_one_le_exp t]

private theorem a_bound {t : ℝ} (ht : 1≤t) :
    0 ≤ a t ∧ a t ≤ 4*t*exp (-t) := by
  have hpos : 0<t := by linarith
  have he := exp_neg_le_half ht
  have hd : 1/2 ≤ 1-exp (-t)^2 := by nlinarith [exp_pos (-t)]
  rw [a_rescaled hpos]
  constructor
  · exact div_nonneg (by positivity) (by linarith)
  · rw [div_le_iff₀ (show 0<1-exp (-t)^2 by linarith)]
    nlinarith [mul_le_mul_of_nonneg_left hd (show 0≤4*t*exp (-t) by positivity)]

private theorem level_distance {t : ℝ} (ht : 1≤t) :
    |level t-exp t| ≤ (4*π*t+16*t^2+1)*exp (-t) := by
  have hpos : 0<t := by linarith
  obtain ⟨ha, hb⟩ := a_bound ht
  have ha1 : a t ≤ 1 := (div_le_one (sinh_pos_iff.mpr hpos)).mpr
    (self_le_sinh_iff.mpr hpos.le)
  have hc : cos (θ t) = -a t := cos_arccos (by linarith) (by linarith)
  have hs : 0 ≤ sin (θ t) := by rw [θ,sin_arccos]; positivity
  have hs1 := sin_le_one (θ t)
  have hsq := sin_sq_add_cos_sq (θ t)
  rw [hc, neg_sq] at hsq
  have hsin : 1-sin (θ t) ≤ a t^2 := by
    nlinarith [mul_nonneg hs (sub_nonneg.mpr hs1)]
  have hθ : θ t-π/2 = arcsin (a t) := by rw [θ, arccos, arcsin_neg]; ring
  have hs2 := mul_le_sin (arcsin_nonneg.mpr ha) (arcsin_le_pi_div_two (a t))
  rw [sin_arcsin (by linarith) ha1, div_mul_eq_mul_div, div_le_iff₀ pi_pos] at hs2
  have hangle : |2*(θ t-π/2)| ≤ 4*π*t*exp (-t) := by
    rw [hθ, abs_of_nonneg (by linarith [arcsin_nonneg.mpr ha])]
    calc
      _ ≤ π * a t := by linarith
      _ ≤ π * (4*t*exp (-t)) := mul_le_mul_of_nonneg_left hb pi_pos.le
      _ = _ := by ring
  have hdefect : |exp t*(1-sin (θ t))| ≤ 16*t^2*exp (-t) := by
    rw [abs_of_nonneg (mul_nonneg (exp_pos t).le (sub_nonneg.mpr hs1))]
    calc
      _ ≤ exp t*a t^2 := mul_le_mul_of_nonneg_left hsin (exp_pos _).le
      _ ≤ exp t*(4*t*exp (-t))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha hb 2) (exp_pos _).le
      _ = _ := by rw [exp_neg]; field_simp; ring
  have hexp : |exp (-t)*sin (θ t)| ≤ exp (-t) := by
    rw [abs_of_nonneg (mul_nonneg (exp_pos _).le hs)]
    simpa using mul_le_mul_of_nonneg_left hs1 (exp_pos (-t)).le
  have he : level t-exp t = (2*(θ t-π/2)-exp t*(1-sin (θ t)))+exp (-t)*sin (θ t) := by
    simp only [level, cosh_eq]
    ring
  rw [he]
  exact (abs_add_le _ _).trans <| (add_le_add (abs_sub _ _) le_rfl).trans
    (by linarith [hangle,hdefect,hexp])

private theorem half_exp_decay (k : ℕ) :
    Tendsto (fun t : ℝ => t^k*exp (-(t/2))) atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (Tendsto.atTop_div_const (show (0:ℝ)<2 by norm_num) tendsto_id)).const_mul ((2:ℝ)^k)
  convert h using 1
  · funext t
    simp only [Function.comp_apply, id_eq, div_pow]
    field_simp
  · simp

private theorem weighted_level :
    Tendsto (fun t : ℝ => exp (t/2)*(level t-exp t)) atTop (𝓝 0) := by
  have h := (((half_exp_decay 1).const_mul (4*π)).add
    ((half_exp_decay 2).const_mul (16:ℝ))).add (half_exp_decay 0)
  apply squeeze_zero_norm' _ (show Tendsto
    (fun t : ℝ => 4*π*(t^1*exp (-(t/2)))+16*(t^2*exp (-(t/2)))+t^0*exp (-(t/2)))
    atTop (𝓝 0) by simpa using h)
  filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
  calc
    _ ≤ exp (t/2)*((4*π*t+16*t^2+1)*exp (-t)) :=
      mul_le_mul_of_nonneg_left (level_distance ht) (exp_pos _).le
    _ = _ := by
      have he : exp (t/2)*exp (-t) = exp (-(t/2)) := by rw [← exp_add]; congr 1; ring
      rw [← he]
      ring

private lemma abs_log_close {x : ℝ} (hx : 1/2 ≤ x) : |log x| ≤ 2*|x-1| := by
  have h0 : 0<x := by linarith
  have hlo := one_sub_inv_le_log_of_pos h0
  have hhi := log_le_sub_one_of_pos h0
  have hr : (x-1)/x = 1-x⁻¹ := by field_simp [h0.ne']
  rw [← hr] at hlo
  apply abs_le.mpr
  constructor
  · apply le_trans _ hlo
    rw [le_div_iff₀ h0]
    have ha := neg_abs_le (x-1)
    have hb := mul_le_mul_of_nonneg_right hx (abs_nonneg (x-1))
    linarith
  · exact hhi.trans (by linarith [le_abs_self (x-1), abs_nonneg (x-1)])

/-- The logarithm of the relative radial correction has a summable eventual
bound. The roots of the characteristic equation can be selected arbitrarily. -/
theorem log_radial_bound {t : ℕ → ℝ}
    (roots : ∀ n, 0<n → 0<t n ∧ level (t n)=2*π*n) :
    ∀ᶠ n in atTop, |log (radius (t n)/(2*π*n))| ≤ 3*(n:ℝ)^(-(3/2:ℝ)) := by
  have hz := roots_unbounded roots
  have hnorm : Tendsto (fun n : ℕ => ‖exp (t n/2)*(level (t n)-exp (t n))‖) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (weighted_level.comp hz).norm
  have H := hnorm.eventually_lt_const (show (0:ℝ)<1 by norm_num)
  have G := ((level_error.comp hz).eventually_lt_const (show (0:ℝ)<1 by norm_num))
  have av : Tendsto (fun n : ℕ => 4*(t n*exp (-(t n/2)))) atTop (𝓝 (0:ℝ)) := by
    simpa [Function.comp_def] using (((half_exp_decay 1).const_mul (4:ℝ)).comp hz)
  filter_upwards [H, G, hz.eventually_ge_atTop 1, eventually_gt_atTop (0:ℕ),
    av.eventually_lt_const (show (0:ℝ)<1 by norm_num)] with n h g ht hn ha
  have hn0 : 0<(n:ℝ) := by positivity
  have hn1 : 1≤(n:ℝ) := by exact_mod_cast hn
  change level (t n)-exp (t n)<1 at g
  change ‖exp (t n/2)*(level (t n)-exp (t n))‖<1 at h
  rw [(roots n hn).2] at g h
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _), ← lt_div_iff₀' (exp_pos _),
    one_div, ← exp_neg] at h
  have he : (n:ℝ) ≤ exp (t n) := by
    have hp := mul_le_mul_of_nonneg_right (show 1≤2*π-1 by linarith [pi_gt_three]) hn0.le
    linarith [hn1]
  have hw : exp (t n * (-(3/2:ℝ))) ≤ (n:ℝ)^(-(3/2:ℝ)) := by
    rw [exp_mul]
    exact rpow_le_rpow_of_nonpos hn0 he (by norm_num)
  let q := (2*π*(n:ℝ))/exp (t n)
  have hq : 0<q := by dsimp [q]; positivity
  have hq1 : |q-1| ≤ exp (t n * (-(3/2:ℝ))) := by
    calc
      |q-1| = |2*π*(n:ℝ)-exp (t n)| * exp (-(t n)) := by
        dsimp only [q]
        rw [div_sub_one (exp_pos _).ne', abs_div, abs_of_pos (exp_pos _), exp_neg, div_eq_mul_inv]
      _ ≤ exp (-(t n/2))*exp (-(t n)) := mul_le_mul_of_nonneg_right h.le (exp_pos _).le
      _ = _ := by rw [← exp_add]; congr 1; ring
  have hq2 : 1/2≤q := by
    have hh : exp (t n * (-(3/2:ℝ))) ≤ 1/2 :=
      (exp_le_exp.mpr (by linarith : t n * (-(3/2:ℝ)) ≤ -(t n))).trans (exp_neg_le_half ht)
    linarith [neg_abs_le (q-1), hq1.trans hh]
  have hqlog := (abs_log_close hq2).trans (mul_le_mul_of_nonneg_left hq1 (by norm_num))
  obtain ⟨ap,ab⟩ := a_bound ht
  have ha1 : |a (t n) * exp (-(t n))| ≤ exp (t n * (-(3/2:ℝ))) := by
    rw [abs_of_nonneg (mul_nonneg ap (exp_pos _).le)]
    have ee : 4*t n*exp (-(t n)) = (4*(t n*exp (-(t n/2))))*exp (-(t n/2)) := by
      have ep : exp (-(t n/2))*exp (-(t n/2)) = exp (-(t n)) := by
        rw [← exp_add]
        congr 1
        ring
      rw [← ep]
      ring
    rw [ee] at ab
    calc
      _ ≤ ((4*(t n*exp (-(t n/2))))*exp (-(t n/2)))*exp (-(t n)) :=
        mul_le_mul_of_nonneg_right ab (exp_pos _).le
      _ ≤ (1*exp (-(t n/2)))*exp (-(t n)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha.le (exp_pos _).le)
          (exp_pos _).le
      _ = _ := by rw [one_mul, ← exp_add]; congr 1; ring
  have hd : 0 < 2*π*(n:ℝ) := by positivity
  have hid : log (radius (t n)/(2*π*n)) = a (t n)*exp (-(t n))-log q := by
    rw [log_div (by unfold radius; positivity) hd.ne', radius, log_exp,
      exponent_identity (by linarith : 0<t n)]
    dsimp [q]
    rw [log_div hd.ne' (exp_pos _).ne', log_exp]
    ring
  rw [hid]
  exact (abs_sub _ _).trans ((add_le_add ha1 hqlog).trans (by linarith))

end
end SuperZeta.QuartetRadius
