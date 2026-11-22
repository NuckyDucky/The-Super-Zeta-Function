import QuartetActualSpiral
import QuarterUnivalent
import QuartetSpiral
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace SuperZeta.QuarterOriginalUnivalent
noncomputable section
open Set Complex Real
open QuartetShiftContinuation QuartetBandCauchy QuartetActualSpiral UnitSpectrum

def strip : Set ℂ := {z | (15/64 ≤ z.re ∧ z.re ≤ 17/64) ∧ 101 ≤ z.im}

lemma strip_spec {z : ℂ} (hz : z ∈ strip) : |z.re-1/4| ≤ 1/64 ∧ 101 ≤ z.im := by
  rcases hz with ⟨⟨hl,hr⟩,ht⟩
  exact ⟨abs_le.mpr ⟨by linarith [show 15/64 ≤ z.re from hl],
    by linarith [show z.re ≤ 17/64 from hr]⟩,ht⟩

lemma strip_convex : Convex ℝ strip :=
  ((convex_halfSpace_re_ge _).inter (convex_halfSpace_re_le _)).inter (convex_halfSpace_im_ge _)

theorem lifted_injective : InjOn lifted strip := by
  apply QuarterUnivalent.injOn_of_deriv_re_neg strip_convex
  · intro z hz
    exact (lifted_deriv (strip_spec hz).1 (strip_spec hz).2).differentiableAt
  · intro z hz
    rw [(lifted_deriv (strip_spec hz).1 (strip_spec hz).2).deriv]
    have H : OuterBound := fun _ hl hr ht => (QuartetBandDominance.band_relative_error hl hr ht).le
    linarith [log_slope H (strip_spec hz).1 (strip_spec hz).2]

def correction (z : ℂ) := Complex.log (continuation z / leading z)

lemma correction_small {z : ℂ} (hz : z ∈ strip) : ‖correction z‖ ≤ 3/256 := by
  have H : OuterBound := fun _ hl hr ht => (QuartetBandDominance.band_relative_error hl hr ht).le
  have he := error_small H (strip_spec hz).1 (strip_spec hz).2
  have h := Complex.norm_log_one_add_half_le_self (z:=error z) (by linarith)
  have ee : 1 + error z = continuation z / leading z := by unfold error; ring
  rw [ee] at h
  dsimp [correction]; linarith

/-- Equal log-radii in this narrow strip force a small imaginary increment
in the logarithmic lift. The angular increment cannot conceal a whole turn. -/
private theorem no_extra_turn {a b dx dy er ei : ℝ} (ha : 0 ≤ a) (hA : a ≤ 3)
    (hb : 5/8 ≤ b) (hB : b ≤ 2) (hdx : |dx| ≤ 1/32)
    (he : |er| ≤ 3/128) (hi : |ei| ≤ 3/128)
    (hzero : -2*dx*a + 2*dy*b + er = 0) :
    |-2*dx*b-2*dy*a + ei| < 2 := by
  have xa : |2*dx*a| ≤ 3/16 := by
    calc
      _ = 2*|dx| *a := by simp [abs_mul,abs_of_nonneg ha]
      _ ≤ 2*(1/32)*3 := by gcongr
      _ = _ := by norm_num
  have yb : |2*dy*b| ≤ 27/128 := by
    rw [show 2*dy*b = 2*dx*a - er by linarith]
    linarith [abs_sub (2*dx*a) er]
  have bp : 0 ≤ b := by linarith
  rw [abs_mul,abs_mul,abs_of_nonneg bp] at yb
  norm_num at yb
  have dyb : |dy| ≤ 1/4 := by nlinarith [mul_nonneg (abs_nonneg dy) (sub_nonneg.mpr hb)]
  have xb : |-2*dx*b| ≤ 1/8 := by
    calc
      _ = 2*|dx| *b := by simp [abs_mul,abs_of_nonneg bp]
      _ ≤ 2*(1/32)*2 := by gcongr
      _ = _ := by norm_num
  have ya : |2*dy*a| ≤ 3/2 := by
    calc
      _ = 2*|dy| *a := by simp [abs_mul,abs_of_nonneg ha]
      _ ≤ 2*(1/4)*3 := by gcongr
      _ = _ := by norm_num
  linarith [abs_add_le (-2*dx*b-2*dy*a) ei,abs_sub (-2*dx*b) (2*dy*a)]

/-- The actual continued spectral zeta takes a different complex value at
every two distinct inputs in this entire unbounded strip. -/
theorem continuation_injective : InjOn continuation strip := by
  intro x hx y hy hxy
  let A := Complex.log (upper 0)
  let d := x-y
  let C := correction x - correction y
  have H : lifted x - lifted y = -2*d*A+C := by
    dsimp [d,A,C,correction,lifted]; ring
  have rex : (lifted x).re = (lifted y).re := by
    rw [← log_radius (strip_spec hx).1 (strip_spec hx).2,
      ← log_radius (strip_spec hy).1 (strip_spec hy).2,hxy]
  have hre : -2*d.re*A.re + 2*d.im*A.im + C.re = 0 := by
    have h := congrArg Complex.re H
    simp [Complex.sub_re,Complex.mul_re,Complex.mul_im,rex] at h
    linarith
  have him : (lifted x - lifted y).im = -2*d.re*A.im-2*d.im*A.re+C.im := by
    rw [H]
    simp [Complex.mul_re,Complex.mul_im]; ring
  have ha : 0 ≤ A.re := by
    rw [show A.re = Real.log ‖upper 0‖ from Complex.log_re _]
    exact Real.log_nonneg QuartetSpiral.norm_first_gt_one.le
  have hA : A.re ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show 0<‖upper 0‖ from (zero_lt_one.trans QuartetSpiral.norm_first_gt_one))
    have hn : ‖upper 0‖ < 4 := QuartetLeading.bounds.2
    change (Complex.log _).re ≤ _
    rw [Complex.log_re]; linarith
  have hb : 5/8 ≤ A.im := by
    rw [show A.im = (upper 0).arg from Complex.log_im _]
    exact QuartetLeading.bounds.1.le
  have hB : A.im ≤ 2 := by
    have h := Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (upper_re_pos 0))
    rw [show A.im = (upper 0).arg from Complex.log_im _]
    linarith [Real.pi_lt_four]
  have hdx : |d.re| ≤ 1/32 := by
    obtain ⟨⟨xl,xr⟩,_⟩ := hx
    obtain ⟨⟨yl,yr⟩,_⟩ := hy
    change 15/64 ≤ x.re at xl
    change x.re ≤ 17/64 at xr
    change 15/64 ≤ y.re at yl
    change y.re ≤ 17/64 at yr
    exact abs_le.mpr ⟨by change _ ≤ x.re-y.re; linarith,by change x.re-y.re ≤ _; linarith⟩
  have hC : ‖C‖ ≤ 3/128 := by
    linarith [norm_sub_le (correction x) (correction y),correction_small hx,correction_small hy,
      show C = correction x - correction y from rfl]
  have hsmall := no_extra_turn ha hA hb hB hdx ((Complex.abs_re_le_norm C).trans hC)
    ((Complex.abs_im_le_norm C).trans hC) hre
  rw [← him] at hsmall
  have same : Complex.exp (lifted x - lifted y) = Complex.exp 0 := by
    rw [Complex.exp_zero,← Complex.exp_eq_exp_iff_exp_sub_eq_one,
      lifted_exp (strip_spec hx).1 (strip_spec hx).2,
      lifted_exp (strip_spec hy).1 (strip_spec hy).2,hxy]
  have cleared := Complex.exp_inj_of_neg_pi_lt_of_le_pi (lt_trans
      (by linarith [Real.pi_gt_three] : -Real.pi < -2) (abs_lt.mp hsmall).1)
    (le_trans (abs_lt.mp hsmall).2.le (by linarith [Real.pi_gt_three]))
    (by simpa using (neg_lt_zero.mpr Real.pi_pos))
    (by simpa using Real.pi_pos.le) same
  exact lifted_injective hx hy (sub_eq_zero.mp cleared)

end
end SuperZeta.QuarterOriginalUnivalent
