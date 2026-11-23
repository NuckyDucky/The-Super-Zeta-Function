import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped ComplexConjugate Interval

namespace QuarticModel

private theorem hasDerivAt_add_ofReal (z : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => z + (y : ℂ)) 1 x := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := x)).const_add z

/-- Projecting the error along its own direction preserves the real trapezoid constant. -/
theorem log_trapezoid_one_bound {z : ℂ} {a : ℝ} (ha : 0 < z.re + a) :
    ‖(Complex.log (z + (a : ℂ)) + Complex.log (z + ((a + 1 : ℝ) : ℂ))) / 2 -
        (∫ x : ℝ in a..a + 1, Complex.log (z + (x : ℂ)))‖ ≤
      1 / (12 * ‖z + (a : ℂ)‖ ^ 2) := by
  let f (x : ℝ) := Complex.log (z + (x : ℂ))
  let J := [[a, a + 1]]
  let error := (f a + f (a + 1)) / 2 - ∫ x in a..a + 1, f x
  let d := ‖z + (a : ℂ)‖ ^ 2
  have hd : 0 < d := by
    have hz : z + (a : ℂ) ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
      exact ha.ne' hr
    exact pow_pos (norm_pos_iff.mpr hz) 2
  change ‖error‖ ≤ 1 / (12 * d)
  by_cases he : error = 0
  · rw [he, norm_zero]
    positivity
  have hJ : J = Icc a (a + 1) := uIcc_of_le (by linarith)
  have hleft {x : ℝ} (hx : x ∈ J) : a ≤ x := by
    rw [hJ] at hx
    exact hx.1
  have hpos {x : ℝ} (hx : x ∈ J) : 0 < (z + (x : ℂ)).re := by
    simpa only [Complex.add_re, Complex.ofReal_re] using
      ha.trans_le (add_le_add (le_refl z.re) (hleft hx))
  have hnormSq {x : ℝ} (hx : x ∈ J) : d ≤ ‖z + (x : ℂ)‖ ^ 2 := by
    have h := pow_le_pow_left₀ ha.le (add_le_add (le_refl z.re) (hleft hx)) 2
    dsimp [d]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero]
    simpa only [pow_two] using add_le_add h (le_refl (z.im * z.im))
  have hf {x : ℝ} (hx : x ∈ J) : HasDerivAt f (z + (x : ℂ))⁻¹ x := by
    simpa only [f, one_div] using
      (hasDerivAt_add_ofReal z x).clog_real (Complex.mem_slitPlane_iff.mpr (Or.inl (hpos hx)))
  have hInv {x : ℝ} (hx : x ∈ J) :
      HasDerivAt (fun y : ℝ => (z + (y : ℂ))⁻¹) (-((z + (x : ℂ)) ^ 2)⁻¹) x := by
    have hz : z + (x : ℂ) ≠ 0 := by
      intro h
      exact (hpos hx).ne' (by simpa only [Complex.zero_re] using congrArg Complex.re h)
    simpa only [Function.comp_def, one_smul] using
      (hasDerivAt_inv hz).scomp x (hasDerivAt_add_ofReal z x)
  have hfI : IntervalIntegrable f volume a (a + 1) :=
    ContinuousOn.intervalIntegrable (fun _ hx => (hf hx).continuousAt.continuousWithinAt)

  let L := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (conj error))
  let F (x : ℝ) := L (f x)
  let F' (x : ℝ) := L (z + (x : ℂ))⁻¹
  have hL (w : ℂ) : |L w| ≤ ‖error‖ * ‖w‖ := by
    change |(conj error * w).re| ≤ _
    simpa only [norm_mul, Complex.norm_conj] using Complex.abs_re_le_norm (conj error * w)
  have heL : L error = ‖error‖ ^ 2 := by
    change (conj error * error).re = _
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, Complex.sq_norm]
  have hJuniq : UniqueDiffOn ℝ J := uniqueDiffOn_uIcc (by linarith : a ≠ a + 1)
  have hF {x : ℝ} (hx : x ∈ J) : HasDerivAt F (F' x) x :=
    L.hasFDerivAt.comp_hasDerivAt x (hf hx)
  have hderiv : EqOn (derivWithin F J) F' J := fun _ hx =>
    (hF hx).hasDerivWithinAt.derivWithin (hJuniq _ hx)
  have hF' {x : ℝ} (hx : x ∈ J) :
      HasDerivWithinAt (derivWithin F J) (L (-((z + (x : ℂ)) ^ 2)⁻¹)) J x :=
    (L.hasFDerivAt.comp_hasDerivAt x (hInv hx)).hasDerivWithinAt.congr_of_mem hderiv hx
  have hSecond (x : ℝ) : |iteratedDerivWithin 2 F J x| ≤ ‖error‖ / d := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDerivWithin_succ, iteratedDerivWithin_one]
    by_cases hx : x ∈ J
    · rw [(hF' hx).derivWithin (hJuniq x hx)]
      calc
        _ ≤ ‖error‖ * ‖-((z + (x : ℂ)) ^ 2)⁻¹‖ := hL _
        _ = ‖error‖ / ‖z + (x : ℂ)‖ ^ 2 := by simp [div_eq_mul_inv]
        _ ≤ ‖error‖ / d := div_le_div_of_nonneg_left (norm_nonneg _) hd (hnormSq hx)
    · have hClosed : IsClosed J := hJ ▸ isClosed_Icc
      rw [derivWithin_zero_of_notMem_closure (by rwa [hClosed.closure_eq]), abs_zero]
      positivity
  have htrap := trapezoidal_error_le (fun _ hx => (hF hx).differentiableAt.differentiableWithinAt)
    (fun _ hx => (hF' hx).differentiableWithinAt) hSecond (N := 1) (by decide)
  have hlen : a + 1 - a = 1 := by ring
  have hHalf (w : ℂ) : w / 2 = (1 / 2 : ℝ) • w := by
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  have herror : trapezoidal_error F 1 a (a + 1) = L error := by
    rw [trapezoidal_error, trapezoidal_integral_one, hlen]
    change (1 : ℝ) / 2 * (L (f a) + L (f (a + 1))) - (∫ x in a..a + 1, L (f x)) = L error
    rw [L.intervalIntegral_comp_comm hfI]
    simp only [error, hHalf, map_sub, map_smul, map_add, smul_eq_mul]
  rw [herror, heL, abs_of_nonneg (sq_nonneg _), hlen] at htrap
  norm_num at htrap
  apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr he)).mp
  calc
    ‖error‖ * ‖error‖ = ‖error‖ ^ 2 := (pow_two _).symm
    _ ≤ ‖error‖ / d / 12 := htrap
    _ = ‖error‖ * (1 / (12 * d)) := by rw [div_div, mul_comm d 12, mul_one_div]

/-- The one-unit trapezoidal error for the logarithm along the original Dottie line. -/
theorem dottie_log_trapezoid {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    ‖(Complex.log (z + (k : ℂ)) + Complex.log (z + (k : ℂ) + 1)) / 2 -
        (∫ x : ℝ in (k : ℝ)..(k : ℝ) + 1, Complex.log (z + (x : ℂ)))‖ ≤
      1 / (6 * ‖z + (k : ℂ)‖ ^ 2) := by
  have h := log_trapezoid_one_bound (z := z) (a := (k : ℝ)) (by positivity)
  have hWeak : (1 : ℝ) / (12 * ‖z + ((k : ℝ) : ℂ)‖ ^ 2) ≤
      1 / (6 * ‖z + ((k : ℝ) : ℂ)‖ ^ 2) := by
    simp only [div_mul_eq_div_div]
    exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  simpa only [Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_one,
    add_assoc] using h.trans hWeak

#print axioms log_trapezoid_one_bound
#print axioms dottie_log_trapezoid

end QuarticModel
