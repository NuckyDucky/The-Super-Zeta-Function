import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import DottieLogTrapezoid

/-! Analytic inputs for the Gamma phase in the archived Dottie normalization. -/

open Complex Filter MeasureTheory Set
open scoped Topology

namespace QuarticModel

/-- A branch-consistent exponent for Euler's finite Gamma product on the
right half-plane. The equality is after exponentiation, where winding of
the accumulated logarithm is immaterial. -/
theorem dottie_gammaSeq_eq_exp {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 0 < n) :
    GammaSeq z n = Complex.exp (Complex.log (n : ℂ) * z +
      Complex.log (n.factorial : ℂ) - ∑ k ∈ Finset.range (n + 1), Complex.log (z + k)) := by
  rw [Complex.exp_sub, Complex.exp_add, Complex.exp_sum, Complex.exp_log
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), GammaSeq,
    cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn.ne')]
  apply congrArg (fun t : ℂ => Complex.exp (Complex.log (n : ℂ) * z) * n.factorial / t)
  apply Finset.prod_congr rfl
  intro k _
  apply (Complex.exp_log _).symm
  intro he
  have hr := congrArg Complex.re he
  simp at hr
  linarith [Nat.cast_nonneg (α := ℝ) k]

private theorem normalized_exp (v : ℂ) :
    Complex.exp v / (‖Complex.exp v‖ : ℂ) = Complex.exp ((v.im : ℂ) * I) := by
  rw [Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_sub]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- The finite Gamma product's phase, with the factorial magnitude canceled. -/
theorem dottie_gammaSeq_phase {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 0 < n) :
    GammaSeq z n / (‖GammaSeq z n‖ : ℂ) = Complex.exp (((z.im * Real.log n -
      ∑ k ∈ Finset.range (n + 1), (Complex.log (z + k)).im : ℝ) : ℂ) * I) := by
  rw [dottie_gammaSeq_eq_exp hz hn, normalized_exp]
  congr 2
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, ← Complex.natCast_log,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.im_sum]
  rw [mul_comm]

/-- The finite phases converge to the actual unit Gamma direction. -/
theorem dottie_gamma_phase_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => Complex.exp (((z.im * Real.log n -
      ∑ k ∈ Finset.range (n + 1), (Complex.log (z + k)).im : ℝ) : ℂ) * I))
      atTop (𝓝 (Gamma z / (‖Gamma z‖ : ℂ))) := by
  have h := GammaSeq_tendsto_Gamma z
  have hn : Tendsto (fun n : ℕ => (‖GammaSeq z n‖ : ℂ)) atTop (𝓝 (‖Gamma z‖ : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp h.norm
  have hv : (‖Gamma z‖ : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos hz))
  apply (h.div hn hv).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hpos
  exact dottie_gammaSeq_phase hz hpos

private theorem log_correction_tendsto (z : ℂ) :
    Tendsto (fun (n : ℕ) => (z+n+1/2)*Complex.log (1+z/(n : ℂ)) - z)
      atTop (𝓝 0) := by
  have hscaled : Tendsto (fun (n : ℕ) => (n : ℂ)*(z/n)) atTop (𝓝 z) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    exact mul_div_cancel₀ z (Nat.cast_ne_zero.mpr hn)
  have hfirst := Complex.tendsto_nat_mul_log_one_add_of_tendsto hscaled
  have hinv : Tendsto (fun n : ℕ => ((n : ℂ)⁻¹)) atTop (𝓝 0) := by
    have hreal := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero,
      Function.comp_def] using hreal.ofReal
  have hratio : Tendsto (fun n : ℕ => z/(n : ℂ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul z
  have hlog : Tendsto (fun n : ℕ => Complex.log (1+z/(n : ℂ))) atTop (𝓝 0) := by
    have h := (Complex.hasDerivAt_log Complex.one_mem_slitPlane).continuousAt.tendsto
    have ha := hratio.const_add 1
    rw [add_zero] at ha
    simpa only [Complex.log_one, Function.comp_def] using h.comp ha
  have h := (hfirst.add (hlog.const_mul (z+1/2))).sub_const z
  simp only [mul_zero, add_zero, sub_self] at h
  apply h.congr
  intro n
  ring

/-- The moving endpoint has no residual phase after removing Im(z) log n. -/
theorem dottie_gamma_endpoint_phase_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => ((z+n+1/2)*Complex.log (z+n) - (z+n)).im - z.im*Real.log n)
      atTop (𝓝 0) := by
  have hi := Complex.continuous_im.continuousAt.tendsto.comp (log_correction_tendsto z)
  simp only [Complex.zero_im] at hi
  apply hi.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  dsimp only [Function.comp_apply]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hsplit : (n : ℂ)*(1 + z/n) = z+n := by
    rw [mul_add, mul_one, mul_div_cancel₀ z hn', add_comm]
  have hsum : z + (n : ℂ) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hne : 1 + z/(n : ℂ) ≠ 0 := by
    intro he
    apply hsum
    rw [← hsplit, he, mul_zero]
  have hlog : Complex.log (z+n) = (Real.log n : ℂ) + Complex.log (1+z/(n : ℂ)) := by
    rw [← hsplit]
    exact Complex.log_ofReal_mul (Nat.cast_pos.mpr hn) hne
  rw [hlog, mul_add]
  simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.natCast_im,
    Complex.ofReal_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.one_im,
    add_zero]
  ring

/-- Exact integral of the same logarithm along a horizontal line. -/
theorem dottie_gamma_log_integral {z : ℂ} (hz : 0 < z.re) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ x : ℝ in a..b, Complex.log (z + x)) =
      ((z + b) * Complex.log (z + b) - (z + b)) - ((z + a) * Complex.log (z + a) - (z + a)) := by
  let primitive := fun w : ℂ => (z+w) * Complex.log (z+w) - (z+w)
  have hs (x : ℝ) (hx : x ∈ uIcc a b) : z + (x : ℂ) ∈ slitPlane := by
    rw [uIcc_of_le hab] at hx
    apply Complex.mem_slitPlane_iff.mpr
    exact Or.inl (by simpa using add_pos_of_pos_of_nonneg hz (ha.trans hx.1))
  have hd (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun y : ℝ => primitive y) (Complex.log (z+x)) x := by
    have ha : HasDerivAt (fun w : ℂ => z+w) 1 (x : ℂ) :=
      (hasDerivAt_id (x : ℂ)).const_add z
    have hlog := (Complex.hasDerivAt_log (hs x hx)).comp (x : ℂ) ha
    have h := ((ha.mul hlog).sub ha).comp_ofReal
    change HasDerivAt (fun y : ℝ => primitive y) _ x at h
    have hn : z+(x : ℂ) ≠ 0 := Complex.slitPlane_ne_zero (hs x hx)
    convert h using 1
    simp only [Function.comp_apply]
    field_simp [hn]
    ring
  have hi : IntervalIntegrable (fun x : ℝ => Complex.log (z+x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have h := (Complex.hasDerivAt_log (hs x hx)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).const_add z)
    exact h.comp_ofReal.continuousAt.continuousWithinAt
  simpa [primitive] using intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

private noncomputable def logTrapezoidError (z : ℂ) (k : ℕ) : ℂ :=
  (Complex.log (z + k) + Complex.log (z + k + 1)) / 2 -
    ∫ x : ℝ in (k : ℝ)..(k : ℝ) + 1, Complex.log (z + x)

private theorem gamma_log_partial_sum {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), Complex.log (z + k)) =
      ((z + n + 1/2) * Complex.log (z + n) - (z + n)) -
      ((z - 1/2) * Complex.log z - z) + ∑ k ∈ Finset.range n, logTrapezoidError z k := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    unfold logTrapezoidError
    rw [dottie_gamma_log_integral hz (Nat.cast_nonneg (α := ℝ) n) (by linarith)]
    push_cast
    simp only [add_assoc]
    ring

private theorem trapezoid_error_sum {z : ℂ} (hz : 0 < z.re) (ht : 1 ≤ |z.im|) :
    Summable (fun k => ‖logTrapezoidError z k‖) ∧
      ‖∑' k, logTrapezoidError z k‖ ≤ 1 / (3 * |z.im|) := by
  let a := |z.im|
  let M (k : ℕ) : ℝ := ((a+k)⁻¹-(a+k+1)⁻¹)/3
  have ha : 0 < a := by linarith only [ht]
  have hb (k : ℕ) : 0 < a+k := by positivity
  have hb' (k : ℕ) : 0 < a+k+1 := by positivity
  have hMpos (k : ℕ) : 0 ≤ M k := by
    apply div_nonneg _ (by norm_num)
    exact sub_nonneg.mpr ((inv_le_inv₀ (hb' k) (hb k)).mpr (by linarith))
  have hMsum : HasSum M (a⁻¹ / 3) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg hMpos _).mpr
    have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
    have haTop : Tendsto (fun n : ℕ => a+(n:ℝ)) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_left ha.le) hcast
    have htor := tendsto_inv_atTop_zero.comp haTop
    have hlim := (tendsto_const_nhds (x := a⁻¹)).sub htor |>.div_const 3
    rw [sub_zero] at hlim
    apply hlim.congr
    intro n
    simp only [M, ← Finset.sum_div, Function.comp_apply, add_assoc, ← Nat.cast_add_one]
    rw [Finset.sum_range_sub' (fun k : ℕ => (a+(k:ℝ))⁻¹) n]
    simp
  have hMbound (k : ℕ) : ‖logTrapezoidError z k‖ ≤ M k := by
    have hunit := log_trapezoid_one_bound (z := z) (a := (k : ℝ)) (by positivity)
    have hw : ‖logTrapezoidError z k‖ ≤ 1 / (12 * ‖z + (k : ℂ)‖ ^ 2) := by
      simpa only [logTrapezoidError, Complex.ofReal_add, Complex.ofReal_one,
        Complex.ofReal_natCast, add_assoc] using hunit
    have hsq : a^2+(k:ℝ)^2 ≤ ‖z+(k:ℂ)‖^2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp only [add_re, add_im, natCast_re, natCast_im, add_zero, show a^2 = z.im^2 from sq_abs _]
      nlinarith [sq_nonneg z.re, mul_nonneg hz.le (Nat.cast_nonneg (α := ℝ) k)]
    have hprod : (a+k)*(a+k+1) ≤ 4*(a^2+(k:ℝ)^2) := by
      have h₁ : 0 ≤ a+(k:ℝ)-1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
      nlinarith [sq_nonneg (a-(k:ℝ)), mul_nonneg (hb k).le h₁]
    have hdiv : 1 / (12 * ‖z + (k : ℂ)‖ ^ 2) ≤ 1 / (3 * ((a+k)*(a+k+1))) := by
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    refine hw.trans (hdiv.trans_eq ?_)
    unfold M
    field_simp [(hb k).ne', (hb' k).ne']
    ring
  have hnorm := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hMbound hMsum.summable
  refine ⟨hnorm, (norm_tsum_le_tsum_norm hnorm).trans ?_⟩
  have hm := hnorm.tsum_le_tsum hMbound hMsum.summable
  rw [hMsum.tsum_eq] at hm
  simpa [a, div_eq_mul_inv, mul_comm] using hm

/-- The Gamma phase for the archived completion has a certified error of
at most 1/(3 |Im z|) relative to the leading Stirling phase. -/
theorem dottie_gamma_phase_with_error {z : ℂ} (hz : 0 < z.re) (ht : 1 ≤ |z.im|) :
    ∃ error : ℝ, |error| ≤ 1 / (3 * |z.im|) ∧
      Gamma z / (‖Gamma z‖ : ℂ) =
      Complex.exp ((((z-1/2)*Complex.log z-z).im + error : ℝ) * I) := by
  obtain ⟨habs, hbound⟩ := trapezoid_error_sum hz ht
  let phase := ((z-1/2)*Complex.log z-z).im
  let error := -(∑' k, logTrapezoidError z k).im
  refine ⟨error, ?_, ?_⟩
  · simpa only [error, abs_neg] using (Complex.abs_im_le_norm _).trans hbound
  have herror := habs.of_norm.hasSum.tendsto_sum_nat
  have heim := Complex.continuous_im.continuousAt.tendsto.comp herror
  have hlin := (tendsto_const_nhds (x := phase)).sub
    (dottie_gamma_endpoint_phase_tendsto hz) |>.sub heim
  have hphase : Tendsto (fun n : ℕ => z.im * Real.log n -
      ∑ k ∈ Finset.range (n+1), (Complex.log (z+k)).im) atTop (𝓝 (phase+error)) := by
    rw [sub_zero, sub_eq_add_neg] at hlin
    apply hlin.congr
    intro n
    rw [← Complex.im_sum, gamma_log_partial_sum hz]
    unfold phase
    simp only [Function.comp_apply, Complex.add_im, Complex.sub_im]
    ring
  have hc := hphase.ofReal.mul_const I |>.cexp
  exact tendsto_nhds_unique (dottie_gamma_phase_tendsto hz) hc

#print axioms dottie_gammaSeq_eq_exp
#print axioms dottie_gamma_phase_tendsto
#print axioms dottie_gamma_endpoint_phase_tendsto
#print axioms dottie_gamma_log_integral
#print axioms dottie_gamma_phase_with_error

end QuarticModel
