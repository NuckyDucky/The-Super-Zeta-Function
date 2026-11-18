import SuperZeta.StirlingCorrection
import SuperZeta.ReferenceResolvent
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! A sign and a one-term upper bound for every finite truncation. The
positive denominators in the reference resolvent give the exact remainder
before taking the Laplace transform. -/
namespace SuperZeta.StirlingCorrection
open Real Set Filter MeasureTheory
open Finset (range sum_range_succ sum_neg_distrib sum_congr mul_sum)
open scoped Topology
noncomputable section

private def pole (j : ℕ) : ℝ := 16 * Reference.eigenvalue j

private lemma pole_lower (j : ℕ) : ((j:ℝ)+1)^2 ≤ pole j := by
  have h : (j:ℝ)+1 ≤ π*((j:ℝ)+1/2) := by
    nlinarith [pi_gt_three, mul_nonneg (Nat.cast_nonneg (α:=ℝ) j)
      (show 0≤π-1 by linarith [pi_gt_three])]
  have e := pow_le_pow_left₀ (show 0≤(j:ℝ)+1 by positivity) h 2
  unfold pole Reference.eigenvalue
  linarith [sq_nonneg (π*((j:ℝ)+1/2))]

private lemma pole_ge_one (j : ℕ) : 1 ≤ pole j :=
  (by nlinarith [Nat.cast_nonneg (α:=ℝ) j] : (1:ℝ) ≤ ((j:ℝ)+1)^2).trans (pole_lower j)

private lemma pole_pos (j : ℕ) : 0 < pole j := zero_lt_one.trans_le (pole_ge_one j)

private theorem kernel_modes {t : ℝ} (ht : 0<t) :
    kernel t = ∑' j, 8/(t^2+pole j) := by
  have h0 : 0<t/4 := by positivity
  have h1 : 0<(t/4)^2 := by positivity
  have a := Reference.reference_resolvent h1
  have d := (((Real.hasDerivAt_sqrt h1.ne').cosh).pow 2).log (by positivity)
  have b := d.unique a
  simp only [Function.comp_apply, Real.sqrt_sq h0.le] at b
  have e : tanh (t/4)/(t/4) = ∑' j, (2:ℝ)/((t/4)^2+Reference.eigenvalue j) := by
    rw [← b, tanh_eq_sinh_div_cosh]
    field_simp [(Real.cosh_pos (t/4)).ne', h0.ne']
    ring
  calc
    kernel t = (1/4)*(tanh (t/4)/(t/4)) := by unfold kernel; ring
    _ = ∑' j, 8/(t^2+pole j) := by
      rw [e, ← tsum_mul_left]
      apply tsum_congr
      intro j
      have hp : 0 < Reference.eigenvalue j := by unfold Reference.eigenvalue; positivity
      have hq : 0 < pole j := pole_pos j
      unfold pole at hq ⊢
      field_simp [show (t/4)^2+Reference.eigenvalue j ≠ 0 by positivity,
        show t^2+16*Reference.eigenvalue j ≠ 0 by positivity]
      ring

private def momentCoeff (m j : ℕ) : ℝ := 8 / pole j^(m+1)

private theorem momentCoeff_summable (m : ℕ) : Summable (momentCoeff m) := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr one_lt_two)
  apply Summable.of_nonneg_of_le (fun j => by
    have hp := pole_pos j
    unfold momentCoeff
    positivity) _ (h.mul_left 8)
  intro j
  change 8/pole j^(m+1) ≤ 8*(1/((j+1:ℕ):ℝ)^2)
  rw [mul_one_div, Nat.cast_add, Nat.cast_one]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  refine (pole_lower j).trans ?_
  exact le_self_pow₀ (pole_ge_one j) (by omega)

/-- The unsigned coefficient of (t^{2m}) before the Laplace transform. -/
def amplitude (m : ℕ) : ℝ := ∑' j, momentCoeff m j

/-- The absolute size of the order (x^{-(2m+1)}) coefficient. -/
def gain (m : ℕ) : ℝ := amplitude m * (Nat.factorial (2*m):ℝ)

private def remainderTerm (m : ℕ) (y : ℝ) (j : ℕ) : ℝ :=
  8 / (pole j^m*(pole j+y))

private lemma remainderTerm_bound (m j : ℕ) {y : ℝ} (hy : 0≤y) :
    0 ≤ remainderTerm m y j ∧ remainderTerm m y j ≤ momentCoeff m j := by
  have hp := pole_pos j
  unfold remainderTerm momentCoeff
  constructor
  · positivity
  · rw [pow_succ]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hy) (by positivity)

/-- The finite geometric expansion for a single partial fraction. -/
private lemma one_mode {a : ℝ} (ha : 0<a) {y : ℝ} (hy : 0≤y) (m : ℕ) :
    8/(a+y) = (∑ k ∈ range m, (-1:ℝ)^k * y^k * (8/a^(k+1))) +
      (-1:ℝ)^m*y^m*(8/(a^m*(a+y))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    calc
      _ = _ := ih
      _ = _ := by
        rw [pow_succ (-1:ℝ), pow_succ y, pow_succ a m]
        field_simp [ha.ne', show a+y≠0 by positivity]
        ring

private def kernelPolynomial (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ range m, (-1:ℝ)^k * (t^2)^k * amplitude k

private theorem kernel_remainder (m : ℕ) {t : ℝ} (ht : 0<t) :
    0 ≤ (-1:ℝ)^m*(kernel t-kernelPolynomial m t) ∧
    (-1:ℝ)^m*(kernel t-kernelPolynomial m t) ≤ amplitude m * t^(2*m) := by
  let f (k j : ℕ) := (-1:ℝ)^k*(t^2)^k*momentCoeff k j
  let g (j : ℕ) := remainderTerm m (t^2) j
  have hf (k : ℕ) : Summable (f k) := (momentCoeff_summable k).mul_left _
  have hg : Summable g := Summable.of_nonneg_of_le (fun j => (remainderTerm_bound m j (sq_nonneg t)).1)
    (fun j => (remainderTerm_bound m j (sq_nonneg t)).2) (momentCoeff_summable m)
  have hsum : Summable (fun j => ∑ k ∈ range m, f k j) :=
    summable_sum (s:=range m) (fun k _ => hf k)
  have hmode (j : ℕ) : 8/(t^2+pole j) = (∑ k ∈ range m, f k j)+
      ((-1:ℝ)^m*(t^2)^m)*g j := by
    rw [add_comm (t^2)]
    exact one_mode (pole_pos j) (sq_nonneg t) m
  have he : kernel t = kernelPolynomial m t + (-1:ℝ)^m*(t^2)^m*(∑' j, g j) := by
    rw [kernel_modes ht]
    simp_rw [hmode]
    rw [hsum.tsum_add (hg.mul_left _), tsum_mul_left, Summable.tsum_finsetSum (fun k _ => hf k)]
    simp only [f, tsum_mul_left, kernelPolynomial, amplitude]
  have hpar : ((-1:ℝ)^m)^2=1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hnorm : (-1:ℝ)^m*(kernel t-kernelPolynomial m t) = (t^2)^m*(∑' j, g j) := by
    rw [he]
    calc
      _ = ((-1:ℝ)^m)^2*((t^2)^m*∑' j, g j) := by ring
      _ = _ := by rw [hpar,one_mul]
  rw [hnorm]
  exact ⟨mul_nonneg (by positivity) (tsum_nonneg (fun j => (remainderTerm_bound m j (sq_nonneg t)).1)),
    by
      rw [pow_mul, mul_comm (amplitude m)]
      exact mul_le_mul_of_nonneg_left
        (hg.tsum_le_tsum (fun j => (remainderTerm_bound m j (sq_nonneg t)).2) (momentCoeff_summable m))
        (by positivity)⟩

private theorem integrable_moment {x : ℝ} (hx : 0<x) (k : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-x*t)*t^k) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => exp (-t)*t^k) (Ioi 0) := by
    simpa only [add_sub_cancel_right, Real.rpow_natCast] using
      (GammaIntegral_convergent (s:=(k:ℝ)+1) (by positivity))
  have g : Integrable (fun t : ℝ => exp (-(x*t))*(x*t)^k) (volume.restrict (Ioi 0)) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ => exp (-t)*t^k) 0 hx).mpr (by simpa using h)
  apply (g.div_const (x^k)).congr
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [mul_pow, neg_mul]
    field_simp [pow_ne_zero k hx.ne']
    ring

private theorem integral_moment {x : ℝ} (hx : 0<x) (k : ℕ) :
    (∫ t : ℝ in Ioi 0, exp (-x*t)*t^k) = (Nat.factorial k:ℝ)/x^(k+1) := by
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a:=(k:ℝ)+1) (r:=x) (by positivity) hx
  have hr : ((1/x):ℝ)^((k:ℝ)+1) = 1/x^(k+1) := by
    rw [show (k:ℝ)+1 = ((k+1:ℕ):ℝ) by push_cast; rfl, Real.rpow_natCast]
    simp [one_div, inv_pow]
  rw [hr, add_sub_cancel_right, Real.Gamma_nat_eq_factorial,
    mul_comm (1/x^(k+1)), mul_one_div] at h
  simp_rw [Real.rpow_natCast] at h
  convert h using 1
  exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by rw [neg_mul, mul_comm])

/-- The signed coefficient, with index zero corresponding to order x⁻¹. -/
def coefficient (k : ℕ) : ℝ := -(-1:ℝ)^k * gain k

/-- First omitted term bounds every finite truncation, with its sign. -/
theorem signed_remainder {x : ℝ} (hx : 0<x) (m : ℕ) :
    0 ≤ -(-1:ℝ)^m*(log (gammaRatio x) -
      (∑ k ∈ range m, coefficient k/x^(2*k+1))) ∧
    -(-1:ℝ)^m*(log (gammaRatio x) -
      (∑ k ∈ range m, coefficient k/x^(2*k+1))) ≤ gain m/x^(2*m+1) := by
  let f (t : ℝ) := exp (-x*t) * ((-1:ℝ)^m*(kernel t-kernelPolynomial m t))
  have hmono (t : ℝ) (ht : t ∈ Ioi 0) := kernel_remainder m ht
  have fp (k : ℕ) : IntegrableOn (fun t : ℝ => exp (-x*t)*((-1:ℝ)^k*(t^2)^k*amplitude k)) (Ioi 0) := by
    apply ((integrable_moment hx (2*k)).const_mul ((-1:ℝ)^k*amplitude k)).congr
    exact Eventually.of_forall fun t => by
      dsimp only
      rw [pow_mul]
      ring
  have hp : IntegrableOn (fun t : ℝ => exp (-x*t)*kernelPolynomial m t) (Ioi 0) := by
    simp_rw [kernelPolynomial, mul_sum]
    exact integrable_finset_sum _ (fun k _ => fp k)
  have hi : IntegrableOn f (Ioi 0) := by
    apply (((laplace_integrable hx).sub hp).const_mul ((-1:ℝ)^m)).congr
    exact Eventually.of_forall fun t => by simp only [Pi.sub_apply, f]; ring
  have he : (∫ t in Ioi (0:ℝ), exp (-x*t)*kernelPolynomial m t) =
      -(∑ k ∈ range m, coefficient k/x^(2*k+1)) := by
    simp_rw [kernelPolynomial, mul_sum, ← sum_neg_distrib]
    rw [integral_finset_sum _ (fun k _ => fp k)]
    apply sum_congr rfl
    intro k _
    rw [show (fun t : ℝ => exp (-x*t)*((-1:ℝ)^k*(t^2)^k*amplitude k)) =
      (fun t : ℝ => ((-1:ℝ)^k*amplitude k)*(exp (-x*t)*t^(2*k))) by
        funext t; rw [pow_mul]; ring]
    rw [MeasureTheory.integral_const_mul, integral_moment hx, coefficient, gain]
    ring
  have hident : (∫ t in Ioi (0:ℝ), f t) =
      -(-1:ℝ)^m*(log (gammaRatio x)-(∑ k ∈ range m, coefficient k/x^(2*k+1))) := by
    unfold f
    simp_rw [show ∀ t : ℝ,
      exp (-x*t)*((-1:ℝ)^m*(kernel t-kernelPolynomial m t)) =
        (-1:ℝ)^m*(exp (-x*t)*kernel t-exp (-x*t)*kernelPolynomial m t) by intro; ring]
    rw [MeasureTheory.integral_const_mul, integral_sub (laplace_integrable hx) hp, he,
      log_gammaRatio_eq_neg_laplace hx, laplace]
    ring
  rw [← hident]
  constructor
  · exact setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (exp_pos _).le (hmono t ht).1)
  · calc
      _ ≤ ∫ t in Ioi (0:ℝ), amplitude m*(exp (-x*t)*t^(2*m)) := by
        apply setIntegral_mono_on hi ((integrable_moment hx _).const_mul _) measurableSet_Ioi
        intro t ht
        simpa only [f, mul_left_comm (amplitude m)] using
          mul_le_mul_of_nonneg_left (hmono t ht).2 (exp_pos _).le
      _ = _ := by rw [MeasureTheory.integral_const_mul, integral_moment hx, gain]; ring

theorem abs_coefficient (m : ℕ) : |coefficient m| = gain m := by
  have ha : 0 ≤ amplitude m := tsum_nonneg fun j => by
    unfold momentCoeff
    exact div_nonneg (by norm_num) (pow_nonneg (pole_pos j).le _)
  have hg : 0 ≤ gain m := by unfold gain; positivity
  simp [coefficient, abs_mul, abs_pow, abs_of_nonneg hg]

theorem abs_remainder {x : ℝ} (hx : 0<x) (m : ℕ) :
    |log (gammaRatio x) - (∑ k ∈ range m, coefficient k/x^(2*k+1))| ≤
      |coefficient m|/x^(2*m+1) := by
  obtain ⟨hs,hb⟩ := signed_remainder hx m
  have h := (abs_of_nonneg hs).trans_le hb
  simpa only [abs_mul, abs_neg, abs_pow, abs_one, one_pow, one_mul, abs_coefficient] using h

/-- The coefficients are moments of the cosine resolvent. This formula
connects them directly to the even Riemann zeta values. -/
theorem amplitude_zeta (k : ℕ) :
    (amplitude k : ℂ) =
      (4/(16:ℂ)^(k+1)) * (Spectrum.riemannFactor ((k:ℂ)+1) * riemannZeta (2*((k:ℂ)+1))) := by
  let m := k+1
  have h : 1/2 < (m:ℂ).re := by
    rw [Complex.natCast_re]
    dsimp [m]
    push_cast
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  have ref := (Reference.reference_hasSum h).mul_left (4/(16:ℂ)^m)
  have eq (j : ℕ) :
      (4/(16:ℂ)^m)*(2*(Reference.eigenvalue j:ℂ)^(-(m:ℂ))) = (momentCoeff k j:ℂ) := by
    rw [Complex.cpow_neg, Complex.cpow_natCast, momentCoeff, pole]
    push_cast
    rw [mul_pow]
    field_simp
    ring
  have hsum : HasSum (fun j => (momentCoeff k j:ℂ))
      (4/(16:ℂ)^m * (Spectrum.riemannFactor (m:ℂ) * riemannZeta (2*(m:ℂ)))) := by
    simpa only [eq] using ref
  rw [amplitude, Complex.ofReal_tsum, hsum.tsum_eq]
  simp [m]

theorem amplitude_zero : amplitude 0 = 1/4 := by
  have e := amplitude_zeta 0
  norm_num [Spectrum.riemannFactor, Complex.cpow_neg, Complex.cpow_two, riemannZeta_two] at e
  have hp : (π:ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  apply Complex.ofReal_injective
  push_cast
  rw [e]
  field_simp [hp]
  ring

theorem amplitude_one : amplitude 1 = 1/192 := by
  have e := amplitude_zeta 1
  norm_num [Spectrum.riemannFactor, Complex.cpow_neg, Complex.cpow_ofNat, riemannZeta_four] at e
  have hp : (π:ℂ) ≠ 0 := by exact_mod_cast pi_ne_zero
  apply Complex.ofReal_injective
  push_cast
  rw [e]
  field_simp [hp]
  ring

/-- The first Stirling correction and its first omitted term. -/
theorem first_remainder {x : ℝ} (hx : 0<x) :
    0 ≤ log (gammaRatio x)+1/(4*x) ∧
    log (gammaRatio x)+1/(4*x) ≤ 1/(96*x^3) := by
  have h := signed_remainder hx 1
  norm_num [sum_range_succ, coefficient, gain, amplitude_zero, amplitude_one,
    Nat.factorial] at h
  have eq : -(1/4:ℝ)/x = -(1/(4*x)) := by rw [neg_div, div_div]
  rw [eq, div_div (1:ℝ) 96] at h
  constructor <;> linarith [h.1,h.2]

theorem first_remainder_nat {n : ℕ} (hn : 0<n) :
    0 ≤ log (Barnes.D n)+1/(4*(n:ℝ)) ∧
    log (Barnes.D n)+1/(4*(n:ℝ)) ≤ 1/(96*(n:ℝ)^3) := by
  simpa only [gammaRatio_nat] using first_remainder (show 0<(n:ℝ) by positivity)

/-- Beyond level N the sum of omitted Stirling terms is bounded by the
first omitted coefficient times the corresponding positive Dirichlet tail. -/
theorem cutoff_error (N m : ℕ) (hm : 0<m) :
    |∑' j : ℕ, (log (Barnes.D (j+N+1)) -
      (∑ k ∈ range m, coefficient k / ((j+N+1:ℕ):ℝ)^(2*k+1)))| ≤
    |coefficient m| * (∑' j : ℕ, 1 / ((j+N+1:ℕ):ℝ)^(2*m+1)) := by
  let f (j : ℕ) := log (Barnes.D (j+N+1)) -
    (∑ k ∈ range m, coefficient k / ((j+N+1:ℕ):ℝ)^(2*k+1))
  let u (j : ℕ) := |coefficient m| * (1 / ((j+N+1:ℕ):ℝ)^(2*m+1))
  have h (j : ℕ) : ‖f j‖ ≤ u j := by
    rw [Real.norm_eq_abs]
    simp only [u, mul_one_div]
    simpa only [gammaRatio_nat, f] using
      abs_remainder (show 0<((j+N+1:ℕ):ℝ) by positivity) m
  have hsum : Summable u := by
    have ht := Real.summable_one_div_nat_pow.mpr (show 1<2*m+1 by omega)
    have hi : Function.Injective (fun j : ℕ => j+N+1) := by
      intro i j e
      dsimp only at e
      omega
    exact (ht.comp_injective hi).mul_left _
  have hnorm := (Summable.of_norm_bounded u hsum h).norm
  have hs := (norm_tsum_le_tsum_norm hnorm).trans (hnorm.tsum_le_tsum h hsum)
  simpa only [Real.norm_eq_abs, f, u, tsum_mul_left] using hs

end
end SuperZeta.StirlingCorrection
