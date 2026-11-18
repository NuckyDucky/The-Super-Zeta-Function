import SuperZeta.Barnes
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.MeasureTheory.Integral.Prod

/-! The exact logarithmic correction from the central binomial coefficient.

The integral formula uses Frullani's identity and the Gamma recurrence. Both
sides tend to zero after translation to infinity, which fixes the constant.
-/
namespace SuperZeta.StirlingCorrection
open Real Set Filter MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

/-- The exact remainder after taking the logarithm of the leading Stirling formula. -/
def factorialRemainder (n : ℕ) : ℝ := Real.log (Stirling.stirlingSeq n) - Real.log π / 2

/-- The normalization by an arbitrary sequence of positive quartet radii. -/
def C (R : ℕ → ℝ) (n : ℕ) : ℝ := R n * Barnes.B n ^ 2 / 2

theorem D_pos {n : ℕ} (hn : 0 < n) : 0 < Barnes.D n := by
  have hb := Nat.centralBinom_pos n
  unfold Barnes.D Barnes.B
  positivity

theorem C_eq (R : ℕ → ℝ) {n : ℕ} (hn : 0 < n) :
    C R n = R n / (2*π*n) * Barnes.D n := by
  have hp : (n:ℝ) ≠ 0 := by positivity
  unfold C Barnes.D
  field_simp [hp, pi_ne_zero]
  ring

theorem C_pos {R : ℕ → ℝ} {n : ℕ} (hR : 0 < R n) : 0 < C R n := by
  have h := Nat.centralBinom_pos n
  unfold C Barnes.B
  positivity

private theorem B_factorials (n : ℕ) :
    Barnes.B n = ((2*n).factorial : ℝ) / (4^n * (n.factorial:ℝ)^2) := by
  have h : n.centralBinom * n.factorial * n.factorial = (2*n).factorial := by
    simpa [Nat.centralBinom, two_mul] using Nat.add_choose_mul_factorial_mul_factorial n n
  have hc : (n.centralBinom:ℝ)*n.factorial*n.factorial = ((2*n).factorial:ℝ) := by exact_mod_cast h
  unfold Barnes.B
  field_simp [show (n.factorial:ℝ) ≠ 0 by positivity]
  linear_combination (4:ℝ)^n * hc

/-- The signed combination of the three factorial remainders is exact. -/
theorem log_D_factorial {n : ℕ} (hn : 0 < n) :
    Real.log (Barnes.D n) = 2*factorialRemainder (2*n) - 4*factorialRemainder n := by
  have h : 0 < (n:ℝ) := by exact_mod_cast hn
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ)=(2:ℝ)^2 by norm_num, Real.log_pow]; norm_num
  rw [Barnes.D, B_factorials, Real.log_mul (by positivity) (by positivity),
    Real.log_mul pi_ne_zero h.ne', Real.log_pow,
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, h4]
  simp only [factorialRemainder, Stirling.log_stirlingSeq_formula, Nat.cast_mul, Nat.cast_ofNat]
  rw [show (2:ℝ)*(2*n) = 2*(2*n) by rfl, Real.log_mul (by norm_num : (2:ℝ) ≠ 0)
    (by positivity : (2:ℝ)*n ≠ 0)]
  rw [Real.log_div (by positivity : (2:ℝ)*n ≠ 0) (by positivity : exp 1 ≠ 0),
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) h.ne',
    Real.log_div h.ne' (by positivity : exp 1 ≠ 0)]
  rw [Real.log_exp]
  ring

theorem log_C_factorial {R : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hr : 0 < R n) :
    Real.log (C R n) = Real.log (R n/(2*π*n)) +
      (2*factorialRemainder (2*n) - 4*factorialRemainder n) := by
  rw [C_eq R hn, Real.log_mul (by positivity) (D_pos hn).ne', log_D_factorial hn]

/-- The normalized half-integer Gamma ratio for a continuous level. -/
def gammaRatio (x : ℝ) := x * (Gamma (x+1/2) / Gamma (x+1))^2

theorem gammaRatio_pos {x : ℝ} (hx : 0<x) : 0 < gammaRatio x := by
  have h₁ := Gamma_pos_of_pos (show 0<x+1/2 by linarith)
  have h₂ := Gamma_pos_of_pos (show 0<x+1 by linarith)
  unfold gammaRatio
  positivity

theorem gammaRatio_nat (n : ℕ) : gammaRatio n = Barnes.D n := by
  unfold gammaRatio Barnes.D
  rw [Barnes.gamma_half_grid n, Gamma_nat_eq_factorial]
  rw [show sqrt π * (n.factorial:ℝ) * Barnes.B n / n.factorial = sqrt π * Barnes.B n by
    field_simp [show (n.factorial:ℝ) ≠ 0 by positivity]; ring]
  rw [mul_pow, sq_sqrt pi_pos.le]
  ring

private theorem logGamma_step {x : ℝ} (hx : 0<x) :
    log (Gamma (x+1)) = log x + log (Gamma x) := by
  rw [Gamma_add_one hx.ne', log_mul hx.ne' (Gamma_pos_of_pos hx).ne']

private theorem logGammaRatio {x : ℝ} (hx : 0<x) :
    log (gammaRatio x) = log x + 2*(log (Gamma (x+1/2)) - log (Gamma (x+1))) := by
  have hp := Gamma_pos_of_pos (show 0 < x+1/2 by linarith)
  have hq := Gamma_pos_of_pos (show 0 < x+1 by linarith)
  rw [gammaRatio, log_mul hx.ne' (by positivity), log_pow, log_div hp.ne' hq.ne']
  norm_num

/-- Logarithmic convexity and the recurrence squeeze the Gamma ratio between
x/(x+1/2) and one. This determines the constant in the integral formula. -/
private theorem logGammaRatio_bounds {x : ℝ} (hx : 0<x) :
    -(log (1+1/(2*x))) ≤ log (gammaRatio x) ∧ log (gammaRatio x) ≤ 0 := by
  have mid {u v : ℝ} (hu : 0<u) (hv : 0<v) :
      log (Gamma ((u+v)/2)) ≤ (log (Gamma u) + log (Gamma v))/2 := by
    have h := convexOn_log_Gamma.2 (show u ∈ Ioi 0 from hu)
      (show v ∈ Ioi 0 from hv) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1:ℝ)/2+1/2=1)
    simpa only [smul_eq_mul, Function.comp_apply, show 1/2*u + 1/2*v = (u+v)/2 by ring,
      show 1/2*log (Gamma u)+1/2*log (Gamma v)=(log (Gamma u)+log (Gamma v))/2 by ring] using h
  have a := mid hx (show 0<x+1 by linarith)
  have b := mid (show 0<x+1/2 by linarith) (show 0<(x+1/2)+1 by linarith)
  rw [show (x+(x+1))/2 = x+1/2 by ring, logGamma_step hx] at a
  rw [show (x+1/2+(x+1/2+1))/2=x+1 by ring,
    logGamma_step (show 0<x+1/2 by linarith)] at b
  rw [logGammaRatio hx]
  constructor
  · rw [show (1:ℝ)+1/(2*x)=(x+1/2)/x by field_simp; ring,
      log_div (by positivity : x+1/2 ≠ 0) hx.ne']
    linarith only [b]
  · linarith only [a, logGamma_step hx]

private theorem logGammaRatio_step {x : ℝ} (hx : 0<x) :
    log (gammaRatio (x+1)) - log (gammaRatio x) =
      (log (x+1/2) - log x) - (log (x+1) - log (x+1/2)) := by
  rw [logGammaRatio (show 0<x+1 by linarith), logGammaRatio hx,
    show x+1+1/2 = x+1/2+1 by ring,
    logGamma_step (show 0<x+1/2 by linarith), logGamma_step (show 0<x+1 by linarith)]
  ring

/-- Frullani's identity for two positive parameters. The joint integrand on
(a,b] × (0,∞) is bounded by exp(−a t), so Fubini applies. -/
private theorem frullani {a b : ℝ} (ha : 0<a) (hab : a≤b) :
    IntegrableOn (fun t : ℝ => (exp (-a*t)-exp (-b*t))/t) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, (exp (-a*t)-exp (-b*t))/t) = log b - log a := by
  let μ := (volume : Measure ℝ).restrict (Ioc a b)
  let ν := (volume : Measure ℝ).restrict (Ioi 0)
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, measure_Ioc_lt_top]⟩
  have hmajor : Integrable (fun p : ℝ × ℝ => exp (-a*p.2)) (μ.prod ν) := by
    have ha' : Integrable (fun t : ℝ => exp (-a*t)) ν :=
      integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
    simpa only [one_mul] using (integrable_const (μ:=μ) (1:ℝ)).mul_prod ha'
  have hle : ∀ᵐ (p : ℝ × ℝ) ∂(μ.prod ν), ‖exp (-p.1*p.2)‖ ≤ exp (-a*p.2) := by
    dsimp only [μ, ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)
      (μ:=(volume : Measure ℝ).prod (volume : Measure ℝ)) (s:=Ioc a b ×ˢ Ioi (0:ℝ))] with p hp
    rw [Real.norm_of_nonneg (exp_pos _).le, exp_le_exp]
    exact mul_le_mul_of_nonneg_right (neg_le_neg hp.1.1.le) hp.2.le
  have hex : Integrable (fun p : ℝ × ℝ => exp (-p.1*p.2)) (μ.prod ν) :=
    hmajor.mono' (by fun_prop : Continuous (fun p : ℝ × ℝ => exp (-p.1*p.2))).aestronglyMeasurable hle
  have hleft : (fun t : ℝ => (∫ u, exp (-u*t) ∂μ)) =ᵐ[ν]
      (fun t : ℝ => (exp (-a*t)-exp (-b*t))/t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi (μ:=volume) (s:=Ioi (0:ℝ))] with t ht
    change (∫ u in Ioc a b, exp (-u*t)) = _
    rw [← intervalIntegral.integral_of_le hab]
    have e (u : ℝ) : HasDerivAt (fun u => exp (-u*t)/(-t)) (exp (-u*t)) u := by
      convert (((hasDerivAt_id u).neg.mul_const t).exp.div_const (-t)) using 1
      simp
      field_simp [show t ≠ 0 from ht.ne']
    have hc : Continuous (fun u : ℝ => exp (-u*t)) := by fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => e u) (hc.intervalIntegrable _ _)]
    ring
  have hright : (fun u : ℝ => (∫ t, exp (-u*t) ∂ν)) =ᵐ[μ] (fun u : ℝ => 1/u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc (μ:=volume) (s:=Ioc a b)] with u hu
    have h : 0<u := ha.trans hu.1
    simpa [ν] using integral_exp_mul_Ioi (neg_lt_zero.mpr h) 0
  refine ⟨hex.integral_prod_right.congr hleft, ?_⟩
  change (∫ t, _ ∂ν) = _
  rw [← integral_congr_ae hleft,
    integral_integral_swap (f:=fun t u : ℝ => exp (-u*t)) hex.swap, integral_congr_ae hright]
  change (∫ u in Ioc a b, 1/u) = _
  rw [← intervalIntegral.integral_of_le hab, integral_one_div_of_pos ha (ha.trans_le hab),
    log_div (ha.trans_le hab).ne' ha.ne']

/-- The Laplace kernel is the logarithmic derivative of the cosine reference product,
rescaled to the central-binomial correction. -/
def kernel (t : ℝ) : ℝ := tanh (t/4)/t

private theorem tanh_le_self {x : ℝ} (hx : 0≤x) : tanh x ≤ x := by
  let f : ℝ → ℝ := fun y => y*cosh y-sinh y
  have df (y : ℝ) : HasDerivAt f (y*sinh y) y := by
    convert ((hasDerivAt_id y).mul (hasDerivAt_cosh y)).sub (hasDerivAt_sinh y) using 1
    simp
  have hm : MonotoneOn f (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici _) (fun y _ => (df y).continuousAt.continuousWithinAt)
    · exact fun y _ => (df y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici, mem_Ioi] at hy
      rw [(df y).deriv]
      exact mul_nonneg hy.le (sinh_nonneg_iff.mpr hy.le)
  rw [tanh_eq_sinh_div_cosh, div_le_iff₀ (cosh_pos x)]
  simpa [f, sub_nonneg] using hm (left_mem_Ici) hx hx

theorem kernel_bounds {t : ℝ} (ht : 0<t) : 0 ≤ kernel t ∧ kernel t ≤ 1/4 := by
  let v := t/4
  have hv : 0<v := by positivity
  have htanh : 0 ≤ tanh v := by
    rw [tanh_eq_sinh_div_cosh]
    exact div_nonneg (sinh_nonneg_iff.mpr hv.le) (cosh_pos v).le
  refine ⟨div_nonneg htanh ht.le, (div_le_iff₀ ht).mpr ?_⟩
  calc
    tanh (t/4) ≤ t/4 := tanh_le_self hv.le
    _ = (1/4)*t := by ring

def laplace (x : ℝ) : ℝ := ∫ t : ℝ in Ioi 0, exp (-x*t)*kernel t

theorem laplace_integrable {x : ℝ} (hx : 0<x) :
    IntegrableOn (fun t : ℝ => exp (-x*t)*kernel t) (Ioi 0) := by
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hx) 0).mul_const (1/4)).mono'
  · have h : Continuous fun t : ℝ => tanh (t/4) := by
      simp only [tanh_eq_sinh_div_cosh]
      apply Continuous.div <;> first | fun_prop | intro t; exact (cosh_pos _).ne'
    exact (measurable_const.neg.mul measurable_id |>.exp |>.mul
      (h.measurable.div measurable_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi (μ:=volume) (s:=Ioi (0:ℝ))] with t ht
    obtain ⟨h0,h1⟩ := kernel_bounds ht
    rw [Real.norm_of_nonneg (mul_nonneg (exp_pos _).le h0)]
    exact mul_le_mul_of_nonneg_left h1 (exp_pos _).le

private theorem laplace_bounds {x : ℝ} (hx : 0<x) :
    0 ≤ laplace x ∧ laplace x ≤ 1/(4*x) := by
  constructor
  · exact setIntegral_nonneg measurableSet_Ioi (fun t ht =>
      mul_nonneg (exp_pos _).le (kernel_bounds ht).1)
  · calc
      laplace x ≤ ∫ t : ℝ in Ioi 0, exp (-x*t)*(1/4) := by
        apply setIntegral_mono_on (laplace_integrable hx)
          ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hx) 0).mul_const _) measurableSet_Ioi
        exact fun t ht => mul_le_mul_of_nonneg_left (kernel_bounds ht).2 (exp_pos _).le
      _ = 1/(4*x) := by
        rw [MeasureTheory.integral_mul_const, integral_exp_mul_Ioi (neg_lt_zero.mpr hx) 0]
        simp

private theorem tanh_exp {t : ℝ} :
    tanh (t/4) = (1-exp (-t/2))/(1+exp (-t/2)) := by
  have e := exp_pos (t/4)
  have e' := exp_pos (-t/4)
  have hh : exp (-(t/4))^2 = exp (-t/2) := by rw [sq, ← exp_add]; congr 1; ring
  rw [tanh_eq_sinh_div_cosh, sinh_eq, cosh_eq, ← hh]
  have hid := exp_add (t/4) (-(t/4))
  rw [add_neg_cancel, exp_zero] at hid
  field_simp [show exp (t/4)+exp (-(t/4)) ≠ 0 by positivity,
    show 1+exp (-(t/4))^2 ≠ 0 by positivity]
  simp only [neg_div] at *
  linear_combination -2 * exp (-(t/4)) * hid

private theorem laplace_step {x : ℝ} (hx : 0<x) :
    laplace x - laplace (x+1) =
      (log (x+1/2) - log x) - (log (x+1) - log (x+1/2)) := by
  let f := fun t : ℝ => (exp (-x*t)-exp (-(x+1/2)*t))/t
  let g := fun t : ℝ => (exp (-(x+1/2)*t)-exp (-(x+1)*t))/t
  have hf := frullani hx (show x≤x+1/2 by linarith)
  have hg := frullani (show 0<x+1/2 by linarith) (show x+1/2≤x+1 by linarith)
  rw [laplace, laplace, ← integral_sub (laplace_integrable hx)
      (laplace_integrable (show 0<x+1 by linarith)), ← hf.2, ← hg.2, ← integral_sub hf.1 hg.1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [kernel, tanh_exp]
  have e₁ : exp (-(x+1/2)*t) = exp (-x*t)*exp (-t/2) := by rw [← exp_add]; congr 1; ring
  have e₂ : exp (-(x+1)*t) = exp (-x*t)*exp (-t/2)^2 := by
    rw [sq, ← exp_add, ← exp_add]; congr 1; ring
  rw [e₁,e₂]
  field_simp [show t ≠ 0 from ht.ne', show 1+exp (-t/2) ≠ 0 by positivity]
  ring

/-- The exact integral, including the full remainder, for every real positive level. -/
theorem log_gammaRatio_eq_neg_laplace {x : ℝ} (hx : 0<x) :
    log (gammaRatio x) = -laplace x := by
  let f := fun y : ℝ => log (gammaRatio y) + laplace y
  have hstep {y : ℝ} (hy : 0<y) : f (y+1)=f y := by
    dsimp [f]
    linarith only [laplace_step hy, logGammaRatio_step hy]
  have hconst (n : ℕ) : f (x+n) = f x := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_succ, ← add_assoc, hstep (by positivity), ih]
  have horbit : Tendsto (fun n : ℕ => x+(n:ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => 1/(x+(n:ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop horbit
  have hlow := (((hzero.div_const 2).const_add 1).log (by norm_num)).neg
  have hup := hzero.div_const 4
  have hl : Tendsto (fun n : ℕ => -(log (1+1/(2*(x+n))))) atTop (𝓝 0) := by
    convert hlow using 1
    · funext n; rw [div_div, mul_comm (x+(n:ℝ))]
    · norm_num
  have hu : Tendsto (fun n : ℕ => 1/(4*(x+n))) atTop (𝓝 0) := by
    convert hup using 1
    · funext n; rw [div_div, mul_comm (x+(n:ℝ))]
    · norm_num
  have ht : Tendsto (fun n : ℕ => f (x+n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
    · intro n
      have hp : 0 < x+(n:ℝ) := by positivity
      dsimp [f]
      linarith only [(logGammaRatio_bounds hp).1, (laplace_bounds hp).1]
    · intro n
      have hp : 0 < x+(n:ℝ) := by positivity
      dsimp [f]
      linarith only [(logGammaRatio_bounds hp).2, (laplace_bounds hp).2]
  simp_rw [hconst] at ht
  have hm := tendsto_nhds_unique (tendsto_const_nhds (x:=f x) (f:=atTop (α:=ℕ))) ht
  linarith only [show log (gammaRatio x) + laplace x = 0 from hm]

theorem log_D_eq_neg_laplace {n : ℕ} (hn : 0<n) :
    log (Barnes.D n) = -laplace n := by
  rw [← gammaRatio_nat, log_gammaRatio_eq_neg_laplace (by positivity)]

theorem factorialRemainder_eq_neg_laplace {n : ℕ} (hn : 0<n) :
    2*factorialRemainder (2*n) - 4*factorialRemainder n = -laplace n :=
  (log_D_factorial hn).symm.trans (log_D_eq_neg_laplace hn)

theorem log_C_eq_radial_sub_laplace {R : ℕ → ℝ} {n : ℕ}
    (hn : 0<n) (hr : 0<R n) :
    log (C R n) = log (R n/(2*π*n)) - laplace n := by
  rw [log_C_factorial hn hr, factorialRemainder_eq_neg_laplace hn, sub_eq_add_neg]


/-- Dyadic telescoping recovers the log remainder of one factorial from the
same Laplace kernel that evaluates the central-binomial combination. -/
theorem factorialRemainder_hasSum {n : ℕ} (hn : 0<n) :
    HasSum (fun k : ℕ => (1/2 : ℝ)^k * laplace (↑((2:ℕ)^k*n) : ℝ)/4)
      (factorialRemainder n) := by
  have index_pos (k : ℕ) : 0 < (2:ℕ)^k*n := by positivity
  refine (hasSum_iff_tendsto_nat_of_nonneg
    (fun k => div_nonneg (mul_nonneg (by positivity)
      (laplace_bounds (by exact_mod_cast index_pos k)).1) (by norm_num)) _).2 ?_
  let tail (k : ℕ) := (1/2 : ℝ)^k * factorialRemainder ((2:ℕ)^k*n)
  have step (k : ℕ) :
      (1/2 : ℝ)^k * laplace (↑((2:ℕ)^k*n) : ℝ)/4 = tail k - tail (k+1) := by
    have h := factorialRemainder_eq_neg_laplace (index_pos k)
    have h' : laplace (↑((2:ℕ)^k*n) : ℝ)/4 =
        factorialRemainder ((2:ℕ)^k*n) -
          factorialRemainder (2*((2:ℕ)^k*n))/2 := by linarith
    rw [div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv, h']
    simp only [tail, pow_succ]
    rw [show (2:ℕ)^k*2*n = 2*((2:ℕ)^k*n) by ac_rfl]
    ring
  simp_rw [step, Finset.sum_range_sub']
  have hindex : Tendsto (fun k : ℕ => (2:ℕ)^k*n) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_right _ hn)
      (Nat.tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hrem : Tendsto factorialRemainder atTop (𝓝 0) := by
    have h := (Stirling.tendsto_stirlingSeq_sqrt_pi.log
      (Real.sqrt_pos.2 Real.pi_pos).ne').sub_const (log π / 2)
    simpa only [factorialRemainder, Real.log_sqrt Real.pi_pos.le, sub_self] using h
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := (1/2 : ℝ))
    (by norm_num [abs_of_pos (by norm_num : 0 < (1/2 : ℝ))])
  have htail : Tendsto tail atTop (𝓝 0) := by
    simpa only [tail, Function.comp_def, zero_mul] using hpow.mul (hrem.comp hindex)
  simpa only [tail, pow_zero, one_mul, sub_zero] using htail.const_sub (factorialRemainder n)

/-- Stirling's leading expression times the exponential of its exact remainder is n!. -/
theorem factorial_eq_stirling_mul_exp_dyadic {n : ℕ} (hn : 0<n) :
    (n.factorial : ℝ) = sqrt (2*π*n) * (n/exp 1)^n *
      exp (∑' k : ℕ, (1/2 : ℝ)^k * laplace (↑((2:ℕ)^k*n) : ℝ)/4) := by
  have hs : 0 < Stirling.stirlingSeq n := by
    have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
    unfold Stirling.stirlingSeq
    positivity
  rw [(factorialRemainder_hasSum hn).tsum_eq, factorialRemainder,
    ← Real.log_sqrt Real.pi_pos.le, ← Real.log_div hs.ne' (Real.sqrt_pos.2 Real.pi_pos).ne',
    Real.exp_log (div_pos hs (Real.sqrt_pos.2 Real.pi_pos)), Stirling.stirlingSeq,
    show 2*π*(n:ℝ) = (2*n)*π by ring, Real.sqrt_mul (by positivity)]
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  field_simp
  ring

end
end SuperZeta.StirlingCorrection
