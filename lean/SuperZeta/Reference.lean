import SuperZeta.Spectrum
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! The unperturbed cosine determinant has a double eigenvalue at each
positive squared half-integer multiple of π. Its Dirichlet series gives the
Riemann channel of the reconstruction in the half-plane of absolute convergence. -/
noncomputable section
namespace SuperZeta.Reference
open Complex

/-- Squared reference root; its summand occurs twice in the determinant. -/
def eigenvalue (n : ℕ) : ℝ := (Real.pi * ((n : ℝ) + 1/2))^2

/-- Odd Dirichlet series in the absolutely convergent half-plane. -/
theorem odd_hasSum {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun n : ℕ => 1 / ((2*n+1 : ℕ) : ℂ)^w)
      ((1 - 1 / (2:ℂ)^w) * riemannZeta w) := by
  let f := fun n : ℕ => 1 / (n:ℂ)^w
  have hsum : Summable f := Complex.summable_one_div_nat_cpow.mpr hw
  have he : Summable fun n : ℕ => f (2*n) :=
    hsum.comp_injective (by intro a b h; omega)
  have ho : Summable fun n : ℕ => f (2*n+1) :=
    hsum.comp_injective (by intro a b h; dsimp at h; omega)
  have scale (n : ℕ) : f (2*n) = (1 / (2:ℂ)^w) * f n := by
    dsimp [f]
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    simp [one_div, mul_comm]
  have all := tsum_even_add_odd he ho
  have ev : (∑' n : ℕ, f (2*n)) = (1/(2:ℂ)^w)*riemannZeta w := by
    simp_rw [scale]
    rw [tsum_mul_left, zeta_eq_tsum_one_div_nat_cpow hw]
  rw [ev, ← zeta_eq_tsum_one_div_nat_cpow hw] at all
  convert ho.hasSum using 1
  linear_combination -all

private theorem mode (s : ℂ) (n : ℕ) :
    (eigenvalue n : ℂ)^(-s) =
      (Real.pi : ℂ)^(-(2*s)) * (2:ℂ)^(2*s) * (1 / ((2*n+1 : ℕ) : ℂ)^(2*s)) := by
  have ho : (0:ℝ) < (2*n+1 : ℕ) := by positivity
  have he : 0 < eigenvalue n := by unfold eigenvalue; positivity
  have log_e : Real.log (eigenvalue n) =
      2 * (Real.log Real.pi + Real.log (2*n+1 : ℕ) - Real.log 2) := by
    have ar : (n:ℝ)+1/2 = (↑(2*n+1 : ℕ):ℝ)/2 := by push_cast; ring
    rw [eigenvalue, Real.log_pow, ar, Real.log_mul Real.pi_ne_zero (by positivity),
      Real.log_div (ne_of_gt ho) (by norm_num)]
    ring
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr he.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by omega : 2*n+1≠0)),
    ← Complex.ofReal_log he.le, ← Complex.ofReal_log Real.pi_pos.le,
    ← Complex.natCast_log, log_e]
  have htwo : log (2:ℂ) = ↑(Real.log 2) := by norm_cast
  rw [htwo, one_div, ← exp_neg, ← exp_add, ← exp_add]
  push_cast
  ring_nf

/-- Equation (21)'s reference spectrum equals the actual mathlib Riemann
zeta expression. The factor two is the reference algebraic multiplicity. -/
theorem reference_hasSum {s : ℂ} (hs : 1/2 < s.re) :
    HasSum (fun n : ℕ => 2 * (eigenvalue n : ℂ)^(-s))
      (Spectrum.riemannFactor s * riemannZeta (2*s)) := by
  have hw : 1 < (2*s).re := by simp [two_mul]; linarith
  have h := (odd_hasSum hw).mul_left (2 * (Real.pi : ℂ)^(-(2*s)) * (2:ℂ)^(2*s))
  have htwo : (2:ℂ)^(2*s) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  convert h using 1
  · funext n
    rw [mode]
    ring
  · unfold Spectrum.riemannFactor
    field_simp
    ring

open MeasureTheory Filter Set Asymptotics
open scoped Topology

/-- The squared reference determinant vanishes quadratically at every listed
eigenvalue, with the exact, positive leading coefficient in λ coordinates. -/
theorem reference_double_root (n : ℕ) :
    Real.cos (Real.sqrt (eigenvalue n)) = 0 ∧
    Tendsto (fun x : ℝ => (Real.cos (Real.sqrt x))^2 / (x-eigenvalue n)^2)
      (𝓝[≠] (eigenvalue n)) (𝓝 (1/(4*eigenvalue n))) ∧ 0 < 1/(4*eigenvalue n) := by
  have he : 0 < eigenvalue n := by unfold eigenvalue; positivity
  have hangle : Real.sqrt (eigenvalue n) = Real.pi/2 + n*Real.pi := by
    rw [eigenvalue, Real.sqrt_sq (by positivity)]
    ring
  have hcos : Real.cos (Real.sqrt (eigenvalue n)) = 0 := by
    rw [hangle, Real.cos_add_nat_mul_pi, Real.cos_pi_div_two, mul_zero]
  have hs := Real.sin_sq_add_cos_sq (Real.sqrt (eigenvalue n))
  rw [hcos] at hs
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hs
  have hder := (Real.hasDerivAt_cos (Real.sqrt (eigenvalue n))).comp
    (eigenvalue n) (Real.hasDerivAt_sqrt he.ne')
  have h := (hasDerivAt_iff_tendsto_slope.mp hder).pow 2
  have norm : (-Real.sin (Real.sqrt (eigenvalue n))*(1/(2*Real.sqrt (eigenvalue n))))^2
      = 1/(4*eigenvalue n) := by
    rw [mul_pow, neg_sq, hs, one_mul, div_pow, mul_pow, Real.sq_sqrt he.le]
    norm_num
  refine ⟨hcos, ?_, by positivity⟩
  simpa only [slope_def_field, Function.comp_apply, hcos, sub_zero, div_pow, norm] using h

/-- With q=ε⁻² and t=x², this is log(1+t sech²(√t)/ε²). -/
def logKernel (q x : ℝ) : ℂ := ↑(Real.log (1 + q*(x / Real.cosh x)^2))

/-- Exact logarithmic determinant split on the integration ray, prior to
differentiation or integration. No term crosses a logarithm cut. -/
theorem log_determinant_split {q t : ℝ} (hq : 0 ≤ q) (ht : 0 ≤ t) :
    (Real.log ((Real.cosh (Real.sqrt t))^2+q*t) : ℂ) =
      ↑(2*Real.log (Real.cosh (Real.sqrt t))) + logKernel q (Real.sqrt t) := by
  have hc := Real.cosh_pos (Real.sqrt t)
  have hp : (Real.cosh (Real.sqrt t))^2+q*t =
      (Real.cosh (Real.sqrt t))^2 * (1+q*(Real.sqrt t/Real.cosh (Real.sqrt t))^2) := by
    rw [div_pow, Real.sq_sqrt ht]
    field_simp
  rw [hp,Real.log_mul (pow_ne_zero _ hc.ne') (by positivity), Real.log_pow]
  simp [logKernel]

theorem logKernel_bound {q : ℝ} (hq : 0 ≤ q) (x : ℝ) :
    ‖logKernel q x‖ ≤ q*(x / Real.cosh x)^2 := by
  have hp : 0 ≤ q*(x / Real.cosh x)^2 := by positivity
  rw [logKernel, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by linarith))]
  linarith [Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + q*(x / Real.cosh x)^2)]

theorem kernel_at_zero {q : ℝ} (hq : 0 ≤ q) :
    logKernel q =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-2 : ℝ))) := by
  refine isBigO_iff.mpr ⟨q, Filter.Eventually.of_forall fun x => ?_⟩
  rw [neg_neg, Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg x)]
  apply (logKernel_bound hq x).trans
  apply mul_le_mul_of_nonneg_left _ hq
  rw [div_pow]
  exact div_le_self (sq_nonneg x) (one_le_pow₀ (Real.one_le_cosh x))

theorem kernel_at_top {q : ℝ} (hq : 0 ≤ q) :
    logKernel q =O[atTop] (fun x : ℝ => Real.exp (-1*x)) := by
  refine isBigO_iff.mpr ⟨q*8, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [neg_one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_assoc]
  apply (logKernel_bound hq x).trans
  apply mul_le_mul_of_nonneg_left _ hq
  rw [div_pow, div_le_iff₀ (sq_pos_of_pos (Real.cosh_pos x))]
  have hcosh : Real.exp x ≤ 2*Real.cosh x := by
    rw [Real.cosh_eq]; linarith [Real.exp_pos (-x)]
  have hsq : (Real.exp x)^2 ≤ (2*Real.cosh x)^2 := by gcongr
  calc
    x^2 ≤ 2*Real.exp x := by
      have h := Real.pow_div_factorial_le_exp x hx 2
      norm_num at h
      linarith
    _ = 2*Real.exp (-x)*(Real.exp x)^2 := by
      rw [Real.exp_neg]; field_simp; ring
    _ ≤ 2*Real.exp (-x)*(2*Real.cosh x)^2 := by gcongr
    _ = _ := by ring

theorem kernel_locally_integrable {q : ℝ} (hq : 0 ≤ q) :
    LocallyIntegrableOn (logKernel q) (Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  apply Continuous.continuousOn
  unfold logKernel
  apply Complex.continuous_ofReal.comp
  apply Continuous.log
  · exact continuous_const.add (continuous_const.mul
      ((continuous_id.div Real.continuous_cosh (fun x => (Real.cosh_pos x).ne')).pow 2))
  · intro x
    dsimp
    positivity

/-- The relative Mellin term of manuscript equation (22), in t-coordinates. -/
def correction (q : ℝ) (s : ℂ) : ℂ :=
  s * Complex.sin (↑Real.pi*s) / ↑Real.pi *
    mellin (fun t : ℝ => logKernel q (Real.sqrt t)) (-s)

theorem sqrt_transform (q : ℝ) (s : ℂ) :
    mellin (fun t : ℝ => logKernel q (Real.sqrt t)) (-s) =
      (2:ℂ)*mellin (logKernel q) (-(2*s)) := by
  simp_rw [Real.sqrt_eq_rpow]
  rw [mellin_comp_rpow]
  norm_num [Complex.real_smul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  ring_nf

theorem correction_converges {q : ℝ} (hq : 0 ≤ q) {s : ℂ} (hs : s.re < 1) :
    MellinConvergent (fun t : ℝ => logKernel q (Real.sqrt t)) (-s) := by
  simp_rw [Real.sqrt_eq_rpow]
  rw [MellinConvergent.comp_rpow (by norm_num)]
  apply mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
    (kernel_locally_integrable hq) (kernel_at_top hq) (kernel_at_zero hq)
  norm_num [div_eq_mul_inv]
  linarith

theorem correction_differentiable {q : ℝ} (hq : 0 ≤ q) {s : ℂ} (hs : s.re < 1) :
    DifferentiableAt ℂ (correction q) s := by
  have hm : DifferentiableAt ℂ (mellin (logKernel q)) (-(2*s)) := by
    apply mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
      (kernel_locally_integrable hq) (kernel_at_top hq) (kernel_at_zero hq)
    simp [two_mul]
    linarith
  unfold correction
  simp_rw [sqrt_transform]
  fun_prop (disch := first | exact hm | exact_mod_cast Real.pi_ne_zero)

/-- Expression furnished by the reference series and the relative determinant. -/
def continuedExpression (q : ℝ) (s : ℂ) : ℂ :=
  Spectrum.riemannFactor s * riemannZeta (2*s) + correction q s

/-- The reconstruction expression has residue 1/π at s=1/2. -/
theorem residue_half {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun s : ℂ => (s-1/2)*continuedExpression q s)
      (𝓝[≠] (1/2)) (𝓝 ((Real.pi : ℂ)⁻¹)) := by
  have scale : Tendsto (fun s : ℂ => 2*s) (𝓝[≠] (1/2)) (𝓝[≠] 1) := by
    have h : ContinuousWithinAt (fun s : ℂ => 2*s) {1/2}ᶜ (1/2) :=
      (continuous_const.mul continuous_id).continuousWithinAt
    convert h.tendsto_nhdsWithin (s := {1/2}ᶜ) (t := {1}ᶜ) (by
      intro x hx
      simp only [mem_compl_iff,mem_singleton_iff] at hx ⊢
      intro hx'
      exact hx (by linear_combination hx'/2)) using 1
    norm_num
  have hz := riemannZeta_residue_one.comp scale
  have hc : ContinuousAt (fun s : ℂ => Spectrum.riemannFactor s / 2) (1/2) := by
    unfold Spectrum.riemannFactor
    have ht : ContinuousAt (fun s : ℂ => 2*s) (1/2) :=
      (continuous_const.mul continuous_id).continuousAt
    have hpi := (continuousAt_const_cpow (a:=(Real.pi:ℂ))
      (by exact_mod_cast Real.pi_ne_zero)).comp ht.neg
    have htwo := (continuousAt_const_cpow (a:=(2:ℂ)) (by norm_num)).comp ht
    exact ((continuousAt_const.mul hpi).mul (htwo.sub continuousAt_const)).div_const 2
  have hj := (correction_differentiable hq (s:=(1/2:ℂ)) (by norm_num)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s:={(1/2:ℂ)}ᶜ))
  have hsmall : Tendsto (fun s : ℂ => s-1/2) (𝓝[≠] (1/2)) (𝓝 0) := by
    have hid : Tendsto (fun s : ℂ => s) (𝓝[≠] (1/2:ℂ)) (𝓝 (1/2:ℂ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using hid.sub_const (1/2:ℂ)
  have ht := ((hc.continuousWithinAt (s:={(1/2:ℂ)}ᶜ)).tendsto.mul hz).add (hsmall.mul hj)
  convert ht using 1
  · funext s
    dsimp [continuedExpression]
    ring
  · norm_num [Spectrum.riemannFactor, Complex.cpow_neg]

end SuperZeta.Reference
