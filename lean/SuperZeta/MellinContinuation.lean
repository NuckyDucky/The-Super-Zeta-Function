import SuperZeta.MellinStep
import SuperZeta.TaylorKernel

/-! Compatible Mellin continuations from even Taylor remainders. The analytic
hypotheses and each integration half-plane are explicit. -/
noncomputable section
namespace SuperZeta.EvenMellin
open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology

/-- The coefficient c(k) is attached to the power x^(2(k+1)). -/
structure Data (f : ℝ → ℂ) (c : ℕ → ℂ) : Prop where
  local_integrable : LocallyIntegrableOn f (Ioi 0)
  at_top : f =O[atTop] (fun x : ℝ => Real.exp (-1*x))
  taylor (N : ℕ) :
    (fun x : ℝ => f x - ∑ k ∈ Finset.range N, c k*(x:ℂ)^(2*(k+1))) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-(-((2*(N+1):ℕ):ℝ))))

private def mode (k : ℕ) : ℝ → ℂ :=
  (Ioc (0:ℝ) 1).indicator fun x => (x:ℂ)^(2*(k+1))

/-- Subtract the first N Taylor terms in the interval (0,1]. -/
def remainder (f : ℝ → ℂ) (c : ℕ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  f x - ∑ k ∈ Finset.range N, c k * mode k x

private theorem rem_succ (f : ℝ → ℂ) (c : ℕ → ℂ) (N : ℕ) :
    remainder f c (N+1) = fun x => remainder f c N x - c N * mode N x := by
  funext x
  simp [remainder, Finset.sum_range_succ]
  ring

private theorem rem_local {f c} (d : Data f c) (N : ℕ) :
    LocallyIntegrableOn (remainder f c N) (Ioi 0) := by
  induction N with
  | zero =>
    have h0 : remainder f c 0 = f := by funext x; simp [remainder]
    rw [h0]
    exact d.local_integrable
  | succ N ih =>
    have hpow : Continuous (fun x : ℝ => (x:ℂ)^(2*(N+1))) := by fun_prop
    have hc : LocallyIntegrable (mode N) := hpow.locallyIntegrable.indicator measurableSet_Ioc
    rw [rem_succ]
    exact ih.sub (fun x hx => (hc.locallyIntegrableOn _ x hx).smul (c N))

private theorem rem_top {f c} (d : Data f c) (N : ℕ) :
    remainder f c N =O[atTop] (fun x : ℝ => Real.exp (-1*x)) := by
  apply d.at_top.congr' _ (Filter.EventuallyEq.rfl)
  filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx
  simp [remainder, mode, not_le.mpr hx]

private theorem rem_zero {f c} (d : Data f c) (N : ℕ) :
    remainder f c N =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(-((2*(N+1):ℕ):ℝ)))) := by
  apply (d.taylor N).congr' _ (Filter.EventuallyEq.rfl)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0:ℝ)<1 by norm_num)).filter_mono
      (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))] with x hx hlt
  have hm : x ∈ Ioc (0:ℝ) 1 := ⟨hx, hlt.le⟩
  simp [remainder,mode,hm]

theorem converges {f c} (d : Data f c) (N : ℕ) {s : ℂ} (hs : s.re < N+1) :
    MellinConvergent (remainder f c N) (-(2*s)) := by
  apply mellinConvergent_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
    (rem_local d N) (rem_top d N) (rem_zero d N)
  push_cast
  simp [two_mul]
  linarith

private theorem mode_transform (k : ℕ) {s : ℂ} (hs : s.re < k+1) :
    HasMellin (mode k) (-(2*s)) (1/(-(2*s)+2*((k:ℂ)+1))) := by
  have hh : 0 < (-(2*s)).re + (((2*(k+1):ℕ):ℂ)).re := by
    push_cast
    simp [two_mul]
    linarith
  have h := hasMellin_cpow_Ioc (((2*(k+1):ℕ):ℂ)) hh
  simp only [Complex.cpow_natCast] at h
  simpa only [mode, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h

private def phase (s : ℂ) : ℂ := Complex.sin ((Real.pi:ℂ)*s)

private theorem phase_entire : Differentiable ℂ phase := by unfold phase; fun_prop

private theorem phase_integer (k : ℕ) : phase ((k:ℂ)+1) = 0 := by
  simpa only [phase, Nat.cast_add, Nat.cast_one, mul_comm] using Complex.sin_nat_mul_pi (k+1)

private theorem divided_entire (k : ℕ) : Differentiable ℂ (dslope phase ((k:ℂ)+1)) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (univ_mem : Set.univ ∈ 𝓝 ((k:ℂ)+1))).mpr
    phase_entire.differentiableOn

/-- N terms removed from the logarithm, with all pole corrections filled by
the divided differences of sin(πs). -/
def patch (f : ℝ → ℂ) (c : ℕ → ℂ) (N : ℕ) (s : ℂ) : ℂ :=
  2*s*phase s/(Real.pi:ℂ)*mellin (remainder f c N) (-(2*s)) -
    ∑ k ∈ Finset.range N, c k*s/(Real.pi:ℂ)*dslope phase ((k:ℂ)+1) s

theorem patch_differentiable {f c} (d : Data f c) (N : ℕ) {s : ℂ} (hs : s.re < N+1) :
    DifferentiableAt ℂ (patch f c N) s := by
  have hm : DifferentiableAt ℂ (mellin (remainder f c N)) (-(2*s)) := by
    apply mellin_differentiableAt_of_isBigO_rpow_exp (by norm_num : (0:ℝ)<1)
      (rem_local d N) (rem_top d N) (rem_zero d N)
    push_cast
    simp [two_mul]
    linarith
  have harg : DifferentiableAt ℂ (fun z : ℂ => -(2*z)) s := by fun_prop
  have hcomp := hm.comp s harg
  unfold patch
  apply DifferentiableAt.sub
  · exact ((((differentiableAt_const (2:ℂ)).mul differentiableAt_id).mul
      (phase_entire s)).div_const (Real.pi:ℂ)).mul hcomp
  · apply DifferentiableAt.sum
    intro k _
    exact (((differentiableAt_const (c k)).mul differentiableAt_id).div_const
      (Real.pi:ℂ)).mul (divided_entire k s)

theorem patch_succ_eq {f c} (d : Data f c) (N : ℕ) {s : ℂ} (hs : s.re < N+1) :
    patch f c (N+1) s = patch f c N s := by
  have hs1 : s ≠ (N:ℂ)+1 := by intro h; rw [h] at hs; simp at hs
  have hc := mode_transform N hs
  have hm := (hasMellin_sub (converges d N hs) (hc.1.const_smul (c N))).2
  rw [mellin_const_smul, hc.2] at hm
  have he : mellin (remainder f c (N+1)) (-(2*s)) = mellin (remainder f c N) (-(2*s)) -
      c N*(1/(-(2*s)+2*((N:ℂ)+1))) := by rw [rem_succ]; exact hm
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hn : -(2*s)+2*((N:ℂ)+1) ≠ 0 := by intro h; apply hs1; linear_combination -h/2
  simp only [patch, Finset.sum_range_succ, he, dslope_of_ne _ hs1,
    slope_def_field, phase_integer, sub_zero]
  field_simp [hp, hn, sub_ne_zero.mpr hs1]
  ring

/-- Finite Taylor subtractions agree on the entire common half-plane. -/
theorem patch_eq {f c} (d : Data f c) {N M : ℕ} (hNM : N ≤ M) {s : ℂ}
    (hs : s.re < N+1) : patch f c M s = patch f c N s := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M h ih =>
    have hh : (N:ℝ) ≤ M := by exact_mod_cast h
    rw [patch_succ_eq d M (by linarith), ih]

/-- The index ceiling chooses a convergent patch at every complex argument. -/
def continuation (f : ℝ → ℂ) (c : ℕ → ℂ) (s : ℂ) : ℂ := patch f c ⌈s.re⌉₊ s

theorem continuation_eq {f c} (d : Data f c) (N : ℕ) {s : ℂ} (hs : s.re < N+1) :
    continuation f c s = patch f c N s := by
  unfold continuation
  have hceil : s.re ≤ (⌈s.re⌉₊:ℕ) := Nat.le_ceil _
  rcases le_total N ⌈s.re⌉₊ with h | h
  · exact patch_eq d h hs
  · exact (patch_eq d h (by linarith : s.re < (⌈s.re⌉₊:ℝ)+1)).symm

/-- The compatible patches define an entire function on the complex plane. -/
theorem continuation_entire {f c} (d : Data f c) : Differentiable ℂ (continuation f c) := by
  intro s
  let N := ⌈s.re⌉₊
  have hsle : s.re ≤ (N:ℝ) := Nat.le_ceil _
  have hs : s.re < (N:ℝ)+1 := by linarith
  apply (patch_differentiable d N hs).congr_of_eventuallyEq
  filter_upwards [Complex.continuous_re.continuousAt.eventually_lt
    (continuousAt_const (y:=(N:ℝ)+1)) hs] with z hz
  exact continuation_eq d N hz

/-- All the original negative-integer sine zeros survive continuation. -/
theorem continuation_neg_nat {f c} (d : Data f c) (n : ℕ) :
    continuation f c (-(n:ℂ)) = 0 := by
  have hr : (-(n:ℂ)).re < ((0:ℕ):ℝ)+1 := by
    simp only [neg_re, natCast_re, Nat.cast_zero, zero_add]
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  rw [continuation_eq d 0 hr]
  simp [patch,phase,mul_comm (Real.pi:ℂ) (n:ℂ), Complex.sin_nat_mul_pi]

/-- Each positive integer reads one even Taylor coefficient. -/
theorem continuation_succ {f c} (d : Data f c) (n : ℕ) :
    continuation f c ((n:ℂ)+1) = -(c n*((n:ℂ)+1)*(-1:ℂ)^(n+1)) := by
  have hr : ((n:ℂ)+1).re < ((n+1:ℕ):ℝ)+1 := by push_cast; simp
  have hsum : (∑ k ∈ Finset.range n,
      c k*((n:ℂ)+1)/(Real.pi:ℂ)*dslope phase ((k:ℂ)+1) ((n:ℂ)+1)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hne : (n:ℂ)+1 ≠ (k:ℂ)+1 := by
      exact fun h => (ne_of_gt hkn) (Nat.cast_injective (add_right_cancel h))
    simp [dslope_of_ne _ hne, slope_def_field, phase_integer]
  have hder : deriv phase ((n:ℂ)+1) = (-1:ℂ)^(n+1)*(Real.pi:ℂ) := by
    have h := (Complex.hasDerivAt_sin ((Real.pi:ℂ)*((n:ℂ)+1))).comp ((n:ℂ)+1)
      ((hasDerivAt_id ((n:ℂ)+1)).const_mul (Real.pi:ℂ))
    have hcosNat (m : ℕ) : Complex.cos ((Real.pi:ℂ)*m) = (-1:ℂ)^m := by
      induction m with
      | zero => simp
      | succ m ih => rw [Nat.cast_succ, mul_add, mul_one, Complex.cos_add_pi, ih, pow_succ]; ring
    have hcos := hcosNat (n+1)
    rw [Nat.cast_succ] at hcos
    simpa [phase,Function.comp_def,hcos] using h.deriv
  rw [continuation_eq d (n+1) hr, patch, phase_integer, Finset.sum_range_succ, hsum,
    dslope_same, hder]
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

end SuperZeta.EvenMellin

namespace SuperZeta.Reference
open Complex

theorem logKernel_data {q : ℝ} (hq : 0 ≤ q) :
    EvenMellin.Data (logKernel q) (taylorKernelCoeff q) :=
  ⟨kernel_locally_integrable hq, kernel_at_top hq, logKernel_taylor_remainder q⟩

/-- The entire continuation of the manuscript's integral J, with q=ε⁻². -/
def entireCorrection (q : ℝ) : ℂ → ℂ :=
  EvenMellin.continuation (logKernel q) (taylorKernelCoeff q)

theorem entireCorrection_differentiable {q : ℝ} (hq : 0 ≤ q) :
    Differentiable ℂ (entireCorrection q) :=
  EvenMellin.continuation_entire (logKernel_data hq)

theorem entireCorrection_eq {q : ℝ} (hq : 0 ≤ q) {s : ℂ} (hs : s.re < 1) :
    entireCorrection q s = correction q s := by
  rw [entireCorrection, EvenMellin.continuation_eq (logKernel_data hq) 0 (by simpa using hs),
    correction, sqrt_transform]
  have h0 : EvenMellin.remainder (logKernel q) (taylorKernelCoeff q) 0 = logKernel q := by
    funext x; simp [EvenMellin.remainder]
  simp [EvenMellin.patch, EvenMellin.phase, h0]
  ring

theorem entireCorrection_succ {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    entireCorrection q ((n:ℂ)+1) =
      -(taylorKernelCoeff q n*((n:ℂ)+1)*(-1:ℂ)^(n+1)) :=
  EvenMellin.continuation_succ (logKernel_data hq) n

theorem entireCorrection_neg_nat {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    entireCorrection q (-(n:ℂ)) = 0 :=
  EvenMellin.continuation_neg_nat (logKernel_data hq) n

/-- The all-order formula agrees with the independently evaluated first
subtraction throughout its domain, in particular at its removable pole. -/
theorem entireCorrection_eq_toTwo {q : ℝ} (hq : 0 ≤ q) {s : ℂ} (hs : s.re < 2) :
    entireCorrection q s = correctionToTwo q s := by
  let U := {z : ℂ | z.re < 2}
  have hop : IsOpen U := isOpen_lt Complex.continuous_re continuous_const
  have hpre : IsPreconnected U := (convex_halfSpace_lt Complex.reLm.isLinear 2).isPreconnected
  have hd : DifferentiableOn ℂ (correctionToTwo q) U :=
    fun z hz => (correctionToTwo_differentiable hq hz).differentiableWithinAt
  have hfg : entireCorrection q =ᶠ[nhds (0:ℂ)] correctionToTwo q := by
    filter_upwards [Complex.continuous_re.continuousAt.eventually_lt
      (continuousAt_const (y:=(1:ℝ))) (by norm_num : (0:ℂ).re < 1)] with z hz
    exact (entireCorrection_eq hq hz).trans (correctionToTwo_eq hq hz).symm
  exact ((entireCorrection_differentiable hq).differentiableOn.analyticOnNhd hop
    |>.eqOn_of_preconnected_of_eventuallyEq (hd.analyticOnNhd hop) hpre
      (show (0:ℂ) ∈ U by change (0:ℂ).re < 2; norm_num) hfg) hs

theorem entireCorrection_one {q : ℝ} (hq : 0 ≤ q) : entireCorrection q 1 = (q:ℂ) := by
  rw [entireCorrection_eq_toTwo hq (by norm_num : (1:ℂ).re < 2), correctionToTwo_one]

end SuperZeta.Reference
