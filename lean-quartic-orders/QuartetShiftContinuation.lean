import QuartetShiftBoundsSeries
import SuperZeta.UnitSpectrum
import Mathlib.Analysis.Complex.LocallyUniformLimit

noncomputable section
open Set Filter Complex
open scoped Topology ComplexConjugate
namespace SuperZeta.QuartetShiftContinuation

def upper (n : ℕ) := RootBounds.u (UnitSpectrum.levelHeight n)
def reference (n : ℕ) : ℂ := ((Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ)
def levelDiff (n : ℕ) (s : ℂ) :=
  upper n ^ (-2*s) + conj (upper n) ^ (-2*s) - 2 * reference n ^ (-2*s)
def regularized (s : ℂ) :=
  (UnitSpectrum.dottie : ℂ) ^ (-2*s) + 2*(Real.pi : ℂ)^(-2*s)*riemannZeta (2*s) +
    ∑' n, levelDiff n s

lemma upper_re_pos (n : ℕ) : 0 < (upper n).re := by
  have hl := RootBounds.x_lower (Nat.succ_pos n)
    (by simpa using (UnitSpectrum.levelHeight_spec n).2)
  change 0 < RootBounds.x _
  exact lt_of_lt_of_le (by positivity : 0 < ((n+1:ℕ):ℝ)) hl

lemma square_power {z : ℂ} (hz : 0 < z.re) (s : ℂ) :
    (z^2)^(-s) = z^(-2*s) := by
  have h := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (.inl hz))
  rw [show -2*s = 2*(-s) by ring]
  exact (Complex.cpow_ofNat_mul' (n:=2) (by linarith [h.1]) (by linarith [h.2]) (-s)).symm

lemma reference_series {s : ℂ} (hs : 1/2 < s.re) :
    HasSum (fun n => reference n ^ (-2*s)) ((Real.pi:ℂ)^(-2*s)*riemannZeta (2*s)) := by
  have hh : 1 < (2*s).re := by simpa [Complex.mul_re] using (show 1 < 2*s.re by linarith)
  have hz := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.mpr hh)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hh]
  have hz' : Summable (fun n : ℕ => 1/(n+1:ℂ)^(2*s)) := by simpa using hz
  apply (hz'.hasSum.mul_left ((Real.pi:ℂ)^(-2*s))).congr_fun
  intro n
  rw [reference, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le
    (show 0 ≤ (n : ℝ)+1 by positivity)]
  simp only [Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
    one_div, show -2*s = -(2*s) by ring, Complex.cpow_neg]

lemma regularized_eq_original_strip {s : ℂ} (hs : 1/2 < s.re) (ht : s.re < 1) :
    regularized s = UnitSpectrum.continuation s := by
  let f : Unit ⊕ (ℕ ⊕ ℕ) → ℂ := fun j => UnitSpectrum.squaredRoot j ^ (-s)
  have h : HasSum f (UnitSpectrum.continuation s) := UnitSpectrum.root_hasSum hs ht
  have hx := h.summable.comp_injective (Sum.inr_injective (α:=Unit) (β:=ℕ ⊕ ℕ))
  have hu := hx.comp_injective (Sum.inl_injective (α:=ℕ) (β:=ℕ))
  have hl := hx.comp_injective (Sum.inr_injective (α:=ℕ) (β:=ℕ))
  have uu (n : ℕ) : f (.inr (.inl n)) = upper n ^ (-2*s) :=
    square_power (upper_re_pos n) s
  have ll (n : ℕ) : f (.inr (.inr n)) = conj (upper n) ^ (-2*s) := by
    change (conj ((upper n)^2))^(-s) = _
    rw [map_pow]
    exact square_power (by simpa using upper_re_pos n) s
  have dd : f (.inl ()) = (UnitSpectrum.dottie:ℂ)^(-2*s) := by
    change ((↑(UnitSpectrum.dottie ^ 2):ℂ))^(-s) = _
    rw [Complex.ofReal_pow]
    exact square_power UnitSpectrum.dottie_spec.1.1 s
  let a := ∑' n, f (.inr (.inl n))
  let b := ∑' n, f (.inr (.inr n))
  have hab : HasSum (fun n => upper n^(-2*s) + conj (upper n)^(-2*s)) (a+b) :=
    (hu.hasSum.add hl.hasSum).congr_fun (fun n => by simp [Function.comp_def, uu, ll])
  have hac : HasSum (fun n => levelDiff n s)
      ((a+b)-2*((Real.pi:ℂ)^(-2*s)*riemannZeta (2*s))) :=
    hab.sub ((reference_series hs).mul_left 2)
  have hid := h.tsum_eq.symm.trans (Summable.tsum_sum (f:=f) (h.summable.comp_injective Sum.inl_injective) hx)
  have hid' := Summable.tsum_sum (f:=f ∘ Sum.inr) hu hl
  simp only [tsum_fintype, Finset.univ_unique, Finset.sum_singleton] at hid
  change UnitSpectrum.continuation s = f (.inl ()) + _ at hid
  rw [dd] at hid
  change (∑' j, f (.inr j)) = a+b at hid'

  rw [hid'] at hid
  rw [regularized, hac.tsum_eq, hid]
  ring

def center (t : ℝ) : ℂ := ⟨1/2, t⟩
def window (t : ℝ) := Metric.ball (center t) (3/10)
def quarter (t : ℝ) : ℂ := ⟨1/4,t⟩
def seed (t : ℝ) : ℂ := ⟨3/4,t⟩

lemma quarter_mem (t : ℝ) : quarter t ∈ window t := by
  rw [window, Metric.mem_ball, dist_eq_norm]
  have h : quarter t - center t = ((-(1/4):ℝ):ℂ) := by
    apply Complex.ext <;> norm_num [quarter, center]
  rw [h, Complex.norm_real]; norm_num

lemma seed_mem (t : ℝ) : seed t ∈ window t := by
  rw [window, Metric.mem_ball, dist_eq_norm]
  have h : seed t - center t = ((1/4:ℝ):ℂ) := by
    apply Complex.ext <;> norm_num [seed,center]
  rw [h, Complex.norm_real]; norm_num

lemma window_bounds {s : ℂ} {t : ℝ} (hs : s ∈ window t) :
    1/5 < s.re ∧ ‖s‖ < ‖center t‖ + 1 ∧ |s.im-t| < 3/10 := by
  change dist s (center t) < 3/10 at hs
  rw [dist_eq_norm] at hs
  have h := (Complex.abs_re_le_norm (s-center t)).trans_lt hs
  have k := (Complex.abs_im_le_norm (s-center t)).trans_lt hs
  change |s.re - 1/2| < _ at h
  refine ⟨by linarith [(abs_lt.mp h).1], ?_, k⟩
  linarith [norm_sub_norm_le s (center t)]

lemma no_pole {s : ℂ} {t : ℝ} (ht : 1 ≤ |t|) (hs : s ∈ window t) : 2*s ≠ 1 := by
  intro he
  have him := congrArg Complex.im he
  simp [Complex.mul_im] at him
  have h := (window_bounds hs).2.2
  rw [show s.im = 0 by linarith, zero_sub, abs_neg] at h
  linarith

lemma diff_differentiable (n : ℕ) : Differentiable ℂ (levelDiff n) := by
  have un : upper n ≠ 0 := by intro h; have := upper_re_pos n; simp [h] at this
  have cn : conj (upper n) ≠ 0 := by simp [un]
  have rn : reference n ≠ 0 := by unfold reference; exact_mod_cast (show Real.pi * ((n:ℝ)+1) ≠ 0 by positivity)
  have f : Differentiable ℂ (fun s : ℂ => -2*s) := by fun_prop
  exact ((f.const_cpow (.inl un)).add (f.const_cpow (.inl cn))).sub
    ((differentiable_const (2 : ℂ)).mul (f.const_cpow (.inl rn)))

/-- Move the identity from its convergent Mellin strip to the quarter-line.
The sole input is a locally uniform series majorant for the shifted quartets. -/
theorem window_eq_of_majorant (t : ℝ) (ht : 1 ≤ |t|) {s : ℂ} (hs : s ∈ window t) {u : ℕ → ℝ}
    (hu : Summable u) (hbound : ∀ n s, s ∈ window t → ‖levelDiff (n+1) s‖ ≤ u n) :
    regularized s = UnitSpectrum.continuation s := by
  have openU : IsOpen (window t) := Metric.isOpen_ball
  have htSum := Complex.differentiableOn_tsum_of_summable_norm hu
    (fun n => (diff_differentiable (n+1)).differentiableOn (s := window t)) openU hbound
  have has (s : ℂ) (hs : s ∈ window t) : Summable (fun n => levelDiff n s) := by
    apply (summable_nat_add_iff 1).mp
    exact Summable.of_norm_bounded u hu (fun n => hbound n s hs)
  have regDiff : DifferentiableOn ℂ (fun s => ∑' n, levelDiff n s) (window t) :=
    ((diff_differentiable 0).differentiableOn.add htSum).congr
    (fun s hs => (has s hs).tsum_eq_zero_add)
  have huD : (UnitSpectrum.dottie:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr UnitSpectrum.dottie_spec.1.1.ne'
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have ex : Differentiable ℂ (fun s : ℂ => -2*s) := by fun_prop
  have zeta : DifferentiableOn ℂ (fun s : ℂ => riemannZeta (2*s)) (window t) :=
    fun z hz => ((Multiplicity.analytic_zeta (no_pole ht hz)).comp
      (Multiplicity.scale_analytic 2 z)).differentiableAt.differentiableWithinAt
  have hr : AnalyticOnNhd ℂ regularized (window t) := by
    apply DifferentiableOn.analyticOnNhd _ openU
    exact (((ex.const_cpow (.inl huD)).differentiableOn.add
      (((differentiableOn_const (2 : ℂ)).mul (ex.const_cpow (.inl hp)).differentiableOn).mul zeta)).add regDiff)
  have he : regularized =ᶠ[𝓝 (seed t)] UnitSpectrum.continuation := by
    have hlow : ∀ᶠ w : ℂ in 𝓝 (seed t), 1/2 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by change (1/2:ℝ) < 3/4; norm_num)
    have hhigh : ∀ᶠ w : ℂ in 𝓝 (seed t), w.re < 1 :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by change (3/4:ℝ) < 1; norm_num)
    filter_upwards [hlow,hhigh] with w hlo hhi using regularized_eq_original_strip hlo hhi
  exact hr.eqOn_of_preconnected_of_eventuallyEq
    (fun w hw => UnitSpectrum.continuation_analytic (no_pole ht hw))
    (convex_ball _ _).isPreconnected (seed_mem t) he hs

/-- For n=0 this estimates the second spectral level. -/
theorem levelDiff_le (n : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖levelDiff (n+1) s‖ ≤ 4*‖s‖*((n+2:ℕ):ℝ)^(-2*s.re-1) *
      Real.exp (11/10*|s.im|)*(4+Real.log (n+2:ℕ)) := by
  let k := n+2
  let t := UnitSpectrum.levelHeight (n+1)
  have hk : 2 ≤ k := by dsimp [k]; omega
  have ht := (UnitSpectrum.levelHeight_spec (n+1)).1
  have he : QuartetRadius.level t = 2*Real.pi*(k:ℝ) := by
    simpa [t,k, Nat.cast_add, add_assoc,one_add_one_eq_two] using (UnitSpectrum.levelHeight_spec (n+1)).2
  let z := upper (n+1)
  have re : z.re = RootBounds.x t := rfl
  have im : z.im = t := rfl
  have v := QuartetShiftBounds.endpoint_variation (z:=z) hk hs ht he re (im ▸ abs_of_pos ht)
  have w := QuartetShiftBounds.endpoint_variation (z:=conj z) hk hs ht he
    (by simpa using re) (by rw [Complex.conj_im, im, abs_neg, abs_of_pos ht])
  have hr : reference (n+1) = ((Real.pi*k:ℝ):ℂ) := by
    unfold reference k; push_cast; ring
  have h : levelDiff (n+1) s =
      (z^(-2*s)-reference (n+1)^(-2*s))+(conj z^(-2*s)-reference (n+1)^(-2*s)) := by
    unfold levelDiff; dsimp [z]; ring
  rw [h,hr]
  exact (norm_add_le _ _).trans ((add_le_add v w).trans_eq (by dsimp [k]; ring))

private lemma window_majorant (n : ℕ) {s : ℂ} {t : ℝ} (hs : s ∈ window t) :
    ‖levelDiff (n+1) s‖ ≤ (36*(‖center t‖+1)*Real.exp (11/10*(‖center t‖+1))) *
    ((n+2:ℕ):ℝ)^(-(6/5):ℝ) := by
  let m : ℝ := (n+2:ℕ)
  let M := ‖center t‖ + 1
  have hm : 1 ≤ m := by dsimp [m]; norm_cast; omega
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  obtain ⟨hσ,hM,_⟩ := window_bounds hs
  have h₁ : m^(-2*s.re-1) ≤ m^(-(7/5):ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hm (by linarith)
  have h₂ : Real.exp (11/10*|s.im|) ≤ Real.exp (11/10*M) := by
    apply Real.exp_le_exp.mpr
    have := Complex.abs_im_le_norm s
    dsimp [M]; linarith
  have hlog : 4 + Real.log m ≤ 9*m^((1/5):ℝ) := by
    have h := Real.log_le_rpow_div hm0.le (show (0:ℝ)<1/5 by norm_num)
    have k := Real.one_le_rpow hm (show (0:ℝ)≤1/5 by norm_num)
    linarith
  have h₃ := levelDiff_le n (s:=s) (by linarith)
  change _ ≤ 4*‖s‖*m^(-2*s.re-1)*Real.exp (11/10*|s.im|)*(4+Real.log m) at h₃
  apply h₃.trans
  calc
    _ ≤ 4*M*m^(-(7/5):ℝ)*Real.exp (11/10*M)*(9*m^(1/5:ℝ)) := by
      gcongr
    _ = _ := by
      change _ = 36*M*Real.exp (11/10*M)*m^(-(6/5):ℝ)
      rw [show (-(6/5):ℝ) = -(7/5)+1/5 by norm_num, Real.rpow_add hm0]
      ring

theorem levelDiff_summable_window {s : ℂ} {t : ℝ} (hs : s ∈ window t) :
    Summable (fun n => levelDiff (n+1) s) := by
  let c := 36*(‖center t‖+1)*Real.exp (11/10*(‖center t‖+1))
  have hM := (Real.summable_nat_rpow.mpr (show -(6/5:ℝ) < -1 by norm_num)).comp_injective
    (show Function.Injective (fun n : ℕ => n+2) from fun _ _ h => Nat.add_right_cancel h)
  apply Summable.of_norm_bounded _ (hM.mul_left c)
  exact fun n => window_majorant n hs

/-- The actual continued spectrum on Re(s)=1/4, after subtracting two copies
of the nth real reference level. No spectral hypothesis is required. -/
theorem window_identity {s : ℂ} {t : ℝ} (ht : 1 ≤ |t|) (hs : s ∈ window t) :
    UnitSpectrum.continuation s = regularized s := by
  let c := 36*(‖center t‖+1)*Real.exp (11/10*(‖center t‖+1))
  have hM := (Real.summable_nat_rpow.mpr (show -(6/5:ℝ) < -1 by norm_num)).comp_injective
    (show Function.Injective (fun n : ℕ => n+2) from fun _ _ h => Nat.add_right_cancel h)
  exact (window_eq_of_majorant t ht hs (hM.mul_left c) (fun n s hs => window_majorant n hs)).symm

theorem quarter_identity (t : ℝ) (ht : 1 ≤ |t|) :
    UnitSpectrum.continuation (quarter t) = regularized (quarter t) :=
  window_identity ht (quarter_mem t)

/-- Isolate the first upper root and leave the entire remaining family in
the summable real-reference differences. -/
theorem quarter_sub_leading_eq (t : ℝ) (ht : 1 ≤ |t|) :
    let s := quarter t
    UnitSpectrum.continuation s - upper 0 ^ (-2*s) =
      (UnitSpectrum.dottie:ℂ)^(-2*s) + 2*(Real.pi:ℂ)^(-2*s)*riemannZeta (2*s) +
      (conj (upper 0)^(-2*s) - 2*(Real.pi:ℂ)^(-2*s)) +
      ∑' n, levelDiff (n+1) s := by
  dsimp only
  rw [quarter_identity t ht,regularized]
  have hsum : Summable (fun n => levelDiff n (quarter t)) :=
    (summable_nat_add_iff 1).mp (levelDiff_summable_window (quarter_mem t))
  rw [hsum.tsum_eq_zero_add]
  unfold levelDiff
  simp only [reference,Nat.cast_zero,zero_add,mul_one]
  ring

/-- At negative heights the lower member grows. The same decomposition
isolates that member explicitly. -/
theorem quarter_sub_conj_leading_eq (t : ℝ) (ht : 1 ≤ |t|) :
    let s := quarter t
    UnitSpectrum.continuation s - conj (upper 0) ^ (-2*s) =
      (UnitSpectrum.dottie:ℂ)^(-2*s) + 2*(Real.pi:ℂ)^(-2*s)*riemannZeta (2*s) +
      (upper 0^(-2*s) - 2*(Real.pi:ℂ)^(-2*s)) +
      ∑' n, levelDiff (n+1) s := by
  dsimp only
  linear_combination quarter_sub_leading_eq t ht

theorem band_sub_leading_eq {s : ℂ} (hl : 7/32 ≤ s.re) (hr : s.re ≤ 9/32) (ht : 100 ≤ s.im) :
    UnitSpectrum.continuation s - upper 0 ^ (-2*s) =
      (UnitSpectrum.dottie:ℂ)^(-2*s) + 2*(Real.pi:ℂ)^(-2*s)*riemannZeta (2*s) +
      (conj (upper 0)^(-2*s) - 2*(Real.pi:ℂ)^(-2*s)) +
      ∑' n, levelDiff (n+1) s := by
  have mem : s ∈ window s.im := by
    rw [window,Metric.mem_ball,dist_eq_norm]
    have h : s - center s.im = ((s.re - 1/2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [center]
    rw [h,Complex.norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith
  have habs : 1 ≤ |s.im| := le_trans (by linarith) (le_abs_self s.im)
  rw [window_identity habs mem, regularized]
  have hsum : Summable (fun n => levelDiff n s) :=
    (summable_nat_add_iff 1).mp (levelDiff_summable_window mem)
  rw [hsum.tsum_eq_zero_add]
  unfold levelDiff
  simp only [reference,Nat.cast_zero,zero_add,mul_one]
  ring

end SuperZeta.QuartetShiftContinuation
