import SuperZeta.QuartetRate
import SuperZeta.StirlingExpansion
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! The first polar term of the central-binomial deformation for the actual
characteristic levels. The remaining series is holomorphic in Re(s) > -1/4
for each fixed deformation parameter and along the spectral diagonal. -/
namespace SuperZeta.DeformedZeta

open Filter Set Real
open scoped Topology
noncomputable section

open StirlingCorrection

def RootSelection (t : ℕ → ℝ) : Prop :=
  ∀ n, 0<n → 0<t n ∧ QuartetRadius.level (t n)=2*π*n

/-- The positive weight from the radius and central-binomial coefficient. -/
def weight (t : ℕ → ℝ) (n : ℕ) : ℝ := C (QuartetRadius.radius ∘ t) n

theorem log_weight_bound {t : ℕ → ℝ} (roots : RootSelection t) :
    ∀ᶠ n : ℕ in atTop, |log (weight t n)+1/(4*(n:ℝ))| ≤ 4*(n:ℝ)^(-(3/2:ℝ)) := by
  filter_upwards [QuartetRadius.log_radial_bound roots, eventually_gt_atTop (0:ℕ)] with n h hn
  have hn1 : 1≤(n:ℝ) := by exact_mod_cast hn
  have hn0 : 0<(n:ℝ) := by positivity
  obtain ⟨hl, hu⟩ := first_remainder_nat hn
  rw [weight, C_eq _ hn, log_mul (by dsimp [Function.comp_def]; unfold QuartetRadius.radius; positivity)
    (D_pos hn).ne', Function.comp_apply, add_assoc]
  have ht : 1/(96*(n:ℝ)^3) ≤ (n:ℝ)^(-(3/2:ℝ)) := by
    calc
      _ ≤ 1/(n:ℝ)^3 := one_div_le_one_div_of_le (by positivity) (by nlinarith [pow_nonneg hn0.le 3])
      _ = (n:ℝ)^(-(3:ℝ)) := by
        rw [rpow_neg hn0.le, ← Nat.cast_ofNat (R:=ℝ) (n:=3), rpow_natCast, one_div]
      _ ≤ _ := rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hd : |log (Barnes.D n)+1/(4*(n:ℝ))| ≤ (n:ℝ)^(-(3/2:ℝ)) := by
    rw [abs_of_nonneg hl]
    exact hu.trans ht
  exact (abs_add_le _ _).trans ((add_le_add h hd).trans_eq (by ring))

private def index (n : ℕ) : ℝ := ((n+1:ℕ):ℝ)
private def logWeight (t : ℕ → ℝ) (n : ℕ) : ℝ := log (weight t (n+1))
private def base (n : ℕ) (s : ℂ) : ℂ := (index n:ℂ)^(-s)
private def term (t : ℕ → ℝ) (n : ℕ) (ν s : ℂ) : ℂ :=
  base n s * Complex.exp (ν*(logWeight t n:ℂ))
private def defect (t : ℕ → ℝ) (n : ℕ) (ν s : ℂ) : ℂ :=
  base n s *(Complex.exp (ν*(logWeight t n:ℂ))-1+ν/(4*(index n:ℂ)))

private theorem index_pos (n : ℕ) : 0 < index n := by unfold index; positivity
private theorem index_ge_one (n : ℕ) : 1 ≤ index n := by unfold index; exact_mod_cast Nat.succ_pos n
private theorem index_ne (n : ℕ) : (index n:ℂ) ≠ 0 := by exact_mod_cast (index_pos n).ne'

private theorem base_bound {s : ℂ} (hs : -1/4<s.re) (n : ℕ) : ‖base n s‖ ≤ index n^(1/4:ℝ) := by
  rw [base, Complex.norm_cpow_eq_rpow_re_of_pos (index_pos n), Complex.neg_re]
  exact rpow_le_rpow_of_exponent_le (index_ge_one n) (by linarith)

private theorem good_indices {t : ℕ → ℝ} (roots : RootSelection t) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, |logWeight t n+1/(4*index n)| ≤ 4*index n^(-(3/2:ℝ)) ∧
      |logWeight t n| ≤ 5/index n ∧ 5*B ≤ index n := by
  have hs : Tendsto (fun n : ℕ => n+1) atTop atTop := tendsto_add_atTop_nat 1
  have he : Tendsto index atTop atTop := tendsto_natCast_atTop_atTop.comp hs
  filter_upwards [hs.eventually (log_weight_bound roots), he.eventually_ge_atTop (5*B)] with n h hsize
  change |logWeight t n+1/(4*index n)| ≤ 4*index n^(-(3/2:ℝ)) at h
  refine ⟨h, ?_, hsize⟩
  have hpow : index n^(-(3/2:ℝ)) ≤ 1/index n := by
    rw [one_div, ← rpow_neg_one]
    exact rpow_le_rpow_of_exponent_le (index_ge_one n) (by norm_num)
  calc
    _ = |(logWeight t n+1/(4*index n))-1/(4*index n)| := by congr 1; ring
    _ ≤ |logWeight t n+1/(4*index n)|+|1/(4*index n)| := abs_sub _ _
    _ ≤ 4*(1/index n)+1/(4*index n) :=
      add_le_add (h.trans (mul_le_mul_of_nonneg_left hpow (by norm_num)))
        (le_of_eq (abs_of_pos (one_div_pos.mpr (mul_pos (by norm_num) (index_pos n)))))
    _ ≤ _ := by
      rw [mul_one_div, ← div_div (1:ℝ) 4, ← add_div]
      exact div_le_div_of_nonneg_right (by norm_num) (index_pos n).le

private theorem defect_bound {t : ℕ → ℝ} {B : ℝ} (hB : 0≤B) {ν s : ℂ}
    (hν : ‖ν‖≤B) (hs : -1/4<s.re) (n : ℕ)
    (h : |logWeight t n+1/(4*index n)| ≤ 4*index n^(-(3/2:ℝ)))
    (hb : |logWeight t n| ≤ 5/index n) (hx : 5*B ≤ index n) :
    ‖defect t n ν s‖ ≤ (25*B^2+4*B)*index n^(-(5/4:ℝ)) := by
  let x := index n
  have xp : 0<x := index_pos n
  let p := ν*(logWeight t n:ℂ)
  have hsmall : ‖p‖ ≤ 5*B/x := by
    dsimp only [p]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ B*(5/x) := mul_le_mul hν hb (abs_nonneg _) hB
      _ = _ := by ring
  have hseries := Complex.norm_exp_sub_one_sub_id_le
    (hsmall.trans ((div_le_one xp).mpr hx))
  have hsq : ‖p‖^2 ≤ 25*B^2 * x^(-(3/2:ℝ)) := by
    calc
      _ ≤ (5*B/x)^2 := pow_le_pow_left₀ (norm_nonneg _) hsmall 2
      _ = 25*B^2*x^(-(2:ℝ)) := by rw [rpow_neg xp.le, rpow_two]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_exponent_le (index_ge_one n) (by norm_num)) (by positivity)
  have hlinear : ‖p+ν/(4*(index n:ℂ))‖ ≤ 4*B*x^(-(3/2:ℝ)) := by
    rw [show p+ν/(4*(index n:ℂ)) = ν*((logWeight t n+1/(4*index n):ℝ):ℂ) by
      simp only [p]
      push_cast
      ring, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul hν h (abs_nonneg _) hB).trans_eq (by dsimp only [x]; ring)
  have hb' : ‖Complex.exp p-1+ν/(4*(index n:ℂ))‖ ≤ (25*B^2+4*B)*x^(-(3/2:ℝ)) := by
    rw [show Complex.exp p-1+ν/(4*(index n:ℂ)) =
      (Complex.exp p-1-p)+(p+ν/(4*(index n:ℂ))) by ring]
    exact (norm_add_le _ _).trans ((add_le_add (hseries.trans hsq) hlinear).trans_eq (by ring))
  rw [defect, norm_mul]
  calc
    _ ≤ x^(1/4:ℝ)*((25*B^2+4*B)*x^(-(3/2:ℝ))) :=
      mul_le_mul (base_bound hs n) hb' (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_left_comm, ← rpow_add xp, show (1/4:ℝ)+ -(3/2)= -(5/4) by norm_num]

private theorem defect_bound_finite {t : ℕ → ℝ} {B : ℝ} {ν s : ℂ}
    (hν : ‖ν‖≤B) (hs : -1/4<s.re) (n : ℕ) :
    ‖defect t n ν s‖ ≤ index n^(1/4:ℝ)*
      (exp (B*|logWeight t n|)+1+B/(4*index n)) := by
  have he : ‖Complex.exp (ν*(logWeight t n:ℂ))‖ ≤ exp (B*|logWeight t n|) := by
    rw [Complex.norm_exp]
    apply exp_le_exp.mpr
    exact (Complex.re_le_norm _).trans (by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hν (abs_nonneg _))
  have hv : ‖ν/(4*(index n:ℂ))‖ ≤ B/(4*index n) := by
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (index_pos n)]
    norm_num
    exact div_le_div_of_nonneg_right hν (mul_nonneg (by norm_num) (index_pos n).le)
  rw [defect, norm_mul]
  apply mul_le_mul (base_bound hs n) _ (norm_nonneg _)
    (rpow_nonneg (index_pos n).le _)
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add_right he 1)) hv)

/-- For a bounded deformation parameter the subtracted terms have a
summable majorant, uniform in the indicated half-plane. -/
private theorem summable_majorant {t : ℕ → ℝ} (roots : RootSelection t) {B : ℝ} (hB : 0≤B) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n ν s, ‖ν‖≤B → -1/4<s.re → ‖defect t n ν s‖≤u n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (good_indices roots B)
  let fin (n : ℕ) := if n<N then index n^(1/4:ℝ)*
    (exp (B*|logWeight t n|)+1+B/(4*index n)) else 0
  let tail (n : ℕ) := (25*B^2+4*B)*index n^(-(5/4:ℝ))
  have ht : Summable tail := by
    have h := Real.summable_nat_rpow.mpr (by norm_num : -(5/4:ℝ) < -1)
    exact (h.comp_injective Nat.succ_injective).mul_left _
  have hf : Summable fin := by
    apply summable_of_ne_finset_zero (s:=Finset.range N)
    intro n hn
    simp [fin, (show ¬n<N by simpa only [Finset.mem_range] using hn)]
  refine ⟨fun n => tail n+fin n, ht.add hf, ?_⟩
  intro n ν s hν hs
  by_cases hn : n<N
  · change ‖defect t n ν s‖ ≤ tail n+fin n
    simp only [fin, if_pos hn]
    exact (defect_bound_finite hν hs n).trans (le_add_of_nonneg_left (by
      dsimp [tail]
      exact mul_nonneg (by positivity) (rpow_nonneg (index_pos n).le _)))
  · have h := hN n (Nat.le_of_not_gt hn)
    simpa [fin, hn, tail] using defect_bound hB hν hs n h.1 h.2.1 h.2.2

/-- The original deformation series, indexed from the first positive quartet level. -/
def dirichletSeries (t : ℕ → ℝ) (ν s : ℂ) : ℂ := ∑' n : ℕ, term t n ν s

/-- Subtract the constant coefficient and the leading factorial coefficient. -/
def remainder (t : ℕ → ℝ) (ν s : ℂ) : ℂ := ∑' n : ℕ, defect t n ν s

theorem defect_summable {t : ℕ → ℝ} (roots : RootSelection t)
    {ν s : ℂ} (hs : -1/4<s.re) : Summable (fun n => defect t n ν s) := by
  obtain ⟨u, hu, hb⟩ := summable_majorant roots (norm_nonneg ν)
  exact Summable.of_norm_bounded u hu (fun n => hb n ν s le_rfl hs)

theorem remainder_differentiable {t : ℕ → ℝ} (roots : RootSelection t)
    {ν : ℂ → ℂ} (hν : Differentiable ℂ ν) {s : ℂ} (hs : -1/4<s.re) :
    DifferentiableAt ℂ (fun z => remainder t (ν z) z) s := by
  let B := ‖ν s‖+1
  let U := {z : ℂ | -1/4 < z.re} ∩ ν ⁻¹' Metric.ball 0 B
  have hu : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (Metric.isOpen_ball.preimage hν.continuous)
  have hmem : s ∈ U := ⟨hs, by simp [Metric.mem_ball, B]⟩
  obtain ⟨bound, hsum, hbound⟩ := summable_majorant roots (show 0≤B by dsimp [B]; positivity)
  have hd (n : ℕ) : DifferentiableOn ℂ (fun z => defect t n (ν z) z) U := by
    have hg : Differentiable ℂ (fun z : ℂ => base n z) := by
      intro z
      exact differentiableAt_id.neg.const_cpow (Or.inl (index_ne n))
    unfold defect
    exact (hg.mul (((hν.mul_const _).cexp.sub_const 1).add (hν.div_const _))).differentiableOn
  apply (Complex.differentiableOn_tsum_of_summable_norm hsum hd hu ?_ s hmem).differentiableAt
    (hu.mem_nhds hmem)
  intro n z hz
  exact hbound n (ν z) z (le_of_lt (by simpa [Metric.mem_ball] using hz.2)) hz.1

/-- Meromorphic expression obtained by restoring the two subtracted terms. -/
def continuation (t : ℕ → ℝ) (ν s : ℂ) : ℂ :=
  riemannZeta s - (ν/4)*riemannZeta (s+1) + remainder t ν s

theorem continuation_differentiable {t : ℕ → ℝ} (roots : RootSelection t)
    {ν : ℂ → ℂ} (hν : Differentiable ℂ ν) {s : ℂ}
    (hs : -1/4<s.re) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    DifferentiableAt ℂ (fun z => continuation t (ν z) z) s := by
  have h : s+1 ≠ 1 := by simpa using h0
  have hz := (differentiableAt_riemannZeta h).comp s (differentiableAt_id.add_const 1)
  exact ((differentiableAt_riemannZeta h1).sub (((hν s).div_const 4).mul hz)).add
    (remainder_differentiable roots hν hs)

private theorem base_sum {s : ℂ} (hs : 1<s.re) : HasSum (fun n => base n s) (riemannZeta s) := by
  have h := ((Complex.summable_one_div_nat_cpow (p:=s)).mpr hs).comp_injective Nat.succ_injective
  have h' : Summable (fun n : ℕ => 1/((n:ℂ)+1)^s) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using h
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  simpa [base, index, Complex.cpow_neg, one_div] using h'.hasSum

private theorem shift_base (n : ℕ) (s : ℂ) :
    base n (s+1) = base n s/(index n:ℂ) := by
  rw [base, base, neg_add, Complex.cpow_add _ _ (index_ne n), Complex.cpow_neg_one, div_eq_mul_inv]

theorem series_hasSum {t : ℕ → ℝ} (roots : RootSelection t) {ν s : ℂ} (hs : 1<s.re) :
    HasSum (fun n => term t n ν s) (continuation t ν s) := by
  have h₁ := base_sum (s:=s) hs
  have h₂ := base_sum (s:=s+1) (by simp; linarith [hs])
  have h₃ := (defect_summable (ν:=ν) roots (by linarith : -1/4<s.re)).hasSum
  have h := (h₁.sub (h₂.mul_left (ν/4))).add h₃
  convert h using 1
  funext n
  rw [shift_base, term, defect]
  ring

theorem continuation_eq_series {t : ℕ → ℝ} (roots : RootSelection t) {ν s : ℂ} (hs : 1<s.re) :
    continuation t ν s = dirichletSeries t ν s := (series_hasSum roots hs).tsum_eq.symm

private theorem shifted_residue :
    Tendsto (fun s : ℂ => s*riemannZeta (s+1)) (𝓝[≠] 0) (𝓝 1) := by
  have h : ContinuousWithinAt (fun s : ℂ => s+1) {0}ᶜ 0 :=
    (continuous_id.add continuous_const).continuousWithinAt
  have map_limit : Tendsto (fun s : ℂ => s+1) (𝓝[≠] 0) (𝓝[≠] 1) := by
    convert h.tendsto_nhdsWithin (t:={1}ᶜ) (by simp [MapsTo]) using 1
    norm_num
  simpa [Function.comp_def] using riemannZeta_residue_one.comp map_limit

/-- The residue at zero is precisely the signed leading Stirling coefficient
times the deformation parameter. -/
theorem residue_zero {t : ℕ → ℝ} (roots : RootSelection t) (ν : ℂ) :
    Tendsto (fun s : ℂ => s*continuation t ν s) (𝓝[≠] 0) (𝓝 (-ν/4)) := by
  have hr := (remainder_differentiable (ν:=fun _ => ν) roots (differentiable_const ν)
    (s:=0) (by norm_num)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s:={(0:ℂ)}ᶜ))
  have hz := (differentiableAt_riemannZeta (s:=0) (by norm_num)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s:={(0:ℂ)}ᶜ))
  have hi : Tendsto (fun s : ℂ => s) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h := ((hi.mul hz).sub (shifted_residue.const_mul (ν/4))).add (hi.mul hr)
  convert h using 1
  · funext s; unfold continuation; ring
  · ring_nf

/-- The zero of the deformation parameter along the diagonal cancels the
pole. Its finite limit is -1/4, the regularized value of the linear spectrum. -/
theorem diagonal_limit_zero {t : ℕ → ℝ} (roots : RootSelection t) :
    Tendsto (fun s : ℂ => continuation t (-s) s) (𝓝[≠] 0) (𝓝 (-1/4)) := by
  have hr := (remainder_differentiable (ν:=fun z => -z) roots differentiable_neg
    (s:=0) (by norm_num)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s:={(0:ℂ)}ᶜ))
  have hz := (differentiableAt_riemannZeta (s:=0) (by norm_num)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (s:={(0:ℂ)}ᶜ))
  have h := (hz.add (shifted_residue.div_const 4)).add hr
  convert h using 1
  · funext s; unfold continuation; ring
  · have h0 : remainder t 0 0=0 := by simp [remainder, defect]
    norm_num [h0, riemannZeta_zero]

/-- The analytically extended diagonal, with its regularized value at zero. -/
def spectralZeta (t : ℕ → ℝ) : ℂ → ℂ :=
  Function.update (fun s => continuation t (-s) s) 0 (-1/4)

theorem spectralZeta_zero (t : ℕ → ℝ) : spectralZeta t 0 = -1/4 := by
  simp [spectralZeta]

theorem spectralZeta_analyticAt_zero {t : ℕ → ℝ} (roots : RootSelection t) :
    AnalyticAt ℂ (spectralZeta t) 0 := by
  let f := fun s : ℂ => continuation t (-s) s
  have hl : Tendsto f (𝓝[≠] 0) (𝓝 (-1/4)) := diagonal_limit_zero roots
  have hb : ∀ᶠ s in 𝓝[≠] (0:ℂ), ‖f s‖ ≤ 1 :=
    (hl.norm.eventually_lt_const (by norm_num : ‖(-1/4:ℂ)‖ < 1)).mono fun _ hs => hs.le
  have hnear : ∀ᶠ s : ℂ in 𝓝 0, -1/4 < s.re ∧ s ≠ 1 := by
    apply ((isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton).mem_nhds
    change (-1/4:ℝ) < (0:ℂ).re ∧ (0:ℂ) ≠ 1
    norm_num
  let U : Set ℂ := {s | (-1/4 < s.re ∧ s ≠ 1) ∧ (s ≠ 0 → ‖f s‖≤1)}
  have hU : U ∈ 𝓝 0 := hnear.and (eventually_nhdsWithin_iff.mp hb)
  have hd : DifferentiableOn ℂ f (U \ {0}) := fun _ hz =>
    (continuation_differentiable roots differentiable_neg hz.1.1.1 hz.2 hz.1.1.2).differentiableWithinAt
  have hc : BddAbove (norm ∘ f '' (U \ {0})) := by
    refine ⟨1, ?_⟩
    rintro y ⟨z,hz,rfl⟩
    exact hz.1.2 hz.2
  have h := Complex.differentiableOn_update_limUnder_of_bddAbove hU hd hc
  rw [hl.limUnder_eq] at h
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have hInt := isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU)
  filter_upwards [hInt] with z hz
  exact h.differentiableAt (mem_interior_iff_mem_nhds.mp hz)

theorem spectralZeta_eq_series {t : ℕ → ℝ} (roots : RootSelection t) {s : ℂ} (hs : 1<s.re) :
    spectralZeta t s = ∑' n : ℕ, ((index n * weight t (n+1):ℝ):ℂ)^(-s) := by
  have h0 : s ≠ 0 := by intro he; subst s; norm_num at hs
  rw [spectralZeta, Function.update_of_ne h0, continuation_eq_series roots hs, dirichletSeries]
  apply tsum_congr
  intro n
  have hw : 0 < weight t (n+1) := C_pos (exp_pos _)
  have hp : (((index n * weight t (n+1)):ℝ):ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (index_pos n) hw).ne'
  rw [term, base, Complex.cpow_def_of_ne_zero (index_ne n),
    Complex.cpow_def_of_ne_zero hp, ← Complex.ofReal_log (index_pos n).le,
    ← Complex.ofReal_log (mul_pos (index_pos n) hw).le,
    log_mul (index_pos n).ne' hw.ne', Complex.ofReal_add, ← Complex.exp_add, logWeight]
  congr 1
  ring

end
end SuperZeta.DeformedZeta
