import SuperZeta.Barnes
import SuperZeta.Quartet
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Pi.Bounds

/-! The quarter shift for the geometric radii. The level equation is
2(θ + cosh(t) sin(θ)) − π = 2πn, with cos(θ) = −t/sinh(t). -/
namespace SuperZeta.QuartetRadius
open Filter Real
open scoped Topology
noncomputable section

def a (t : ℝ) := t / sinh t
def θ (t : ℝ) := arccos (-(a t))
def level (t : ℝ) := 2*(θ t + cosh t * sin (θ t)) - π
def radius (t : ℝ) := exp (t * (cosh t / sinh t))

/-- The outer root with positive argument in the classified quartet. -/
def polarPhase (t : ℝ) := Complex.exp ⟨t, θ t⟩

private lemma angle_cos {t : ℝ} (ht : 0<t) : cos (θ t) = -(a t) := by
  have hp : 0 ≤ a t := div_nonneg ht.le (sinh_pos_iff.mpr ht).le
  have hq : a t ≤ 1 := (div_le_one (sinh_pos_iff.mpr ht)).mpr (self_le_sinh_iff.mpr ht.le)
  exact cos_arccos (by linarith) (by linarith)

/-- Every positive solution of the real phase equation gives an actual complex
multiplier-one characteristic root. -/
theorem characteristic_of_level {n : ℕ} {t : ℝ} (ht : 0<t)
    (hl : level t=2*π*n) : Quartet.characteristic (polarPhase t) := by
  have hprod : sinh t * a t = t := by
    unfold a
    field_simp [(sinh_pos_iff.mpr ht).ne']
  rw [sinh_eq] at hprod
  unfold level at hl
  rw [cosh_eq] at hl
  let z : ℂ := ⟨t,θ t⟩
  have he : 2*z + Complex.exp z - Complex.exp (-z) =
      (π:ℂ)*Complex.I + (n:ℂ)*(2*π*Complex.I) := by
    apply Complex.ext
    · simp [z, Complex.exp_re, Complex.mul_re,angle_cos ht]
      linarith
    · simp [z, Complex.exp_im, Complex.mul_im]
      linarith
  change Complex.exp z ^ 2 * Complex.exp (Complex.exp z - (Complex.exp z)⁻¹) = -1
  rw [← Complex.exp_neg, ← Complex.exp_nat_mul, ← Complex.exp_add]
  rw [show (2:ℕ) * z + (Complex.exp z - Complex.exp (-z)) =
    2*z + Complex.exp z - Complex.exp (-z) by push_cast; ring, he, Complex.exp_add,
    Complex.exp_pi_mul_I, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem a_rescaled {t : ℝ} (h : 0<t) :
    a t = (2*(t*exp (-t))) / (1-exp (-t)^2) := by
  have p : exp (-t)<1 := exp_lt_one_iff.mpr (by linarith)
  have d : 1-exp (-t)^2 ≠ 0 := by nlinarith [exp_pos (-t)]
  have s := (sinh_pos_iff.mpr h).ne'
  unfold a
  field_simp [s,d]
  rw [sinh_eq, exp_neg]
  field_simp
  ring

private theorem decay_a : Tendsto a atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (2:ℝ)).div
    (tendsto_const_nhds.sub (tendsto_exp_neg_atTop_nhds_zero.pow 2))
    (show (1:ℝ)-0^2 ≠ 0 by norm_num)
  apply (show Tendsto (fun t : ℝ => (2*(t*exp (-t))) / (1-exp (-t)^2)) atTop (𝓝 0) by
    simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht using (a_rescaled ht).symm

private theorem decay_quadratic :
    Tendsto (fun t : ℝ => exp t * a t^2) atTop (𝓝 0) := by
  have h := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul (4:ℝ)).div
    ((tendsto_const_nhds.sub (tendsto_exp_neg_atTop_nhds_zero.pow 2)).pow 2)
    (show ((1:ℝ)-0^2)^2 ≠ 0 by norm_num)
  apply (show Tendsto (fun t : ℝ => 4*(t^2*exp (-t))/(1-exp (-t)^2)^2) atTop (𝓝 0) by
    simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  rw [a_rescaled ht, div_pow, ← mul_div_assoc]
  congr 1
  rw [exp_neg]
  field_simp
  ring

private theorem decay_angle : Tendsto θ atTop (𝓝 (π/2)) := by
  simpa [θ, Function.comp_def, arccos_zero] using continuous_arccos.continuousAt.tendsto.comp decay_a.neg

private theorem decay_sine : Tendsto (fun t => sin (θ t)) atTop (𝓝 1) := by
  simpa [Function.comp_def] using continuous_sin.continuousAt.tendsto.comp decay_angle

private theorem sin_defect :
    Tendsto (fun t => exp t * (1-sin (θ t))) atTop (𝓝 0) := by
  have h := decay_quadratic.div (tendsto_const_nhds.add decay_sine)
    (show (1:ℝ)+1 ≠ 0 by norm_num)
  apply (show Tendsto (fun t => (exp t * a t^2)/(1+sin (θ t))) atTop (𝓝 0) by
    simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
  have apos : 0 ≤ a t := div_nonneg ht.le (sinh_pos_iff.mpr ht).le
  have ale : a t ≤ 1 := (div_le_one (sinh_pos_iff.mpr ht)).mpr (self_le_sinh_iff.mpr ht.le)
  have hc : cos (θ t) = -a t := cos_arccos (by linarith) (by linarith)
  have hs : 0 ≤ sin (θ t) := by rw [θ,sin_arccos]; positivity
  rw [div_eq_iff (by positivity : 1+sin (θ t) ≠ 0)]
  have hsq := sin_sq_add_cos_sq (θ t)
  rw [hc, neg_sq] at hsq
  linear_combination exp t * hsq

/-- The characteristic level and the elementary exponential differ by a vanishing
additive error, even before restricting to integer levels. -/
theorem level_error : Tendsto (fun t => level t-exp t) atTop (𝓝 0) := by
  have h := (((decay_angle.const_mul 2).sub_const π).sub sin_defect).add
    (tendsto_exp_neg_atTop_nhds_zero.mul decay_sine)
  convert h using 1
  · funext t
    simp only [level, cosh_eq]
    ring
  · ring_nf

theorem exponent_identity {t : ℝ} (ht : 0<t) :
    t*(cosh t / sinh t) = t + a t*exp (-t) := by
  unfold a
  field_simp [(sinh_pos_iff.mpr ht).ne']
  rw [cosh_eq, sinh_eq]
  ring

/-- Norm of the recovered parameter L=α/exp(1/α) from the original return. -/
theorem recovered_norm {t : ℝ} (ht : 0<t) :
    ‖polarPhase t / Complex.exp (polarPhase t)⁻¹‖ = radius t := by
  unfold polarPhase
  rw [norm_div, ← Complex.exp_neg, Complex.norm_exp, Complex.norm_exp,
    ← Real.exp_sub, Complex.exp_re]
  change exp (t-exp (-t)*cos (-θ t)) = radius t
  rw [cos_neg,angle_cos ht,radius,exponent_identity ht]
  congr 1
  ring

theorem radius_error : Tendsto (fun t => radius t-exp t) atTop (𝓝 0) := by
  have z := decay_a.mul tendsto_exp_neg_atTop_nhds_zero
  have z' : Tendsto (fun t => a t*exp (-t)) atTop (𝓝 0) := by simpa using z
  have bound := z'.eventually_lt_const (show (0:ℝ)<1 by norm_num)
  apply squeeze_zero_norm' _ (show Tendsto (fun t => 2*a t) atTop (𝓝 0) by
    simpa using decay_a.const_mul 2)
  filter_upwards [eventually_gt_atTop (0:ℝ),bound] with t ht hb
  have ha : 0 ≤ a t := div_nonneg ht.le (sinh_pos_iff.mpr ht).le
  have hp : 0 ≤ a t * exp (-t) := mul_nonneg ha (exp_pos _).le
  rw [radius, exponent_identity ht, exp_add, ← mul_sub_one, Real.norm_eq_abs,
    abs_mul, abs_of_pos (exp_pos _)]
  have e := abs_exp_sub_one_le (x:=a t*exp (-t)) (by rw [abs_of_nonneg hp]; exact hb.le)
  rw [abs_of_nonneg hp] at e
  calc
    _ ≤ exp t*(2*(a t*exp (-t))) := mul_le_mul_of_nonneg_left e (exp_pos _).le
    _ = 2*a t := by rw [exp_neg]; field_simp

private theorem level_upper (t : ℝ) : level t ≤ π+2*cosh t := by
  unfold level
  have h := mul_le_mul_of_nonneg_left (sin_le_one (θ t)) (cosh_pos t).le
  have k := arccos_le_pi (-(a t))
  change θ t ≤ π at k
  linarith

private theorem level_unbounded : Tendsto level atTop atTop := by
  exact (tendsto_exp_atTop.atTop_add level_error).congr fun t => by ring

/-- Existence for each strictly positive quartet index, directly from its continuous
phase equation. The subsequent estimates apply to every choice of positive roots. -/
theorem exists_level (n : ℕ) (hn : 0<n) : ∃ t : ℝ, 0<t ∧ level t=2*π*n := by
  have hstart : level (1/4) ≤ 2*π*n := by
    have h := level_upper (1/4)
    have e := exp_bound_div_one_sub_of_interval (x := (1/4:ℝ)) (by norm_num) (by norm_num)
    have e' : exp (-(1/4:ℝ)) ≤ exp (1/4) := exp_le_exp.mpr (by norm_num)
    rw [cosh_eq] at h
    have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hπ := mul_le_mul_of_nonneg_left hn' pi_pos.le
    nlinarith [pi_gt_three]
  obtain ⟨b, hb, hlevel⟩ := ((eventually_ge_atTop (1/4:ℝ)).and
    (level_unbounded.eventually_ge_atTop (2*π*n))).exists
  have hc : ContinuousOn level (Set.Icc (1/4) b) := by
    intro t ht
    have hs : sinh t ≠ 0 := (sinh_pos_iff.mpr (show 0<t by linarith [ht.1])).ne'
    have hat : ContinuousAt a t := continuousAt_id.div continuous_sinh.continuousAt hs
    have hθ : ContinuousAt θ t := continuous_arccos.continuousAt.comp hat.neg
    exact ((continuousAt_const.mul (hθ.add (continuous_cosh.continuousAt.mul
      (continuous_sin.continuousAt.comp hθ)))).sub continuousAt_const).continuousWithinAt
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hb hc (show 2*π*(n:ℝ) ∈
    Set.Icc (level (1/4)) (level b) from ⟨hstart,hlevel⟩)
  exact ⟨t,by linarith [ht.1],he⟩

/-- The level equation itself forces all positive selections to escape to infinity. -/
theorem roots_unbounded {t : ℕ → ℝ}
    (roots : ∀ n, 0<n → 0<t n ∧ level (t n)=2*π*n) : Tendsto t atTop atTop := by
  apply tendsto_atTop.2
  intro b
  have hh := (tendsto_natCast_atTop_atTop.const_mul_atTop (show 0<2*π by positivity)).eventually_gt_atTop
    (π+2*cosh b)
  filter_upwards [hh,eventually_gt_atTop (0:ℕ)] with n hn hpos
  obtain ⟨ht,he⟩ := roots n hpos
  by_contra! h
  have hc : cosh (t n) ≤ cosh b := cosh_le_cosh.mpr (by
    rw [abs_of_pos ht, abs_of_pos (lt_trans ht h)]; exact h.le)
  have hu := level_upper (t n)
  rw [he] at hu
  linarith

/-- The radii approach the grid with an additive error tending to zero. -/
theorem radial_error {t : ℕ → ℝ}
    (roots : ∀ n, 0<n → 0<t n ∧ level (t n)=2*π*n) :
    Tendsto (fun n : ℕ => radius (t n) - 2*π*n) atTop (𝓝 0) := by
  have h := (radius_error.sub level_error).comp (roots_unbounded roots)
  apply (show Tendsto (fun n => (radius (t n)- exp (t n)) - (level (t n)-exp (t n))) atTop
      (𝓝 0) by simpa [Function.comp_def] using h).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  rw [(roots n hn).2]
  ring

/-- The relative radial deviation from the grid is little-o of 1/n. -/
theorem relative_radial_error {t : ℕ → ℝ}
    (roots : ∀ n, 0<n → 0<t n ∧ level (t n)=2*π*n) :
    Tendsto (fun n : ℕ => n*(radius (t n)/(2*π*n)-1)) atTop (𝓝 0) := by
  apply (show Tendsto (fun n : ℕ => (radius (t n)-2*π*n)/(2*π)) atTop (𝓝 0) by
    simpa using (radial_error roots).div_const (2*π)).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  field_simp [pi_ne_zero, show (n:ℝ) ≠ 0 by positivity]
  ring

/-- Quarter displacement for the actual normalization Cₙ=RₙBₙ²/2 of any root selection. -/
theorem quartet_quarter_limit {t : ℕ → ℝ}
    (roots : ∀ n, 0<n → 0<t n ∧ level (t n)=2*π*n) :
    Tendsto (fun n : ℕ => n*(1-radius (t n)*Barnes.B n^2/2)) atTop (𝓝 (1/4:ℝ)) := by
  have h := Barnes.quarter_limit.sub (((radial_error roots).mul Barnes.D_tendsto).div_const (2*π))
  convert h using 1
  · funext n
    simp only [Barnes.D]
    field_simp [pi_ne_zero]
    ring
  · norm_num

/-- An unconditional sequence of original characteristic roots exhibits the
quarter shift in the norms of the dynamically recovered parameters. -/
theorem exists_characteristic_quarter :
    ∃ t : ℕ → ℝ, (∀ n, 0<n → 0<t n ∧ level (t n)=2*π*n ∧
      Quartet.characteristic (polarPhase (t n))) ∧
      Tendsto (fun n : ℕ => n*(1-
        ‖polarPhase (t n)/Complex.exp (polarPhase (t n))⁻¹‖ * Barnes.B n^2/2))
        atTop (𝓝 (1/4:ℝ)) := by
  let t (n : ℕ) := if hn : 0<n then Classical.choose (exists_level n hn) else 0
  have h (n : ℕ) (hn : 0<n) : 0<t n ∧ level (t n)=2*π*n := by
    simpa [t, hn] using Classical.choose_spec (exists_level n hn)
  refine ⟨t,fun n hn => ⟨(h n hn).1,(h n hn).2,characteristic_of_level (h n hn).1 (h n hn).2⟩,?_⟩
  apply (quartet_quarter_limit h).congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  rw [recovered_norm (h n hn).1]

end
end SuperZeta.QuartetRadius
