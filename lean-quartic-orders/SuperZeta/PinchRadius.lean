import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Radius and separation at the critical value of a quadratic, and the local
square law at an even analytic critical point. Radii are measured in the
original Euclidean coordinates. -/

open Filter Asymptotics
open scoped Topology

namespace SuperZeta.PinchRadius

def quadratic (z : ℂ) : ℂ := 1 - z ^ 2

theorem output_radius (z : ℂ) : ‖quadratic z - 1‖ = ‖z‖ ^ 2 := by
  simp [quadratic, sub_eq_add_neg, norm_pow]

theorem opposite_input_separation (z : ℂ) :
    ‖z - (-z)‖ = 2 * Real.sqrt ‖quadratic z - 1‖ := by
  rw [output_radius, Real.sqrt_sq (norm_nonneg z)]
  rw [show z - (-z) = (2 : ℂ) * z by ring, norm_mul]
  simp

theorem output_diameter (z : ℂ) : ‖quadratic z - (2 - quadratic z)‖ = 2 * ‖z‖ ^ 2 := by
  rw [show quadratic z - (2 - quadratic z) = (2 : ℂ) * (quadratic z - 1) by ring,
    norm_mul, output_radius]
  simp

theorem quarter_turn_realizes_diameter (z : ℂ) :
    ‖Complex.I * z‖ = ‖z‖ ∧ ‖quadratic z - quadratic (Complex.I * z)‖ = 2 * ‖z‖ ^ 2 := by
  constructor
  · simp [norm_mul]
  · have h : quadratic (Complex.I * z) = 2 - quadratic z := by
      simp [quadratic, mul_pow, Complex.I_sq]
      ring
    rw [h, output_diameter]

theorem diameter_upper_bound {z w : ℂ} (hw : ‖w‖ = ‖z‖) :
    ‖quadratic z - quadratic w‖ ≤ 2 * ‖z‖ ^ 2 := by
  calc
    _ = ‖(quadratic z - 1) - (quadratic w - 1)‖ := by congr 1; ring
    _ ≤ ‖quadratic z - 1‖ + ‖quadratic w - 1‖ := norm_sub_le _ _
    _ = _ := by rw [output_radius, output_radius, hw]; ring

/-- Adding a full output turn negates its continuous square-root lift.
Continuing along opposite arcs to their common exit thus gives
opposite input values when the arc angles differ by one full turn. -/
theorem extra_turn_negates_lift (z : ℂ) (θ : ℝ) :
    z * Complex.exp ((((θ : ℂ) + 2 * Real.pi) / 2) * Complex.I) =
      -(z * Complex.exp (((θ : ℂ) / 2) * Complex.I)) := by
  rw [show (((θ : ℂ) + 2 * Real.pi) / 2) * Complex.I =
      ((θ : ℂ) / 2) * Complex.I + Real.pi * Complex.I by ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

/-- Rotating an input through half the output angle keeps it above the
prescribed output circle throughout the detour. -/
theorem projected_lift (z : ℂ) (θ : ℝ) :
    quadratic (z * Complex.exp (((θ : ℂ) / 2) * Complex.I)) - 1 =
      (quadratic z - 1) * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [show (θ : ℂ) * Complex.I = ((θ : ℂ) / 2) * Complex.I + ((θ : ℂ) / 2) * Complex.I by ring,
    Complex.exp_add]
  unfold quadratic
  ring

/-- In centered coordinates the functional equation is evenness. -/
theorem quartic_remainder {f : ℂ → ℂ} (ha : AnalyticAt ℂ f 0)
    (he : ∀ z, f (-z) = f z) :
    (fun h : ℂ => f h - (f 0 + (iteratedDeriv 2 f 0 / 2) * h ^ 2))
      =O[𝓝 0] (fun h : ℂ => ‖h‖ ^ 4) := by
  have hf : (fun z => f (-z)) = f := funext he
  have odd₁ := iteratedDeriv_comp_neg 1 f 0
  have odd₃ := iteratedDeriv_comp_neg 3 f 0
  rw [hf] at odd₁ odd₃
  norm_num [smul_eq_mul] at odd₁ odd₃
  have h₁ : deriv f 0 = 0 := by linear_combination (1/2 : ℂ) * odd₁
  have h₃ : iteratedDeriv 3 f 0 = 0 := by linear_combination (1/2 : ℂ) * odd₃
  convert ha.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 4 using 2 with h
  simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff, h₁, h₃, Nat.factorial, smul_eq_mul]
  ring

/-- The coefficient of the squared displacement is the half-curvature. -/
theorem scaled_increment {f : ℂ → ℂ} (ha : AnalyticAt ℂ f 0)
    (he : ∀ z, f (-z) = f z) :
    Tendsto (fun h : ℂ => (f h - f 0) / h ^ 2) (𝓝[≠] 0)
      (𝓝 (iteratedDeriv 2 f 0 / 2)) := by
  let a := iteratedDeriv 2 f 0 / 2
  have rem : (fun h : ℂ => f h - (f 0 + a * h ^ 2)) =o[𝓝 0] (fun h => h ^ 2) := by
    apply isLittleO_norm_right.mp
    simpa only [norm_pow] using
      (quartic_remainder ha he).trans_isLittleO (isLittleO_norm_pow_norm_pow (by decide : 2 < 4))
  have ht := rem.tendsto_div_nhds_zero.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hs := ht.add (tendsto_const_nhds (x := a))
  simp only [zero_add] at hs
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hz : h ≠ 0 := hh
  change (f h - (f 0 + a * h ^ 2)) / h ^ 2 + a = (f h - f 0) / h ^ 2
  field_simp
  ring

/-- In original coordinates the inverse radius approaches √(r/|a|).
Both antipodal inputs share this limit. -/
theorem inverse_radius_ratio {f : ℂ → ℂ} (ha : AnalyticAt ℂ f 0)
    (he : ∀ z, f (-z) = f z) (h₂ : iteratedDeriv 2 f 0 ≠ 0) :
    Tendsto (fun h : ℂ => ‖h‖ / Real.sqrt ‖f h - f 0‖) (𝓝[≠] 0)
      (𝓝 (1 / Real.sqrt ‖iteratedDeriv 2 f 0 / 2‖)) := by
  have ht := (scaled_increment ha he).norm.sqrt
  have hnon := (Real.sqrt_pos.2 (norm_pos_iff.mpr (div_ne_zero h₂ (by norm_num : (2 : ℂ) ≠ 0)))).ne'
  have hi := (tendsto_const_nhds (x := (1 : ℝ))).div ht hnon
  apply hi.congr
  intro h
  change 1 / Real.sqrt ‖(f h - f 0) / h ^ 2‖ = ‖h‖ / Real.sqrt ‖f h - f 0‖
  simp [norm_div, norm_pow, Real.sqrt_div (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- Halving the input displacement gives one quarter of the output
displacement in the limit, in every complex direction. -/
theorem halving_ratio {f : ℂ → ℂ} (ha : AnalyticAt ℂ f 0)
    (he : ∀ z, f (-z) = f z) (h₂ : iteratedDeriv 2 f 0 ≠ 0) :
    Tendsto (fun h : ℂ => (f (h / 2) - f 0) / (f h - f 0)) (𝓝[≠] 0) (𝓝 (1/4)) := by
  let a := iteratedDeriv 2 f 0 / 2
  have hnon : a ≠ 0 := div_ne_zero h₂ (by norm_num)
  have hp : Tendsto (fun h : ℂ => h / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have ht₀ : Tendsto (fun h : ℂ => h / 2) (𝓝 0) (𝓝 0) := by
        simpa using ((continuous_id.div_const (2 : ℂ)).continuousAt (x := 0)).tendsto
      exact ht₀.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact div_ne_zero (show x ≠ 0 from hx) (by norm_num)
  have ht := scaled_increment ha he
  have hr := ((ht.comp hp).div ht hnon).div_const (4 : ℂ)
  rw [div_self hnon] at hr
  apply hr.congr'
  filter_upwards [self_mem_nhdsWithin, ht.eventually_ne hnon] with h hh hn
  have hz : h ≠ 0 := hh
  have hd : f h - f 0 ≠ 0 := by
    intro heq
    apply hn
    simp [heq]
  change ((f (h / 2) - f 0) / (h / 2) ^ 2 / ((f h - f 0) / h ^ 2)) / 4 = _
  field_simp
  ring

/-- The centered half-Mellin integral used by the Gaussian calculation.
The kernel K comes from the signed ideal coefficients in the arithmetic replay. -/
noncomputable def halfMellin (K : ℝ → ℝ) (h : ℂ) : ℂ :=
  ∫ x in Set.Ici (0 : ℝ), (2 * (K x : ℂ)) * Complex.cosh (h * (x : ℂ))

theorem halfMellin_even (K : ℝ → ℝ) (h : ℂ) :
    halfMellin K (-h) = halfMellin K h := by
  simp [halfMellin, neg_mul, Complex.cosh_neg]

/-- The conditional application in the normalization of the arithmetic replay.
The analytic proof and interval calculation supply analyticity and nonzero
curvature for the quartic's actual theta kernel. -/
theorem halfMellin_radius (K : ℝ → ℝ) (ha : AnalyticAt ℂ (halfMellin K) 0)
    (h₂ : iteratedDeriv 2 (halfMellin K) 0 ≠ 0) :
    Tendsto (fun h : ℂ => 2 * ‖h‖ / Real.sqrt ‖halfMellin K h - halfMellin K 0‖)
      (𝓝[≠] 0) (𝓝 (2 / Real.sqrt ‖iteratedDeriv 2 (halfMellin K) 0 / 2‖)) := by
  have ht := (inverse_radius_ratio ha (halfMellin_even K) h₂).const_mul 2
  simpa [div_eq_mul_inv, mul_assoc] using ht

end SuperZeta.PinchRadius
