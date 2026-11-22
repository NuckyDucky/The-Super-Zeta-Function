import SuperZeta.PinchRadius
import SuperZeta.UnitSpectrum

/-! The quadratic terms of the two plotted traces. The same height t is
used for the centered Gaussian input it and the spectral input 1/4 + it/2. -/

open Filter Asymptotics
open scoped Topology

namespace SuperZeta.GaussianBends

noncomputable section

/-- Along the critical line the even Gaussian expansion has negative quadratic
coefficient when the real second derivative at its center is positive. -/
theorem gaussian_vertical_expansion {f : ℂ → ℂ} (ha : AnalyticAt ℂ f 0)
    (he : ∀ h, f (-h) = f h) :
    (fun t : ℝ => f (Complex.I * t) -
      (f 0 - (iteratedDeriv 2 f 0 / 2) * (t : ℂ) ^ 2))
      =O[𝓝 0] (fun t : ℝ => |t| ^ 4) := by
  have hlim : Tendsto (fun t : ℝ => Complex.I * (t : ℂ)) (𝓝 0) (𝓝 0) := by
    simpa using ((continuous_const.mul Complex.continuous_ofReal).continuousAt (x := 0)).tendsto
  simpa [Function.comp_def, mul_pow, Complex.I_sq, norm_mul, Real.norm_eq_abs, sub_eq_add_neg]
    using (PinchRadius.quartic_remainder ha he).comp_tendsto hlim

/-- Polynomial in the plotted coordinates: horizontal displacement C t²,
vertical displacement B t. -/
def spectralJet (x₀ B C t : ℝ) : ℂ :=
  ⟨x₀ + C*t^2, B*t⟩

/-- In the output plane the quadratic jet is X = x₀ + (C/B²)Y².
Positive C opens to the right. Negative B sends positive heights below
the horizontal axis. -/
theorem spectralJet_graph {x₀ B C : ℝ} (hB : B < 0) (hC : 0 < C) (t : ℝ) :
    (spectralJet x₀ B C t).re = x₀ + C / B ^ 2 * (spectralJet x₀ B C t).im ^ 2 ∧
    0 < C / B ^ 2 ∧ (0 < t → (spectralJet x₀ B C t).im < 0) := by
  unfold spectralJet
  refine ⟨?_, div_pos hC (sq_pos_of_ne_zero (ne_of_lt hB)), fun ht => mul_neg_of_neg_of_pos hB ht⟩
  field_simp [ne_of_lt hB]
  ring

/-- Taylor's theorem for the original continued super zeta at the real
input 1/4. The three derivative readings are expressed in real plot units. -/
theorem continuation_vertical_expansion {x₀ B C : ℝ}
    (h₀ : UnitSpectrum.continuation (1/4) = (x₀ : ℂ))
    (h₁ : deriv UnitSpectrum.continuation (1/4) = 2 * (B : ℂ))
    (h₂ : iteratedDeriv 2 UnitSpectrum.continuation (1/4) = -8 * (C : ℂ)) :
    (fun t : ℝ => UnitSpectrum.continuation (1/4 + Complex.I * t / 2) -
      spectralJet x₀ B C t) =O[𝓝 0] (fun t : ℝ => |t| ^ 3) := by
  have ha := UnitSpectrum.continuation_analytic (s := 1/4) (by norm_num)
  let center : ℂ := 1/4
  change UnitSpectrum.continuation center = _ at h₀
  change deriv UnitSpectrum.continuation center = _ at h₁
  change iteratedDeriv 2 UnitSpectrum.continuation center = _ at h₂
  change AnalyticAt ℂ UnitSpectrum.continuation center at ha
  have hpoly : (fun h : ℂ => UnitSpectrum.continuation (center + h) -
      ((x₀ : ℂ) + 2 * B * h + (-4) * C * h ^ 2)) =O[𝓝 0] (fun h : ℂ => ‖h‖ ^ 3) := by
    convert ha.hasFPowerSeriesAt.isBigO_sub_partialSum_pow 3 using 2 with h
    change _ = UnitSpectrum.continuation (center + h) - _
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff, h₀, h₁, h₂, Nat.factorial, smul_eq_mul]
    ring
  have hlim : Tendsto (fun t : ℝ => Complex.I * (t : ℂ) / 2) (𝓝 0) (𝓝 0) := by
    simpa using ((((continuous_const.mul Complex.continuous_ofReal).div_const (2 : ℂ)).continuousAt
      (x := 0))).tendsto
  have hjet (t : ℝ) : (x₀ : ℂ) + 2 * B * (Complex.I * t / 2) +
      -4 * C * (Complex.I * t / 2)^2 = spectralJet x₀ B C t := by
    rw [div_pow, mul_pow, Complex.I_sq]
    have hj : spectralJet x₀ B C t = ((x₀ + C*t^2 : ℝ) : ℂ) + (B*t : ℝ) * Complex.I := by
      exact (Complex.re_add_im (spectralJet x₀ B C t)).symm
    rw [hj]
    push_cast
    ring
  have h := hpoly.comp_tendsto hlim
  simp only [Function.comp_def, hjet, norm_div, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat] at h
  refine h.trans ?_
  refine isBigO_iff.mpr ⟨1, Filter.Eventually.of_forall fun t => ?_⟩
  simp [Real.norm_eq_abs, abs_of_nonneg, abs_nonneg, div_pow]
  linarith [pow_nonneg (abs_nonneg t) 3]

private theorem component_bound {e : ℝ → ℂ} (proj : ℂ → ℝ)
    (hle : ∀ z : ℂ, |proj z| ≤ ‖z‖)
    (h : e =O[𝓝 0] (fun t : ℝ => |t| ^ 3)) :
    (fun t => proj (e t)) =O[𝓝 0] (fun t : ℝ => |t| ^ 3) := by
  obtain ⟨M, hM⟩ := isBigO_iff.mp h
  refine isBigO_iff.mpr ⟨M, ?_⟩
  filter_upwards [hM] with t ht
  exact (hle (e t)).trans ht

private theorem scaled_error {e : ℝ → ℝ} {n : ℕ} (hn : n < 3)
    (h : e =O[𝓝 0] (fun t : ℝ => |t| ^ 3)) :
    Tendsto (fun t => e t / t ^ n) (𝓝[≠] 0) (𝓝 0) := by
  have h' : e =o[𝓝 0] (fun t : ℝ => t ^ n) := by
    apply isLittleO_norm_right.mp
    simpa only [norm_pow, Real.norm_eq_abs] using
      h.trans_isLittleO (isLittleO_norm_pow_norm_pow (E' := ℝ) hn)
  exact h'.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds

/-- Eliminating the shared height gives the quadratic opening coefficient
of the actual trace in its own output plane. -/
theorem output_plane_limit {g : ℝ → ℂ} {x₀ B C : ℝ} (hB : B ≠ 0)
    (h : (fun t => g t - spectralJet x₀ B C t) =O[𝓝 0] (fun t : ℝ => |t| ^ 3)) :
    Tendsto (fun t => ((g t).re - x₀) / (g t).im ^ 2) (𝓝[≠] 0) (𝓝 (C / B ^ 2)) := by
  have hx := scaled_error (by decide : 2 < 3) (component_bound Complex.re Complex.abs_re_le_norm h)
  have hy := scaled_error (by decide : 1 < 3) (component_bound Complex.im Complex.abs_im_le_norm h)
  have hx' : Tendsto (fun t => ((g t).re - x₀) / t ^ 2) (𝓝[≠] 0) (𝓝 C) := by
    have hsum := hx.add (tendsto_const_nhds (x := C))
    rw [zero_add] at hsum
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : t ≠ 0 := ht
    change ((g t).re - (x₀ + C * t^2)) / t^2 + C = _
    field_simp
    ring
  have hy' : Tendsto (fun t => (g t).im / t) (𝓝[≠] 0) (𝓝 B) := by
    have hsum := hy.add (tendsto_const_nhds (x := B))
    rw [zero_add] at hsum
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hne : t ≠ 0 := ht
    change ((g t).im - B * t) / t^1 + B = _
    field_simp
  apply (hx'.div (hy'.pow 2) (pow_ne_zero _ hB)).congr'
  filter_upwards [self_mem_nhdsWithin, hy'.eventually_ne hB] with t ht him
  have hne : t ≠ 0 := ht
  have hi : (g t).im ≠ 0 := by
    intro hz
    apply him
    simp [hz]
  change (((g t).re - x₀) / t ^ 2) / ((g t).im / t) ^ 2 = _
  field_simp

/-- Opening coefficient of the original super-zeta trace in its output coordinates. -/
theorem continuation_output_parabola {x₀ B C : ℝ} (hB : B ≠ 0)
    (h₀ : UnitSpectrum.continuation (1/4) = (x₀ : ℂ))
    (h₁ : deriv UnitSpectrum.continuation (1/4) = 2 * (B : ℂ))
    (h₂ : iteratedDeriv 2 UnitSpectrum.continuation (1/4) = -8 * (C : ℂ)) :
    let g := fun t : ℝ => UnitSpectrum.continuation (1/4 + Complex.I * t / 2)
    Tendsto (fun t => ((g t).re - x₀) / (g t).im ^ 2) (𝓝[≠] 0) (𝓝 (C / B ^ 2)) :=
  output_plane_limit hB (continuation_vertical_expansion h₀ h₁ h₂)

end
end SuperZeta.GaussianBends
