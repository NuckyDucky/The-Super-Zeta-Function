import SuperZeta.QuarterLine.QuartetBandCauchy
import SuperZeta.QuarterLine.QuartetBandDominance
import Mathlib.Analysis.Complex.RealDeriv

namespace SuperZeta.QuartetActualSpiral
noncomputable section
open Complex
open QuartetBandCauchy QuartetShiftContinuation UnitSpectrum

private theorem certified_bound : OuterBound :=
  fun _ h₁ h₂ ht => (QuartetBandDominance.band_relative_error h₁ h₂ ht).le

/-- An explicit branch of the logarithm through the full spectral spiral.
The leading logarithm supplies all complete turns and the principal logarithm
of the relative correction is single-valued in the right half-plane. -/
def lifted (s : ℂ) := -2*s*Complex.log (upper 0) + Complex.log (continuation s / leading s)

theorem lifted_exp {s : ℂ} (hσ : |s.re-1/4| ≤ 1/64) (ht : 101 ≤ s.im) :
    Complex.exp (lifted s) = continuation s := by
  have hl := leading_ne s
  have hz := continuation_ne certified_bound hσ ht
  have h : Complex.exp (-2*s*Complex.log (upper 0)) = leading s := by
    rw [leading,Complex.cpow_def_of_ne_zero (show upper 0 ≠ 0 from QuartetLeading.first_ne_zero),mul_comm (-2*s)]
  rw [lifted,Complex.exp_add,h,Complex.exp_log (div_ne_zero hz hl)]
  field_simp

theorem log_radius {s : ℂ} (hσ : |s.re-1/4| ≤ 1/64) (ht : 101 ≤ s.im) :
    Real.log ‖continuation s‖ = (lifted s).re := by
  rw [← lifted_exp hσ ht, Complex.norm_exp, Real.log_exp]

theorem lifted_deriv {s : ℂ} (hσ : |s.re-1/4| ≤ 1/64) (ht : 101 ≤ s.im) :
    HasDerivAt lifted (deriv continuation s / continuation s) s := by
  have hl := leading_ne s
  have hz := continuation_ne certified_bound hσ ht
  have h := error_small certified_bound hσ ht
  have he : (continuation s / leading s) ∈ Complex.slitPlane := by
    have hh : 1 + error s ∈ Complex.slitPlane := Complex.mem_slitPlane_of_norm_lt_one (by linarith)
    convert hh using 1
    dsimp [error]
    ring
  have D := (((hasDerivAt_id s).const_mul (-2:ℂ)).mul_const (Complex.log (upper 0))).add
    ((((continuation_diff (show 0<s.im by linarith)).hasDerivAt).div (leading_deriv s) hl).clog he)
  change HasDerivAt lifted _ s at D
  apply D.congr_deriv
  simp only [Pi.div_apply]
  field_simp [hl, hz]
  ring

/-- Actual derivative inequalities for the unwrapped phase and the logarithm
of the radius along a vertical spectral input line. -/
theorem clockwise_outward (σ t : ℝ) (hσ : |σ-1/4| ≤ 1/64) (ht : 101 ≤ t) :
    deriv (fun y : ℝ => (lifted ((σ:ℂ)+(y:ℂ)*I)).im) t < -(62/381:ℝ) ∧
    379/508 < deriv (fun y : ℝ => (lifted ((σ:ℂ)+(y:ℂ)*I)).re) t := by
  let s : ℂ := (σ:ℂ)+(t:ℂ)*I
  have hr : s.re = σ := by simp [s,Complex.mul_re]
  have hi : s.im = t := by simp [s,Complex.mul_im]
  have hr' : |s.re-1/4|≤1/64 := hr ▸ hσ
  have hi' : 101≤s.im := hi ▸ ht
  have Dl := lifted_deriv hr' hi'
  have Dp : HasDerivAt (fun u : ℂ => (σ:ℂ)+u*I) I (t:ℂ) := by
    simpa using (((hasDerivAt_id (t:ℂ)).mul_const I).const_add (σ:ℂ))
  have D := Dl.comp (t:ℂ) Dp
  have Dr := D.real_of_complex
  have Di := (D.mul_const (-I)).real_of_complex
  have phase := log_slope certified_bound hr' hi'
  have radius := vertical_log_growth certified_bound hr' hi'
  constructor
  · have he : deriv (fun y : ℝ => (lifted ((σ:ℂ)+(y:ℂ)*I)).im) t =
        (deriv continuation s / continuation s).re := by
      simpa [Function.comp_def,Complex.mul_re,Complex.mul_im] using Di.deriv
    rw [he]; exact phase
  · have he : deriv (fun y : ℝ => (lifted ((σ:ℂ)+(y:ℂ)*I)).re) t =
        -(deriv continuation s / continuation s).im := by
      simpa [Function.comp_def,Complex.mul_re,Complex.mul_im] using Dr.deriv
    rw [he]; exact radius

end
end SuperZeta.QuartetActualSpiral
