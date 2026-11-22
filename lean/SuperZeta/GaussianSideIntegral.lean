import SuperZeta.PinchRadius
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Imaginary part of the completed Gaussian half-Mellin integral,
in coordinates centered at the critical line. -/

open MeasureTheory Set Complex

namespace SuperZeta.GaussianSideIntegral

noncomputable section

def sinc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sin x / x

def sinhc (x : ℝ) : ℝ := if x = 0 then 1 else Real.sinh x / x

@[simp] theorem sinc_zero : sinc 0 = 1 := by simp [sinc]
@[simp] theorem sinhc_zero : sinhc 0 = 1 := by simp [sinhc]

theorem mul_sinc (x : ℝ) : x * sinc x = Real.sin x := by
  by_cases h : x = 0
  · simp [h]
  · rw [sinc, if_neg h, mul_comm, div_mul_cancel₀ _ h]

theorem mul_sinhc (x : ℝ) : x * sinhc x = Real.sinh x := by
  by_cases h : x = 0
  · simp [h]
  · rw [sinhc, if_neg h, mul_comm, div_mul_cancel₀ _ h]

theorem abs_sinc_le_one (x : ℝ) : |sinc x| ≤ 1 := by
  by_cases h : x = 0
  · simp [h]
  · rw [sinc, if_neg h, abs_div, div_le_one (abs_pos.mpr h)]
    exact Real.abs_sin_le_abs

def slope (K : ℝ → ℝ) (a t : ℝ) : ℝ :=
  ∫ x in Ici (0 : ℝ), (2 * K x * x ^ 2) * sinc (t * x) * sinhc (a * x)

/-- The pointwise identity includes zero horizontal displacement, height
and integration variable, by the removable definitions of both kernels. -/
theorem integrand_im (K : ℝ → ℝ) (a t x : ℝ) :
    ((2 * (K x : ℂ)) * Complex.cosh ((⟨a,t⟩ : ℂ) * (x : ℂ))).im =
    (a * t) * ((2 * K x * x ^ 2) * sinc (t * x) * sinhc (a * x)) := by
  have hz : (⟨a,t⟩ : ℂ) * (x : ℂ) =
      ((a*x : ℝ) : ℂ) + ((t*x : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hz, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  have h2r : (2 : ℂ).re = 2 := rfl
  have h2i : (2 : ℂ).im = 0 := rfl
  simp only [Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    h2r, h2i, Complex.cosh_ofReal_im, Complex.cosh_ofReal_re,
    Complex.sinh_ofReal_im, Complex.sinh_ofReal_re, Complex.cos_ofReal_re,
    Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, mul_one]
  rw [← mul_sinhc (a*x), ← mul_sinc (t*x)]
  ring

/-- The imaginary part of the full integral has one horizontal and one
vertical factor. Integrability of the complex integrand permits taking
its imaginary part under the integral. -/
theorem halfMellin_im_eq (K : ℝ → ℝ) (a t : ℝ)
    (h : IntegrableOn (fun x : ℝ => (2 * (K x : ℂ)) *
      Complex.cosh ((⟨a,t⟩ : ℂ) * (x : ℂ))) (Ici (0 : ℝ))) :
    (SuperZeta.PinchRadius.halfMellin K ⟨a,t⟩).im = a*t*slope K a t := by
  unfold SuperZeta.PinchRadius.halfMellin slope
  rw [← RCLike.im_eq_complex_im, ← integral_im h, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (integrand_im K a t)

theorem halfMellin_im_on_axis (K : ℝ → ℝ) (t : ℝ)
    (h : IntegrableOn (fun x : ℝ => (2 * (K x : ℂ)) *
      Complex.cosh ((⟨0,t⟩ : ℂ) * (x : ℂ))) (Ici (0 : ℝ))) :
    (SuperZeta.PinchRadius.halfMellin K ⟨0,t⟩).im = 0 := by
  rw [halfMellin_im_eq K 0 t h, zero_mul, zero_mul]

theorem zero_forces_axis (K : ℝ → ℝ) (a t : ℝ)
    (h : IntegrableOn (fun x : ℝ => (2 * (K x : ℂ)) *
      Complex.cosh ((⟨a,t⟩ : ℂ) * (x : ℂ))) (Ici (0 : ℝ)))
    (ht : t ≠ 0) (hQ : slope K a t ≠ 0)
    (hz : SuperZeta.PinchRadius.halfMellin K ⟨a,t⟩ = 0) : a = 0 := by
  have hzero := congrArg Complex.im hz
  rw [halfMellin_im_eq K a t h] at hzero
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hQ)).resolve_right ht

end
end SuperZeta.GaussianSideIntegral
