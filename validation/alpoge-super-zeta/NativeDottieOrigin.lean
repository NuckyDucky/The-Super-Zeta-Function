import NativeDottieContact
import SuperZeta.Oriented.SpectralInverse
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-! Attach the two native channels to the two cap-rooted words at the same
imaginary lift. The angle crossing itself is supplied by the original orbit
certificate. -/
noncomputable section

namespace DottieOriented.NativeSpectrum
open Complex Filter Set SuperZeta.Reciprocal TraceRecovery
open scoped Topology ComplexConjugate

def qReturn (y : ℝ) : ℂ → ℂ := (scalarReturn (-(I * (y : ℂ))))^[320]

private theorem return_conj (y : ℝ) (p : ℂ) :
    qReturn y (conj p) = conj (capReturn y p) := by
  have h : Function.Semiconj (conj : ℂ → ℂ) (scalarReturn (I * (y : ℂ)))
      (scalarReturn (-(I * (y : ℂ)))) := by
    intro z
    simp [scalarReturn, ← Complex.exp_conj]
  exact (h.iterate_right 320 p).symm

private theorem deriv_conj_conj {f : ℂ → ℂ} {z f' : ℂ} (hf : HasDerivAt f f' z) :
    HasDerivAt (fun u => conj (f (conj u))) (conj f') (conj z) := by
  have hc0 : Tendsto (conj : ℂ → ℂ) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (Complex.continuous_conj.continuousAt (x := (0:ℂ))).tendsto.mono_left
        (nhdsWithin_le_nhds (s := ({0} : Set ℂ)ᶜ))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa using ht
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have h := Complex.continuous_conj.continuousAt.tendsto.comp
    (hf.tendsto_slope_zero.comp hc0)
  simpa only [Function.comp_def, smul_eq_mul, map_mul, map_inv₀, map_sub, map_add,
    Complex.conj_conj] using h

theorem origin_return_derivative (y : ℝ) (p : ℂ) :
    deriv (qReturn y) (conj p) = conj (deriv (capReturn y) p) := by
  let L := I * (y : ℂ)
  have hd : Differentiable ℂ (scalarReturn L) := by
    unfold scalarReturn
    fun_prop
  have hcap : Differentiable ℂ (capReturn y) := hd.iterate 320
  have he : (fun u => conj (capReturn y (conj u))) = qReturn y := by
    funext u
    simpa only [conj_conj] using (return_conj y (conj u)).symm
  have h := (deriv_conj_conj (hcap p).hasDerivAt).deriv
  rw [he] at h
  exact h

def absoluteAngle (b : Bool) : ℝ := -phase b

theorem crossed_origin_angles (y : ℝ) (p : ℂ) (b : Bool)
    (h : nativeAngle y p = absoluteAngle b) :
    arg (deriv (qReturn y) (conj p)) = absoluteAngle (!b) := by
  rw [origin_return_derivative, Complex.arg_conj]
  change arg (deriv (capReturn y) p) = absoluteAngle b at h
  rw [h]
  have hne : absoluteAngle b ≠ Real.pi := by
    cases b <;> simp [absoluteAngle, phase] <;> linarith [Real.pi_pos]
  rw [if_neg hne]
  cases b <;> simp [absoluteAngle, phase]

theorem first_reading_from_roots (b : Bool) :
    spectralReading b 1 = SpectralInverse.rootSum (phase b) := by
  have hR : sharedReference 1 = 4/3 := by
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [sharedReference_eq (s := 1) (by norm_num)]
    norm_num [thirdFactor, Complex.cpow_neg, Complex.cpow_two, riemannZeta_two]
    field_simp [hπ]
    ring
  rw [spectralReading, hR, SpectralInverse.rootSum_is_trace (cos_phase_ne b)]
  cases b
  · rw [archived_first_corrections.1]
    have ht := TraceRecovery.firstCorrection_pi_div_six.1
    norm_num [phase, ht]
  · rw [archived_first_corrections.2]
    have ht := TraceRecovery.firstCorrection_neg_pi_div_six.1
    norm_num [phase, ht]

#print axioms origin_return_derivative
#print axioms crossed_origin_angles
#print axioms first_reading_from_roots

end DottieOriented.NativeSpectrum
end
