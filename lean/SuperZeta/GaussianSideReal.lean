import SuperZeta.PinchRadius
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

open MeasureTheory Set

namespace SuperZeta.GaussianSideReal

/-- On the real axis the Mellin integrand has the sign of its kernel.
A positive second moment rules out a kernel that vanishes almost everywhere. -/
theorem halfMellin_re_pos (K : ℝ → ℝ) (a : ℝ)
    (hK : ∀ x ∈ Ici (0 : ℝ), 0 ≤ K x)
    (hi : IntegrableOn (fun x : ℝ => (2 * (K x : ℂ)) *
      Complex.cosh ((⟨a,0⟩ : ℂ) * (x : ℂ))) (Ici (0 : ℝ)))
    (hm : 0 < ∫ x in Ici (0 : ℝ), 2 * K x * x ^ 2) :
    0 < (SuperZeta.PinchRadius.halfMellin K ⟨a,0⟩).re := by
  let f : ℝ → ℂ := fun x => 2 * (K x : ℂ) * Complex.cosh ((⟨a,0⟩ : ℂ) * (x : ℂ))
  have hfx (x : ℝ) : (f x).re = 2 * K x * Real.cosh (a*x) := by
    change ((2 : ℂ) * (K x : ℂ) * Complex.cosh ((a : ℂ) * (x : ℂ))).re = _
    rw [← Complex.ofReal_mul, ← Complex.ofReal_cosh]
    norm_cast
  have hn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ici 0)] (fun x => (f x).re) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with x hx
    exact (hfx x).symm ▸ mul_nonneg (mul_nonneg (by norm_num) (hK x hx)) (Real.cosh_pos _).le
  have hir : Integrable (fun x => (f x).re) (volume.restrict (Ici 0)) := hi.re
  unfold SuperZeta.PinchRadius.halfMellin
  rw [← RCLike.re_eq_complex_re, ← integral_re hi]
  change 0 < ∫ x in Ici (0 : ℝ), (f x).re
  by_contra! h
  have hzero := (integral_eq_zero_iff_of_nonneg_ae hn hir).mp
    (le_antisymm h (integral_nonneg_of_ae hn))
  have hmass : (fun x : ℝ => 2 * K x * x ^ 2) =ᵐ[volume.restrict (Ici 0)] 0 := by
    filter_upwards [hzero] with x hx
    change (f x).re = 0 at hx
    rw [hfx] at hx
    change 2 * K x * x ^ 2 = 0
    rw [(mul_eq_zero.mp hx).resolve_right (Real.cosh_pos _).ne', zero_mul]
  have hx := integral_congr_ae hmass
  simp only [Pi.zero_apply, integral_zero] at hx
  exact (ne_of_gt hm) hx

end SuperZeta.GaussianSideReal
