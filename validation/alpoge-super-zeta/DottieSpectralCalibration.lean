import SuperZeta.GaussianSpectralTransfer

/-! Magnitude and signed bounds at the same input in the ordinary,
Super Zeta, and quartic readings. -/

namespace SuperZeta.DottieSpectralCalibration

open Complex Metric
open GaussianSpectralTransfer (FactorizationData beta corrected spectral_product)

noncomputable section

/-- The magnitude of the reconstruction factor is bounded above and below
using only the real part of the doubled input. -/
theorem riemannFactor_norm_bounds (s : ℂ) :
    let σ := (2 * s).re
    2 * Real.pi ^ (-σ) * ((2 : ℝ) ^ σ - 1) ≤ ‖Spectrum.riemannFactor s‖ ∧
      ‖Spectrum.riemannFactor s‖ ≤ 2 * Real.pi ^ (-σ) * ((2 : ℝ) ^ σ + 1) := by
  dsimp only
  have hπ : ‖(Real.pi : ℂ) ^ (-(2 * s))‖ = Real.pi ^ (-(2 * s).re) := by
    simpa only [neg_re] using
      norm_cpow_eq_rpow_re_of_pos Real.pi_pos (-(2 * s))
  have h2 : ‖(2 : ℂ) ^ (2 * s)‖ = (2 : ℝ) ^ (2 * s).re := by
    simpa using norm_cpow_eq_rpow_re_of_pos (by norm_num : 0 < (2 : ℝ)) (2 * s)
  have hlow : (2 : ℝ) ^ (2 * s).re - 1 ≤ ‖(2 : ℂ) ^ (2 * s) - 1‖ := by
    simpa only [h2, norm_one] using (norm_sub_norm_le ((2 : ℂ) ^ (2 * s)) 1)
  have hhigh : ‖(2 : ℂ) ^ (2 * s) - 1‖ ≤ (2 : ℝ) ^ (2 * s).re + 1 := by
    simpa only [h2, norm_one] using (norm_sub_le ((2 : ℂ) ^ (2 * s)) 1)
  have hn : 0 ≤ 2 * Real.pi ^ (-(2 * s).re) := by positivity
  rw [Spectrum.riemannFactor, norm_mul, norm_mul, hπ, show ‖(2 : ℂ)‖ = 2 by norm_num]
  exact ⟨mul_le_mul_of_nonneg_left hlow hn, mul_le_mul_of_nonneg_left hhigh hn⟩

private theorem relative_bound_mul_iff {m f p : ℂ} {q : ℝ} (hm : m ≠ 0) :
    ‖m * f - m * p‖ ≤ q * ‖m * p‖ ↔ ‖f - p‖ ≤ q * ‖p‖ := by
  rw [← mul_sub, norm_mul, norm_mul, mul_left_comm q]
  exact mul_le_mul_left (norm_pos_iff.mpr hm)

private theorem corrected_eq (s : ℂ) :
    corrected s = Spectrum.riemannFactor s * riemannZeta (2 * s) := by
  simp [corrected, UnitSpectrum.continuation]

/-- A relative error budget survives the spectral reconstruction exactly
when the reference is evaluated at the same input and scaled by the same factor. -/
theorem corrected_relative_bound_iff {s p : ℂ} {q : ℝ} (hs : 0 < s.re) :
    ‖corrected s - Spectrum.riemannFactor s * p‖ ≤ q * ‖Spectrum.riemannFactor s * p‖ ↔
      ‖riemannZeta (2 * s) - p‖ ≤ q * ‖p‖ := by
  rw [corrected_eq]
  exact relative_bound_mul_iff (Spectrum.riemannFactor_ne_zero hs)

/-- Dividing the contour weight by the reconstruction factor keeps the
whole complex reading, including the signed axis, at the doubled input. -/
theorem corrected_weighted_eq {s : ℂ} (hs : 0 < s.re) (W : ℂ) :
    (W / Spectrum.riemannFactor s) * corrected s = W * riemannZeta (2 * s) := by
  rw [corrected_eq, ← mul_assoc, div_mul_cancel₀ W (Spectrum.riemannFactor_ne_zero hs)]

/-- A holomorphic contour weight stays holomorphic under the change of
coordinates and division by the reconstruction factor. -/
theorem riemannFactor_weight_differentiableOn_disk {W : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hpos : ∀ s ∈ closedBall c r, 0 < s.re)
    (hW : DifferentiableOn ℂ W (closedBall (2 * c) (2 * r))) :
    DifferentiableOn ℂ (fun s => W (2 * s) / Spectrum.riemannFactor s)
      (closedBall c r) := by
  have hmap : Set.MapsTo (fun s : ℂ => 2 * s) (closedBall c r) (closedBall (2 * c) (2 * r)) := by
    intro s hs
    rw [mem_closedBall, dist_eq_norm] at hs ⊢
    rw [← mul_sub, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact mul_le_mul_of_nonneg_left hs (by norm_num)
  have hscale : DifferentiableOn ℂ (fun s : ℂ => 2 * s) (closedBall c r) := by fun_prop
  exact (hW.comp hscale hmap).div
    (fun s _ => (Multiplicity.analytic_factor s).differentiableAt.differentiableWithinAt)
    (fun s hs => Spectrum.riemannFactor_ne_zero (hpos s hs))

variable {field gaussian : ℂ → ℂ}

/-- The same relative budget rule applies to the full quartic product in
the spectral coordinates, including both the beta and Gaussian readings. -/
theorem field_relative_bound_iff (d : FactorizationData field gaussian)
    {s p : ℂ} {q : ℝ} (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2) :
    ‖corrected s * beta (2 * s) * gaussian (2 * s) - Spectrum.riemannFactor s * p‖ ≤
      q * ‖Spectrum.riemannFactor s * p‖ ↔ ‖field (2 * s) - p‖ ≤ q * ‖p‖ := by
  rw [show corrected s * beta (2 * s) * gaussian (2 * s) =
    Spectrum.riemannFactor s * field (2 * s) from spectral_product d h₁]
  exact relative_bound_mul_iff (Spectrum.riemannFactor_ne_zero h₀)

theorem field_weighted_eq (d : FactorizationData field gaussian)
    {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2) (W : ℂ) :
    (W / Spectrum.riemannFactor s) * (corrected s * beta (2 * s) * gaussian (2 * s)) =
      W * field (2 * s) := by
  rw [show corrected s * beta (2 * s) * gaussian (2 * s) =
    Spectrum.riemannFactor s * field (2 * s) from spectral_product d h₁]
  rw [← mul_assoc, div_mul_cancel₀ W (Spectrum.riemannFactor_ne_zero h₀)]

#print axioms riemannFactor_norm_bounds
#print axioms corrected_relative_bound_iff
#print axioms corrected_weighted_eq
#print axioms riemannFactor_weight_differentiableOn_disk
#print axioms field_relative_bound_iff
#print axioms field_weighted_eq

end

end SuperZeta.DottieSpectralCalibration
