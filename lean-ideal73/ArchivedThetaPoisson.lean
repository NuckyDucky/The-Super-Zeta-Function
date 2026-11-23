import QuarticQuadrants
import ArchivedGaussianContinuation

/-! Identify the Poisson transform's theta series with the same theta
series that supplies the archived Mellin integral and the field factor. -/

namespace QuarticModel

open QuarticFiniteFourier

private theorem quarterTerm_hasSum {A : ℝ} (hA : 0 < A) :
    HasSum (quarterTerm A) (archivedTheta (Real.pi*A) : ℂ) := by
  let t := Real.pi*A*archivedThetaScale
  have ht : 0 < t := mul_pos (mul_pos Real.pi_pos hA) archivedThetaScale_pos
  have htScale : t/archivedThetaScale = Real.pi*A :=
    mul_div_cancel_right₀ _ archivedThetaScale_pos.ne'
  rw [← htScale]
  refine (archivedTheta_hasSum_quarter ht).congr_fun ?_
  intro p
  change (QuarticDualArithmetic.conductorReading ((p.1 : ℤ)+1) p.2 : ℂ) *
      Complex.exp (-Real.pi*(A : ℂ)*((((p.1 : ℤ)+1 : ℤ) : ℂ)^2 + ((p.2 : ℤ) : ℂ)^2)) =
    archivedQuarterWeight p * (Real.exp (-((archivedQuarterNorm p : ℝ)/archivedThetaScale)*t) : ℂ)
  rw [Complex.ofReal_exp]
  congr 2
  unfold t archivedQuarterNorm
  push_cast
  field_simp [archivedThetaScale_pos.ne']

theorem gaussianLattice_eq_archivedTheta {A : ℝ} (hA : 0 < A) :
    gaussianLattice A = 4*(archivedTheta (Real.pi*A) : ℂ) := by
  have hq := quarterTerm_hasSum hA
  rw [gaussianLattice_four_quarters A hq.summable.norm, hq.tsum_eq]

/-- The exact positive Gauss amplitude gives the archived theta reflection. -/
theorem archivedThetaReflects_of_gaussAmplitude (hs : gaussAmplitude = (Real.sqrt D : ℂ)) :
    ArchivedThetaReflects := by
  intro t ht
  have hp : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (D : ℝ)^2 = (D : ℝ) := Real.sq_sqrt (by positivity)
  have hd : 1/((D : ℝ)*(t/Real.sqrt D)) = t⁻¹/Real.sqrt D := by
    field_simp [ht.ne', hp.ne']
    nlinarith only [hsq]
  have sc (u : ℝ) : Real.pi*(u/Real.sqrt D) = u/archivedThetaScale := by
    change _ = u/(Real.sqrt (D : ℝ)/Real.pi)
    rw [div_div_eq_mul_div]
    ring
  have ha := gaussian_lattice_transform (div_pos ht hp)
  rw [hs, hd, gaussianLattice_eq_archivedTheta (div_pos ht hp),
    gaussianLattice_eq_archivedTheta (div_pos (inv_pos.mpr ht) hp), sc, sc] at ha
  have h' : Real.sqrt (D : ℝ)*(4*archivedTheta (t/archivedThetaScale)) =
      (t/Real.sqrt D)⁻¹*(4*archivedTheta (t⁻¹/archivedThetaScale)) := by exact_mod_cast ha
  rw [inv_div, div_eq_mul_inv (Real.sqrt (D : ℝ)) t] at h'
  apply mul_left_cancel₀ (show (4 : ℝ)*Real.sqrt D ≠ 0 by positivity)
  linear_combination h'

#print axioms gaussianLattice_eq_archivedTheta
#print axioms archivedThetaReflects_of_gaussAmplitude

end QuarticModel
