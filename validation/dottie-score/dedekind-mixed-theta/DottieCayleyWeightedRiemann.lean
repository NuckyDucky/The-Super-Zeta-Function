import DottieContourPhase
import DottieRationalContour
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace FieldTarget

open Complex Set SuperZeta.StirlingCorrection

noncomputable section

/-- The actual center from the ordinary-zeta Cayley example. -/
def dottieCayleyCenter : ℂ := (3 / 4 : ℂ) + (100000001 : ℂ) * I

def dottieCayleyReference : ℝ := 100000001 + 1 / 512

theorem dottieCayley_center_eq :
    dottieScaledRightCenter dottieCayleyReference 0 = dottieCayleyCenter := by
  apply Complex.ext <;>
    norm_num [dottieScaledRightCenter, dottieRingScale, dottieCayleyReference, dottieCayleyCenter,
      mul_re, mul_im]

theorem dottieCayley_radius_eq : dottieScaledRadius 0 = 31 / 128 := by
  norm_num [dottieScaledRadius, dottieRingScale]

def dottieCayleySlope : ℝ := Real.log (100000001 / (2 * Real.pi)) / 2

def dottieCayleyScale : ℝ := ‖Gammaℝ dottieCayleyCenter‖

theorem dottieCayleyScale_pos : 0 < dottieCayleyScale := by
  apply norm_pos_iff.mpr
  apply Gammaℝ_ne_zero_of_re_pos
  norm_num [dottieCayleyCenter, mul_re]

/-- The exponential phase correction, unit rotation, and real completion factor
from the actual interval replay, at the same complex input. -/
def dottieCayleyWeight (w : ℂ) : ℂ :=
  (((15 : ℂ) + 8 * I) / 17) * exp (-((dottieCayleySlope : ℂ) * (w - dottieCayleyCenter))) *
    Gammaℝ w / (dottieCayleyScale : ℂ)

theorem dottieCayleyReading_eq_replay_formula (w : ℂ) :
    dottieCayleyWeight w * riemannZeta w =
      (((15 : ℂ) + 8 * I) / 17) *
        (exp (-((Real.log Real.pi : ℝ) : ℂ) * w / 2 -
          (dottieCayleySlope : ℂ) * (w - dottieCayleyCenter)) * Gamma (w / 2)) *
        riemannZeta w / (dottieCayleyScale : ℂ) := by
  unfold dottieCayleyWeight
  rw [Gammaℝ_def, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero),
    ← Complex.ofReal_log Real.pi_pos.le]
  have hArg : -((Real.log Real.pi : ℝ) : ℂ) * w / 2 -
      (dottieCayleySlope : ℂ) * (w - dottieCayleyCenter) =
      -((dottieCayleySlope : ℂ) * (w - dottieCayleyCenter)) +
        ((Real.log Real.pi : ℝ) : ℂ) * (-w / 2) := by ring
  rw [hArg, Complex.exp_add]
  ring

theorem dottieCayleyWeight_differentiableOn :
    DifferentiableOn ℂ dottieCayleyWeight (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
  have hγ : DifferentiableOn ℂ Gammaℝ (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
    intro w hw
    have h := (Complex.differentiable_Gammaℝ_inv w).inv
      (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hw.1))
    change DifferentiableAt ℂ (fun z : ℂ => ((Gammaℝ z)⁻¹)⁻¹) w at h
    exact (by simpa only [inv_inv] using h : DifferentiableAt ℂ Gammaℝ w).differentiableWithinAt
  have he : Differentiable ℂ
      (fun w : ℂ => exp (-((dottieCayleySlope : ℂ) * (w - dottieCayleyCenter)))) := by
    fun_prop
  exact (((differentiableOn_const _).mul he.differentiableOn).mul hγ).div_const _

/-- Exact handoff from closed rational-parameter arc enclosures to zero
exclusion on the chosen disk, for any holomorphic weight. -/
theorem dottieCayley_riemannZeta_ne_zero_of_weighted_arcs {W : ℂ → ℂ} {m : ℕ}
    (hW : DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1)) (hm : 0 < m)
    (hArcs : ∀ a ∈ contourQuarterTurns, ∀ j : Fin m, ∀ t ∈
      Icc (((j : ℕ) : ℝ) / m) ((((j : ℕ) : ℝ) + 1) / m),
      (W (rationalContourPoint dottieCayleyCenter (31 / 128) a t) *
        riemannZeta (rationalContourPoint dottieCayleyCenter (31 / 128) a t)).im ≤ -(1 / 16)) :
    ∀ w ∈ Metric.closedBall dottieCayleyCenter (31 / 128 : ℝ), riemannZeta w ≠ 0 := by
  intro w hw
  have hζ : DifferentiableOn ℂ riemannZeta (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
    intro z hz
    have htop : z.re < 1 := hz.2
    have h1 : z ≠ 1 := by rintro rfl; norm_num at htop
    exact (differentiableAt_riemannZeta h1).differentiableWithinAt
  have hboundary : ∀ z ∈ Metric.sphere (dottieScaledRightCenter dottieCayleyReference 0)
      (dottieScaledRadius 0), (W z * riemannZeta z).im ≤ -(1 / 16) := by
    rw [dottieCayley_center_eq, dottieCayley_radius_eq]
    intro z hz
    obtain ⟨a, ha, t, ht, rfl⟩ := exists_rationalContourPoint (by norm_num) hz
    obtain ⟨j, hj⟩ := exists_rationalContourInterval hm ht
    exact hArcs a ha j t hj
  exact dottie_disk_nonzero_of_holomorphic_weight hζ hW
    (by norm_num : (0 : ℝ) < 1 / 16) hboundary
    (by simpa only [dottieCayley_center_eq, dottieCayley_radius_eq] using hw)

/-- The signed arc enclosure for the exact weight used by the Cayley plot. -/
theorem dottieCayley_riemannZeta_ne_zero_of_arcs {m : ℕ} (hm : 0 < m)
    (hArcs : ∀ a ∈ contourQuarterTurns, ∀ j : Fin m, ∀ t ∈
      Icc (((j : ℕ) : ℝ) / m) ((((j : ℕ) : ℝ) + 1) / m),
      (dottieCayleyWeight (rationalContourPoint dottieCayleyCenter (31 / 128) a t) *
        riemannZeta (rationalContourPoint dottieCayleyCenter (31 / 128) a t)).im ≤ -(1 / 16)) :
    ∀ w ∈ Metric.closedBall dottieCayleyCenter (31 / 128 : ℝ), riemannZeta w ≠ 0 :=
  dottieCayley_riemannZeta_ne_zero_of_weighted_arcs dottieCayleyWeight_differentiableOn hm hArcs

#check @dottieCayley_riemannZeta_ne_zero_of_arcs
#print axioms dottieCayley_center_eq
#print axioms dottieCayley_radius_eq
#print axioms dottieCayleyScale_pos
#print axioms dottieCayleyReading_eq_replay_formula
#print axioms dottieCayleyWeight_differentiableOn
#print axioms dottieCayley_riemannZeta_ne_zero_of_weighted_arcs
#print axioms dottieCayley_riemannZeta_ne_zero_of_arcs

end

end FieldTarget
