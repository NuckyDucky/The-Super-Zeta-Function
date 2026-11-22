import GaussianSideConstants
import GaussianSideIntegral
import GaussianSideError
import GaussianSideReal

/-! Reading the side of the critical line from the completed Gaussian value.
The field-specific inputs are the theta integral and the bounds recorded in
the interval certificate. No hypothesis concerns the location of zeros. -/

open MeasureTheory Set
open GaussianSideIntegral

namespace GaussianSideSign

noncomputable section

def point (a t : ℝ) : ℂ := ⟨1/2 + a, t⟩

def mass (K : ℝ → ℝ) (x : ℝ) : ℝ := 2 * K x * x^2

/-- Analytic representation, convergence and bounds to be supplied for the
quartic. The line estimate is a one-variable integral bound in t. -/
structure Certificate (Λ : ℂ → ℂ) (K : ℝ → ℝ) : Prop where
  representation : ∀ a t : ℝ, |a| ≤ 1/20 → |t| ≤ 27/100 →
    Λ (point a t) = SuperZeta.PinchRadius.halfMellin K ⟨a,t⟩
  kernel_nonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ K x
  mass_integrable : IntegrableOn (mass K) (Ici 0)
  theta_tail : ∀ x ∈ Ioi (18 : ℝ), K x ≤
    3 * Real.exp (x/2) * Real.exp (-40 * Real.exp (x-18))
  base_integrable : ∀ t : ℝ, |t| ≤ 27/100 →
    IntegrableOn (fun x => mass K x * sinc (t*x)) (Ici 0)
  slope_integrable : ∀ a t : ℝ, |a| ≤ 1/20 → |t| ≤ 27/100 →
    IntegrableOn (fun x => mass K x * sinc (t*x) * sinhc (a*x)) (Ici 0)
  complex_integrable : ∀ a t : ℝ, |a| ≤ 1/20 → |t| ≤ 27/100 →
    IntegrableOn (fun x : ℝ => (2 * (K x : ℂ)) *
      Complex.cosh ((⟨a,t⟩ : ℂ) * (x : ℂ))) (Ici (0 : ℝ))
  line_floor : ∀ t : ℝ, |t| ≤ 27/100 →
    519994 < ∫ x in Ici 0, mass K x * sinc (t*x)
  curvature : ∫ x in Ici 0, mass K x ≤ 3565602

theorem slope_floor {Λ K} (cert : Certificate Λ K) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) : 18000 < GaussianSideIntegral.slope K a t := by
  have hs (u : ℝ) : GaussianSideError.averageCosh u = sinhc u :=
    GaussianSideError.averageCosh_eq u
  have hend : GaussianSideError.averageCosh (9/10) ≤ 11407/10000 := by
    rw [GaussianSideError.averageCosh_eq, if_neg (by norm_num)]
    linarith [GaussianSideConstants.sinh_ratio]
  have hm (x : ℝ) (hx : x ∈ Ici (0 : ℝ)) : 0 ≤ mass K x := by
    unfold mass
    exact mul_nonneg (mul_nonneg (by norm_num) (cert.kernel_nonneg x hx)) (sq_nonneg x)
  have hsub : Ioi (18 : ℝ) ⊆ Ici 0 :=
    fun _ hx => (by norm_num : (0 : ℝ) ≤ 18).trans hx.le
  have hmeas := (cert.mass_integrable.mono_set hsub).aestronglyMeasurable
  have hexp : Continuous (fun x : ℝ => Real.exp (x/20)) :=
    Real.continuous_exp.comp (continuous_id.div_const _)
  obtain ⟨htailI, htail⟩ := GaussianSideError.tail_of_kernel_majorant
    (fun x hx => cert.kernel_nonneg x (hsub hx)) cert.theta_tail
    (hmeas.mul hexp.aestronglyMeasurable)
  have h := GaussianSideError.slope_lower (mass := mass K) (v := fun x => sinc (t*x))
    ha hm (fun x => abs_sinc_le_one _) cert.mass_integrable (cert.base_integrable t ht)
    (by simpa only [hs] using cert.slope_integrable a t ha ht)
    htailI (cert.line_floor t ht) cert.curvature htail.le hend
  simpa only [hs, mass, GaussianSideIntegral.slope] using h

/-- Height may have either sign, and the identity includes both coordinate axes. -/
theorem quantitative_reading {Λ K} (cert : Certificate Λ K) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) :
    (Λ (point a t)).im = a*t*GaussianSideIntegral.slope K a t ∧
      18000 < GaussianSideIntegral.slope K a t := by
  constructor
  · rw [cert.representation a t ha ht]
    exact halfMellin_im_eq K a t (cert.complex_integrable a t ha ht)
  · exact slope_floor cert ha ht

/-- At each positive height the imaginary part recovers the horizontal side,
including equality on the line. -/
theorem side_reading {Λ K} (cert : Certificate Λ K) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) (htpos : 0 < t) :
    (0 < (Λ (point a t)).im ↔ 0 < a) ∧
    ((Λ (point a t)).im < 0 ↔ a < 0) ∧
    ((Λ (point a t)).im = 0 ↔ a = 0) := by
  obtain ⟨hy, hq⟩ := quantitative_reading cert ha ht
  have h : 0 < t * GaussianSideIntegral.slope K a t := mul_pos htpos (by linarith)
  rw [hy, mul_assoc]
  have hn : a * (t * GaussianSideIntegral.slope K a t) < 0 ↔ a < 0 := by
    constructor
    · intro hn
      by_contra! ha'
      exact (not_lt_of_ge (mul_nonneg ha' h.le)) hn
    · intro ha'
      exact mul_neg_of_neg_of_pos ha' h
  simp [mul_pos_iff_of_pos_right h, hn, h.ne']

/-- Any zero of nonzero height in this rectangle has real part one half. -/
theorem zero_requires_line {Λ K} (cert : Certificate Λ K) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) (ht0 : t ≠ 0)
    (hz : Λ (point a t) = 0) : (point a t).re = 1/2 := by
  rw [cert.representation a t ha ht] at hz
  have hq := slope_floor cert ha ht
  have h := zero_forces_axis K a t (cert.complex_integrable a t ha ht)
    ht0 (by linarith) hz
  simp [point, h]

/-- On the real axis the completed value is strictly positive. -/
theorem real_axis_positive {Λ K} (cert : Certificate Λ K) {a : ℝ}
    (ha : |a| ≤ 1/20) : 0 < (Λ (point a 0)).re := by
  have ht : |(0 : ℝ)| ≤ 27/100 := by norm_num
  have h0 := cert.line_floor 0 ht
  simp only [zero_mul, sinc_zero, mul_one] at h0
  rw [cert.representation a 0 ha ht]
  exact GaussianSideReal.halfMellin_re_pos K a cert.kernel_nonneg
    (cert.complex_integrable a 0 ha ht) (lt_trans (by norm_num) h0)

/-- This local zero-location consequence also covers height zero. -/
theorem zero_requires_line_whole_rectangle {Λ K} (cert : Certificate Λ K) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100)
    (hz : Λ (point a t) = 0) : (point a t).re = 1/2 := by
  by_cases h : t = 0
  · subst t
    have hp := real_axis_positive cert ha
    rw [hz] at hp
    exact (lt_irrefl (0 : ℝ) hp).elim
  · exact zero_requires_line cert ha ht h hz

/-- A concrete margin at both reflected inputs throughout the positive root bracket. -/
theorem bracket_margin {Λ K} (cert : Certificate Λ K) {t : ℝ}
    (hlo : 25835/100000 < t) (hhi : t < 25838/100000) :
    (Λ (point (-(1/100)) t)).im < -(465/10) ∧ 465/10 < (Λ (point (1/100) t)).im := by
  have htpos : 0 < t := by linarith
  have ht : |t| ≤ 27/100 := by rw [abs_of_pos htpos]; linarith
  have ha : |(1/100 : ℝ)| ≤ 1/20 := by rw [abs_of_pos (by norm_num)]; norm_num
  obtain ⟨hleft, qleft⟩ := quantitative_reading (a := -(1/100)) cert (by rwa [abs_neg]) ht
  obtain ⟨hright, qright⟩ := quantitative_reading cert ha ht
  rw [hleft, hright]
  have hl := mul_lt_mul_of_pos_left qleft htpos
  have hr := mul_lt_mul_of_pos_left qright htpos
  constructor <;> linarith

end
end GaussianSideSign

#print axioms GaussianSideSign.quantitative_reading
#print axioms GaussianSideSign.side_reading
#print axioms GaussianSideSign.zero_requires_line
#print axioms GaussianSideSign.bracket_margin
#print axioms GaussianSideSign.real_axis_positive
#print axioms GaussianSideSign.zero_requires_line_whole_rectangle
