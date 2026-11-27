import DedekindFiniteDottieCover
import Mathlib.Analysis.Complex.AbsMax

/-! Finite boundary certificates exclude same-input zeros on bounded height
bands. A family of such certificates yields the full-strip implication. -/

namespace FieldTarget

open Complex Set ArtinPrimitiveRootsConjecture SuperZeta.StirlingCorrection
open scoped ComplexConjugate

/-- Finite data and its checked bounds for one bounded height band. -/
def HasFiniteDottieBoundaryCertificate (Z F : ℂ → ℂ) (l u : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∃ disks : Finset (DottieBandRing l u),
    (∀ w : ℂ, w.im ∈ Icc l u → 1/2 < w.re → w.re ≤ 31/32 →
      w.re - 1/2 < ε → Z w ≠ 0) ∧
    (∀ w : ℂ, w.im ∈ Icc l u → 1/2 + ε ≤ w.re → w.re ≤ 31/32 →
      ∃ a ∈ disks, w ∈ Metric.ball (dottieScaledRightCenter a.val.1 a.val.2)
        (dottieScaledRadius a.val.2)) ∧
    ∀ a ∈ disks, ∃ axis : ℂ, ∃ margin : ℝ, 0 < margin ∧
      ∀ z ∈ Metric.sphere (dottieScaledRightCenter a.val.1 a.val.2) (dottieScaledRadius a.val.2),
        (axis * F z).im ≤ -margin

/-- One signed inequality along a circumference excludes a zero of its
holomorphic reading everywhere in the closed disk. -/
theorem dottie_disk_nonzero_of_signed_boundary {F : ℂ → ℂ} {T margin : ℝ} {n : ℕ} {axis : ℂ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hm : 0 < margin)
    (hboundary : ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (axis * F z).im ≤ -margin)
    {w : ℂ} (hw : w ∈ Metric.closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    F w ≠ 0 := by
  let c := dottieScaledRightCenter T n
  let r := dottieScaledRadius n
  have hr : 0 < r := by dsimp [r, dottieScaledRadius, dottieRingScale]; positivity
  let f := fun z : ℂ => Complex.exp (-I * (axis * F z))
  have hsub : closure (Metric.ball c r) ⊆ Complex.re ⁻¹' Ioo (0 : ℝ) 1 := by
    rw [closure_ball c hr.ne']
    intro z hz
    have hh := dottieScaledRightDisk_strip hz
    exact ⟨(by norm_num : (0:ℝ) < 1/2).trans hh.1, hh.2⟩
  have hF' := hF.mono hsub
  have hreg : DifferentiableOn ℂ f (closure (Metric.ball c r)) :=
    Complex.differentiable_exp.comp_differentiableOn
      ((differentiableOn_const (-I)).mul ((differentiableOn_const axis).mul hF'))
  have hnorm (z : ℂ) : ‖f z‖ = Real.exp ((axis * F z).im) := by
    change ‖Complex.exp (-I * (axis * F z))‖ = _
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hedge : ∀ z ∈ frontier (Metric.ball c r), ‖f z‖ ≤ Real.exp (-margin) := by
    intro z hz
    rw [frontier_ball c hr.ne'] at hz
    rw [hnorm, Real.exp_le_exp]
    exact hboundary z hz
  have hclosed : w ∈ closure (Metric.ball c r) := by rwa [closure_ball c hr.ne']
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball
    hreg.diffContOnCl hedge hclosed
  rw [hnorm, Real.exp_le_exp] at hbound
  intro h
  rw [h, mul_zero, zero_im] at hbound
  linarith

/-- A finite boundary certificate excludes a zero of the given continuation
on the part of this band to the right of the line and through `31/32`. -/
theorem dottie_band_nonzero_of_certificate {Z F : ℂ → ℂ} {l u : ℝ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hzero : ∀ z : ℂ, 0 < z.re → z.re < 1 → Z z = 0 → F z = 0)
    (cert : HasFiniteDottieBoundaryCertificate Z F l u)
    {w : ℂ} (him : w.im ∈ Icc l u) (hre : 1/2 < w.re) (hhi : w.re ≤ 31/32) : Z w ≠ 0 := by
  obtain ⟨ε, _, rings, hclear, hcover, hbound⟩ := cert
  by_cases h : w.re - 1/2 < ε
  · exact hclear w him hre hhi h
  · obtain ⟨a, ha, hw⟩ := hcover w him (by linarith [le_of_not_gt h]) hhi
    obtain ⟨axis, margin, hm, hb⟩ := hbound a ha
    have hball := Metric.ball_subset_closedBall hw
    exact fun hz => dottie_disk_nonzero_of_signed_boundary hF hm hb hball
      (hzero w (by linarith) (by linarith) hz)

/-- Cofinal bounded-band certificates, horizontal reflection, and the
rightmost zero-free strip imply the exact Dedekind zeta statement. -/
theorem dedekindZetaRH_of_finite_signed_dottie_boundaries {K : Type*} [Field K] [NumberField K]
    {Z F : ℂ → ℂ} (hZ : IsDedekindZeta K Z)
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hzero : ∀ z : ℂ, 0 < z.re → z.re < 1 → Z z = 0 → F z = 0)
    (hreflect : ∀ z : ℂ, 0 < z.re → z.re < 1 → Z z = 0 → Z (1-conj z) = 0)
    (hrightmost : ∀ z : ℂ, 31/32 < z.re → z.re < 1 → Z z ≠ 0)
    (hbands : ∀ N : ℕ, HasFiniteDottieBoundaryCertificate Z F (-(N : ℝ)) (N : ℝ)) :
    DedekindZetaRH K := by
  have hright (z : ℂ) (hre : 1/2 < z.re) (hu : z.re < 1) : Z z ≠ 0 := by
    by_cases h : z.re ≤ 31/32
    · obtain ⟨N, hN⟩ := exists_nat_gt |z.im|
      exact dottie_band_nonzero_of_certificate hF hzero (hbands N) (abs_le.mp hN.le) hre h
    · exact hrightmost z (lt_of_not_ge h) hu
  apply (dedekindZetaRH_iff_strip hZ).mpr
  intro z hlo hhi hz
  rcases lt_trichotomy z.re (1/2 : ℝ) with hleft | heq | hr
  · exfalso
    apply hright (1-conj z) _ _ (hreflect z hlo hhi hz)
    · simp only [sub_re, one_re, conj_re]
      linarith
    · simp only [sub_re, one_re, conj_re]
      linarith
  · exact heq
  · exact (hright z hr hhi hz).elim

#check @dedekindZetaRH_of_finite_signed_dottie_boundaries
#print axioms dottie_disk_nonzero_of_signed_boundary
#print axioms dottie_band_nonzero_of_certificate
#print axioms dedekindZetaRH_of_finite_signed_dottie_boundaries

end FieldTarget
