import DedekindMixedThetaFiniteSamples

namespace FieldTarget

open Complex MeasureTheory Set SuperZeta.StirlingCorrection
open DedekindZetaZeroFree.AbelianQuotient

/-- A disk whose circumference has a strict sign in some fixed direction. -/
def HasDottieBoundarySign (F : ℂ → ℂ) (T : ℝ) (n : ℕ) : Prop :=
  ∃ axis : ℂ, ∃ margin : ℝ, 0 < margin ∧
    ∀ z ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (axis * F z).im ≤ -margin

/-- Pointwise choices of signed disks suffice for a finite cover of a bounded band. -/
theorem hasFiniteDottieBoundaryCertificate_of_local_signs {Z F : ℂ → ℂ} {l u ε : ℝ}
    (hε : 0 < ε)
    (hclear : ∀ w : ℂ, w.im ∈ Icc l u → 1/2 < w.re → w.re ≤ 31/32 →
      w.re - 1/2 < ε → Z w ≠ 0)
    (hlocal : ∀ w : ℂ, w.im ∈ Icc l u → 1/2 + ε ≤ w.re → w.re ≤ 31/32 →
      ∃ a : DottieBandRing l u,
        w ∈ Metric.ball (dottieScaledRightCenter a.val.1 a.val.2) (dottieScaledRadius a.val.2) ∧
        HasDottieBoundarySign F a.val.1 a.val.2) :
    HasFiniteDottieBoundaryCertificate Z F l u := by
  classical
  let SignedDisk := {a : DottieBandRing l u // HasDottieBoundarySign F a.val.1 a.val.2}
  let patch (a : SignedDisk) : Set ℂ :=
    Metric.ball (dottieScaledRightCenter a.val.val.1 a.val.val.2)
      (dottieScaledRadius a.val.val.2)
  let box := Icc ((1/2 : ℝ) + ε) (31/32) ×ℂ Icc l u
  have hb : IsCompact box := isCompact_Icc.reProdIm isCompact_Icc
  have hcover : box ⊆ ⋃ a, patch a := by
    intro w hw
    obtain ⟨hre, him⟩ := mem_reProdIm.mp hw
    obtain ⟨a, ha, hsign⟩ := hlocal w him hre.1 hre.2
    exact mem_iUnion.mpr ⟨⟨a, hsign⟩, ha⟩
  obtain ⟨disks, hdisks⟩ := hb.elim_finite_subcover patch (fun _ => Metric.isOpen_ball) hcover
  refine ⟨ε, hε, disks.image Subtype.val, hclear, ?_, ?_⟩
  · intro w him hlo hhi
    obtain ⟨a, ha⟩ := mem_iUnion.mp (hdisks (mem_reProdIm.mpr ⟨⟨hlo, hhi⟩, him⟩))
    obtain ⟨hm, hw⟩ := mem_iUnion.mp ha
    exact ⟨a.val, Finset.mem_image.mpr ⟨a, hm, rfl⟩, hw⟩
  · intro a ha
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp ha
    exact b.property

/-- Finite rational samples and explicit allowances on one measuring disk. -/
def HasDottieCompletedSamples (K : Type) [Field K] [NumberField K] (T : ℝ) (n : ℕ) : Prop :=
  ∃ R : ℝ, 1 ≤ R ∧ ∃ m : ℕ, 0 < m ∧ ∃ axis : ℂ, ‖axis‖ = 1 ∧
    ∃ margin : ℝ, 0 < margin ∧ ∃ tail : ℝ,
    2 * ∫ t : ℝ in Ioi R, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖ ≤ tail ∧
    ∀ a ∈ contourQuarterTurns, ∀ j ≤ m,
      (axis * mixedThetaCompletedTruncation K R
        (rationalContourSample (dottieScaledRightCenter T n) (dottieScaledRadius n) a m j)).im +
          mixedThetaContourVariation K R (dottieScaledRightCenter T n) (dottieScaledRadius n) *
            (2 * dottieScaledRadius n / (m : ℝ)) + tail ≤ -margin

/-- A local sample certificate at each point beyond the clearance yields the band certificate. -/
theorem hasFiniteDottieBoundaryCertificate_of_completed_samples
    (K : Type) [Field K] [NumberField K] {l u : ℝ}
    (hlocal : ∀ ε : ℝ, 0 < ε → ∀ w : ℂ, w.im ∈ Icc l u →
      1/2 + ε ≤ w.re → w.re ≤ 31/32 →
      ∃ a : DottieBandRing l u,
        w ∈ Metric.ball (dottieScaledRightCenter a.val.1 a.val.2) (dottieScaledRadius a.val.2) ∧
        HasDottieCompletedSamples K a.val.1 a.val.2) :
    HasFiniteDottieBoundaryCertificate (mixedThetaContinuation K) (mixedThetaCompletedReading K)
      l u := by
  obtain ⟨ε, hε, hclear⟩ := exists_dedekind_band_clearance (mixedThetaContinuation_isDedekind K) l u
  refine hasFiniteDottieBoundaryCertificate_of_local_signs hε hclear ?_
  intro w him hlo hhi
  obtain ⟨a, ha, R, hR, m, hm, axis, haxis, margin, hmargin, tail, hTail, hSamples⟩ :=
    hlocal ε hε w him hlo hhi
  exact ⟨a, ha, axis, margin, hmargin,
    dottie_completed_boundary_of_rational_samples K R hR hm axis haxis hTail hSamples⟩

#check @hasFiniteDottieBoundaryCertificate_of_completed_samples
#print axioms hasFiniteDottieBoundaryCertificate_of_local_signs
#print axioms hasFiniteDottieBoundaryCertificate_of_completed_samples

end FieldTarget
