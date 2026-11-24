import ArchivedDottieSmoothedIdentity
import SuperZeta.QuarterLine.QuarticTurn

/-! Apply the original Super Zeta chart to the exact field completion and
its two Hamilton orderings on the original fixed Dottie ring. -/

open Complex Set
open scoped ComplexConjugate

namespace QuarticModel

open SuperZeta
open SuperZeta.StirlingCorrection
open SuperZeta.QuarticOrderedTurns

noncomputable def archivedRightInput {w : ℂ} (hw : w ∈ archivedDottieRightRing) :
    QuarticTurn.Input := by
  obtain ⟨h₁,h₂,h₃⟩ := archivedDottieRing_address hw
  exact ⟨w, ⟨⟨h₁,h₂⟩, h₃⟩⟩

noncomputable def archivedMirrorInput {w : ℂ} (hw : w ∈ archivedDottieRightRing) :
    QuarticTurn.Input := by
  obtain ⟨h₁,h₂,h₃⟩ := archivedDottieRing_address hw
  refine ⟨1-conj w, ?_⟩
  change (15/64 ≤ ((1-conj w)/2).re ∧ ((1-conj w)/2).re ≤ 17/64) ∧
    101 ≤ ((1-conj w)/2).im
  simp only [div_ofNat_re, div_ofNat_im, sub_re, one_re, conj_re, sub_im, one_im,
    conj_im, zero_sub, neg_neg] at h₁ h₂ h₃ ⊢
  exact ⟨⟨by linarith, by linarith⟩, h₃⟩

private theorem archivedRightInput_val {w : ℂ} (hw : w ∈ archivedDottieRightRing) :
    (archivedRightInput hw).val = w := by
  unfold archivedRightInput
  rcases archivedDottieRing_address hw with ⟨_, _, _⟩
  rfl

private theorem archivedMirrorInput_val {w : ℂ} (hw : w ∈ archivedDottieRightRing) :
    (archivedMirrorInput hw).val = 1-conj w := by
  unfold archivedMirrorInput
  rcases archivedDottieRing_address hw with ⟨_, _, _⟩
  rfl

theorem archivedDottieAddresses_separate {w : ℂ} (hw : w ∈ archivedDottieRightRing) :
    QuarticTurn.address (archivedRightInput hw) ≠ QuarticTurn.address (archivedMirrorInput hw) := by
  intro h
  have hab : QuarticTurn.chart (archivedRightInput hw) =
      QuarticTurn.chart (archivedMirrorInput hw) := Subtype.ext h
  have hw' := congrArg Subtype.val (QuarticTurn.chart.injective hab)
  rw [archivedRightInput_val hw, archivedMirrorInput_val hw] at hw'
  have hr := congrArg Complex.re hw'
  simp only [sub_re, one_re, conj_re] at hr
  have hgap := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr hw.2.le)
  linarith

/-- The actual field's three zero tests, all evaluated at the single input
recovered by the original Super Zeta chart. -/
theorem archivedFieldZero_at_chart (x : QuarticTurn.Input) (ink : ℂ → ℂ) :
    let f := fun y : QuarticTurn.Input => paintedReading y.val (ink y.val)
    let q := QuarticTurn.inChart f (QuarticTurn.chart x)
    archivedQuarticZeta x.val = 0 ↔
      QuarticTurn.address x = Reference.entireCorrection 1 (x.val/2) ∨
      FieldCoefficientTransfer.chi4.LFunction x.val = 0 ∨ jk q = kj q := by
  have hx : (15/64 ≤ (x.val/2).re ∧ (x.val/2).re ≤ 17/64) ∧ 101 ≤ (x.val/2).im :=
    x.property
  have hs₀ : 0 < (x.val/2).re := by linarith [hx.1.1]
  have hs₁ : (x.val/2).re < 1/2 := by linarith [hx.1.2]
  have hw₀ : 0 < x.val.re := by
    rw [Complex.div_ofNat_re] at hs₀
    linarith
  have hscalar := (UnitSpectrum.equality_iff_riemann_zero hs₀ hs₁).2
  rw [show 2*(x.val/2) = x.val by ring] at hscalar
  change QuarticTurn.address x = _ ↔ _ at hscalar
  dsimp only
  rw [QuarticTurn.same_reading, archivedQuarticZeta_zero_iff hw₀, hscalar]
  have horders : jk (paintedReading x.val (ink x.val)) = kj (paintedReading x.val (ink x.val)) ↔
      archivedMellin x.val = 0 := by
    rw [← sub_eq_zero, paintedReading, order_difference_after_paint, sub_eq_zero, order_eq_iff]
  rw [horders]

theorem archivedDottie_chart_painted_orders (hS : 0 < dottieCircleReference)
    (model : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieRetained w).im ≤ -(190*((w.re-1/2)*dottieCircleReference)))
    (tail : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieOmitted w).im ≤ 189*((w.re-1/2)*dottieCircleReference))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) (ink : ℂ → ℂ) :
    let right := archivedRightInput hw
    let left := archivedMirrorInput hw
    let f := fun x : QuarticTurn.Input => paintedReading x.val (ink x.val)
    let q := QuarticTurn.inChart f (QuarticTurn.chart right)
    let qm := QuarticTurn.inChart f (QuarticTurn.chart left)
    QuarticTurn.chart.symm (QuarticTurn.chart right) = right ∧
      QuarticTurn.chart.symm (QuarticTurn.chart left) = left ∧
      QuarticTurn.address right ≠ QuarticTurn.address left ∧
      0 < (J*q).imK ∧ (J*qm).imK < 0 ∧ jk q ≠ kj q ∧ jk qm ≠ kj qm := by
  dsimp only
  refine ⟨QuarticTurn.same_input _, QuarticTurn.same_input _,
    archivedDottieAddresses_separate hw, ?_⟩
  rw [QuarticTurn.same_reading, QuarticTurn.same_reading,
    archivedRightInput_val hw, archivedMirrorInput_val hw]
  exact dottie_ring_painted_orders_of_signed_bounds hS model tail hw (ink w) (ink (1-conj w))

#print axioms archivedDottieAddresses_separate
#print axioms archivedFieldZero_at_chart
#print axioms archivedDottie_chart_painted_orders

end QuarticModel
