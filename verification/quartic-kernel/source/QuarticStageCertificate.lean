import QuarticStageAxes
import QuarticVerified

namespace SuperZeta.QuarticStageAxes
noncomputable section
open QuarticOrderedTurns

/-- This theorem uses the completed *numerical* certificate. Its inputs are
    the launch, offset and height; no Gaussian value or quadrature bound. -/
theorem low_stage_axis (l : Launch) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) :
    let w := GaussianSideSign.point a t
    (J * pack (stageValue l w) (HiddenQuarticQuaternion.total w)).imK =
        -(a*t*GaussianSideIntegral.slope QuarticKernel.kernel a t) ∧
      400000 < GaussianSideIntegral.slope QuarticKernel.kernel a t := by
  dsimp only
  have hw : |(GaussianSideSign.point a t).re - 1/2| ≤ 1/20 := by
    simpa [GaussianSideSign.point] using ha
  rw [stage_eq_full l hw]
  obtain ⟨him, hs⟩ := QuarticKernel.verified_quartic_direction ha ht
  change (QuarticSignedOrders.full _).im = _ at him
  refine ⟨?_, hs⟩
  simpa [J, pack, Quaternion.mul_imK] using congrArg Neg.neg him

theorem low_k_ne_zero (l : Launch) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) (hne : a ≠ 0) (htne : t ≠ 0) :
    let w := GaussianSideSign.point a t
    (J * pack (stageValue l w) (HiddenQuarticQuaternion.total w)).imK ≠ 0 := by
  obtain ⟨hk, hs⟩ := low_stage_axis l ha ht
  dsimp only
  rw [hk]
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero hne htne) (by linarith))

theorem low_stage_zero_on_line (l : Launch) {a t : ℝ}
    (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100)
    (hz : stageValue l (GaussianSideSign.point a t) = 0) : a = 0 := by
  have hw : |(GaussianSideSign.point a t).re - 1/2| ≤ 1/20 := by
    simpa [GaussianSideSign.point] using ha
  rw [stage_eq_full l hw] at hz
  have h := QuarticKernel.verified_quartic_zero_on_line ha ht hz
  change 1/2 + a = (1/2 : ℝ) at h
  linarith

/-- One launch and one conductor are used for the reflection, the observable,
    the two high-chart comparisons and the low-height sign certificate. -/
structure Verification (l : Launch) : Prop where
  marks : weight (generator l 3 8) = -1 ∧ weight (generator l 3 (-8)) = 1
  positive_root_number : QuarticFiniteFourier.quarticCharacter.rootNumber = 1
  reflect_theta : ∀ t > (0 : ℝ), theta l (t/QuarticKernel.scale) =
    t⁻¹ * theta l (t⁻¹/QuarticKernel.scale)
  full_mellin : ∀ w : ℂ, |w.re - 1/2| ≤ 1/20 → stageValue l w = QuarticSignedOrders.full w
  at_address : ∀ x : QuarticTurn.Input,
    QuarticTurn.chart.symm (QuarticTurn.chart x) = x ∧
    (J * reading (QuarticTurn.chart x)).imJ = (stageValue l x.val).re ∧
    (J * reading (QuarticTurn.chart x)).imK = -(stageValue l x.val).im
  scalar_and_orders : ∀ x : QuarticTurn.Input,
    (QuarticTurn.address x = Reference.entireCorrection 1 (x.val/2) ↔ riemannZeta x.val = 0) ∧
    jk (reading (QuarticTurn.chart x)) - kj (reading (QuarticTurn.chart x)) =
      pack (2 * Complex.I * star (stageValue l x.val)) 0
  reflected_axes : ∀ x : QuarticTurn.Input,
    let q := J * reading (QuarticTurn.chart x)
    let qMirror := J * reading (QuarticTurn.chart (ReflectedGaussianReading.reflectedInput x))
    qMirror.imJ = q.imJ ∧ qMirror.imK = -q.imK
  axis_length : ∀ x : QuarticTurn.Input,
    let q := J * reading (QuarticTurn.chart x)
    q.imJ ^ 2 + q.imK ^ 2 = Complex.normSq (QuarticSignedOrders.full x.val)
  low_zeros : ∀ a t : ℝ, |a| ≤ 1/20 → |t| ≤ 27/100 →
    stageValue l (GaussianSideSign.point a t) = 0 → a = 0
  low_k_survives : ∀ a t : ℝ, |a| ≤ 1/20 → |t| ≤ 27/100 → a ≠ 0 → t ≠ 0 →
    let w := GaussianSideSign.point a t
    (J * pack (stageValue l w) (HiddenQuarticQuaternion.total w)).imK ≠ 0

theorem verified_stage_chain : ∃ l : Launch, Verification l := by
  obtain ⟨l⟩ := launch_exists
  exact ⟨l, ⟨opposite_marks_73 l, QuarticConductorSign.root_number,
    fun _ ht => theta_reflection l ht, fun _ ha => stage_eq_full l ha,
    axes_at_address l, both_tests_at_address l, axes_at_mirror_addresses l,
    axis_length_at_address l, fun _ _ => low_stage_zero_on_line l,
    fun _ _ => low_k_ne_zero l⟩⟩

end
end SuperZeta.QuarticStageAxes

#print axioms SuperZeta.QuarticStageAxes.low_stage_axis
#print axioms SuperZeta.QuarticStageAxes.low_k_ne_zero
#print axioms SuperZeta.QuarticStageAxes.low_stage_zero_on_line
#print axioms SuperZeta.QuarticStageAxes.verified_stage_chain
