import QuarticOrderedTurns
import QuarticMurphyBridge
import QuarticMellinFold

/-! The primitive character fixes the reflection sign of the quartic norm theta
series. We compare its full Mellin integral in the original super-zeta chart.
The high-ring test uses both real coordinates of the same signed kernel. -/
open MeasureTheory Set
open scoped ComplexConjugate
namespace SuperZeta.QuarticSignedOrders
noncomputable section
open QuarticFiniteFourier QuarticOrderedTurns QuarticTurn RingReversibility GaussianRingMidpoint

theorem kernels_agree : ReflectedGaussianReading.kernel = QuarticKernel.kernel := by
  have hs : ReflectedGaussianReading.scale = QuarticKernel.scale := by
    unfold ReflectedGaussianReading.scale QuarticKernel.scale QuarticKernel.conductorNorm
    push_cast
    rw [show (4*41*457*1414835497 : ℝ) = 4*(41*457*1414835497) by norm_num,
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
    rw [show Real.sqrt 4 = 2 by
      apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
      norm_num]
    ring
  funext x
  unfold ReflectedGaussianReading.kernel QuarticKernel.kernel
  rw [hs, QuarticKernel.theta_quarter_lattice (div_pos (Real.exp_pos _) QuarticKernel.scale_pos)]
  congr 1
  unfold ReflectedGaussianReading.theta
  apply tsum_congr
  intro p
  push_cast
  ring_nf

def full (w : ℂ) := mellin (fun t : ℝ => (QuarticKernel.theta (t/QuarticKernel.scale) : ℂ)) w

/-- The equality applies at every height in this vertical strip. -/
theorem full_eq_completed (h : quarticCharacter.rootNumber = 1) (w : ℂ)
    (ha : |w.re - 1/2| ≤ 1/20) : full w = ReflectedGaussianReading.completed w := by
  have hK := QuarticKernel.theta_reflection_iff_kernel_even.mp
    (fun t ht => QuarticMurphyBridge.theta_reflection (QuarticMurphyBridge.amplitude h) ht)
  have hw : _root_.GaussianSideSign.point (w.re-1/2) w.im = w := by
    apply Complex.ext
    · change 1/2 + (w.re-1/2) = w.re
      ring
    · rfl
  unfold full ReflectedGaussianReading.completed
  rw [kernels_agree]
  simpa only [hw] using QuarticKernel.mellin_fold_in_rectangle hK (w.re-1/2) w.im ha

private theorem width (x : Input) : |x.val.re-1/2| ≤ 1/20 := by
  obtain ⟨⟨hl,hu⟩,_⟩ := x.property
  change 15/64 ≤ (x.val/2).re at hl
  change (x.val/2).re ≤ 17/64 at hu
  simp only [Complex.div_ofNat_re] at hl hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def difference (x : Input) := jk (reading (chart x)) - kj (reading (chart x))

theorem order_formula (h : quarticCharacter.rootNumber = 1) (x : Input) :
    difference x = pack (2 * Complex.I * conj (full x.val)) 0 := by
  unfold difference reading
  rw [same_reading, full_eq_completed h x.val (width x)]
  exact order_difference _ _

/-- Both coordinates of the order difference, in terms of the arithmetic kernel. -/
def cosineMoment (a t : ℝ) := ∫ x in Ici (0:ℝ),
  2 * QuarticKernel.kernel x * Real.cosh (a*x) * Real.cos (t*x)

theorem coordinates (x : Input) :
    let a := x.val.re - 1/2
    let t := x.val.im
    (difference x).re = 2 * (a*t*GaussianSideIntegral.slope QuarticKernel.kernel a t) ∧
      (difference x).imI = 2*cosineMoment a t := by
  dsimp only
  unfold difference reading
  rw [same_reading, order_difference]
  change (2 * Complex.I * conj (ReflectedGaussianReading.completed x.val)).re = _ ∧
    (2 * Complex.I * conj (ReflectedGaussianReading.completed x.val)).im = _
  let a := x.val.re-1/2
  let t := x.val.im
  have ha : |a| ≤ 1/20 := width x
  have hi := QuarticKernel.complex_integrable ha t
  have hreal : (PinchRadius.halfMellin QuarticKernel.kernel ⟨a,t⟩).re = cosineMoment a t := by
    unfold PinchRadius.halfMellin cosineMoment
    rw [← RCLike.re_eq_complex_re, ← integral_re hi]
    apply integral_congr_ae
    filter_upwards [] with y
    change ((2 : ℂ) * (QuarticKernel.kernel y : ℂ) *
      Complex.cosh ((⟨a,t⟩ : ℂ) * (y:ℂ))).re = _
    have hz : (⟨a,t⟩ : ℂ) * (y : ℂ) =
        ((a*y : ℝ) : ℂ) + ((t*y : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
    rw [hz, Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
    have h2r : (2 : ℂ).re = 2 := rfl
    have h2i : (2 : ℂ).im = 0 := rfl
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im, h2r, h2i, Complex.ofReal_re, Complex.ofReal_im,
      Complex.cosh_ofReal_re, Complex.cosh_ofReal_im, Complex.sinh_ofReal_re,
      Complex.sinh_ofReal_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, mul_zero, zero_mul, add_zero,
      zero_add, sub_zero, mul_one]
    ring
  have him := GaussianSideIntegral.halfMellin_im_eq QuarticKernel.kernel a t hi
  unfold ReflectedGaussianReading.completed
  rw [kernels_agree]
  change (2 * Complex.I * conj (PinchRadius.halfMellin QuarticKernel.kernel ⟨a,t⟩)).re = _ ∧
    (2 * Complex.I * conj (PinchRadius.halfMellin QuarticKernel.kernel ⟨a,t⟩)).im = _
  change _ = 2*(a*t*GaussianSideIntegral.slope QuarticKernel.kernel a t) ∧
    _ = 2*cosineMoment a t
  simp [Complex.mul_re, Complex.mul_im, him, hreal]

theorem ring_orders_iff (h : quarticCharacter.rootNumber = 1) {w : ℂ} (hw : w ∈ rightRing) :
    jk (reading (chart (inputOfRing hw))) ≠ kj (reading (chart (inputOfRing hw))) ↔ full w ≠ 0 := by
  rw [fixed_input_test, full_eq_completed h w (width (inputOfRing hw))]
  rfl

/-- At a fixed input in the right annulus, both real moments have to vanish together. -/
theorem ring_moments {w : ℂ} (hw : w ∈ rightRing) :
    jk (reading (chart (inputOfRing hw))) = kj (reading (chart (inputOfRing hw))) ↔
      cosineMoment (w.re-1/2) w.im = 0 ∧
        GaussianSideIntegral.slope QuarticKernel.kernel (w.re-1/2) w.im = 0 := by
  let x := inputOfRing hw
  have hreal := (coordinates x).1
  have him := (coordinates x).2
  change (difference x).re = 2*((w.re-1/2)*w.im*
    GaussianSideIntegral.slope QuarticKernel.kernel (w.re-1/2) w.im) at hreal
  change (difference x).imI = 2*cosineMoment (w.re-1/2) w.im at him
  have hradius : ‖w - GaussianDiskCount.rightCenter StirlingCorrection.dottieHeight‖ <
      31/2048 := hw.2
  have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hradius.le)).1
  simp only [Complex.sub_re, GaussianDiskCount.rightCenter] at hr
  have hwpos : 0 < w.re-1/2 := by linarith
  have ht := x.property.2
  change 101 ≤ (w/2).im at ht
  rw [Complex.div_ofNat_im] at ht
  have htpos : 0 < w.im := by linarith
  change jk (reading (chart x)) = kj (reading (chart x)) ↔ _
  rw [← sub_eq_zero]
  change difference x = 0 ↔ _
  constructor
  · intro h
    rw [h] at hreal him
    change 0 = _ at hreal him
    exact ⟨by linarith only [him], (mul_eq_zero.mp
      ((mul_eq_zero.mp hreal.symm).resolve_left (by norm_num))).resolve_left
        (mul_pos hwpos htpos).ne'⟩
  · rintro ⟨hc,hs⟩
    rw [hc,mul_zero] at him
    rw [hs,mul_zero,mul_zero] at hreal
    have pure : (difference x).imJ = 0 ∧ (difference x).imK = 0 := by
      unfold difference reading
      rw [same_reading, order_difference]
      exact ⟨rfl,rfl⟩
    apply Quaternion.ext
    · exact hreal
    · exact him
    · exact pure.1
    · exact pure.2

theorem full_zero_iff_moments (h : quarticCharacter.rootNumber = 1) {w : ℂ}
    (hw : w ∈ rightRing) : full w = 0 ↔
      cosineMoment (w.re-1/2) w.im = 0 ∧
        GaussianSideIntegral.slope QuarticKernel.kernel (w.re-1/2) w.im = 0 := by
  classical
  exact (not_iff_not.mp (ring_orders_iff h hw)).symm.trans (ring_moments hw)

/-- The numerical certificate supplies a distinct conclusion on its own height range. -/
theorem low_orders_of_certificate (cert : _root_.GaussianSideSign.Certificate full QuarticKernel.kernel)
    {a t : ℝ} (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) (hne : a ≠ 0) :
    let w := _root_.GaussianSideSign.point a t
    let q := pack (full w) (HiddenQuarticQuaternion.total w)
    jk q ≠ kj q := by
  dsimp only
  intro he
  have hz := (order_eq_iff _ _).mp he
  have hr := _root_.GaussianSideSign.zero_requires_line_whole_rectangle cert ha ht hz
  change 1/2 + a = (1/2 : ℝ) at hr
  exact hne (by linarith)

end
end SuperZeta.QuarticSignedOrders

#print axioms QuarticMurphyBridge.reflection_of_murphy
#print axioms SuperZeta.QuarticSignedOrders.kernels_agree
#print axioms SuperZeta.QuarticSignedOrders.order_formula
#print axioms SuperZeta.QuarticSignedOrders.coordinates
#print axioms SuperZeta.QuarticSignedOrders.ring_orders_iff
#print axioms SuperZeta.QuarticSignedOrders.ring_moments
#print axioms SuperZeta.QuarticSignedOrders.full_zero_iff_moments
#print axioms SuperZeta.QuarticSignedOrders.low_orders_of_certificate
