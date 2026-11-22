import QuarticTurn
import QuarterReflectedReadings
import SuperZeta.GaussianRingMidpoint

/-! Test the implication from reversibility to exclusion on the project's
original open annulus. The candidate point and the spectral map are fixed.
The comparison polynomial is explicitly a control, not a Hecke factor. -/
namespace SuperZeta.RingReversibility
noncomputable section
open QuarticTurn GaussianRingMidpoint StirlingCorrection
open scoped ComplexConjugate

private theorem height_ge : 203 ≤ dottieHeight := by
  have hr : 0 ≤ witnessRatio := by norm_num [witnessRatio]
  have hlog : Real.log (1+witnessRatio) ≤ witnessRatio := by
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1+witnessRatio)
  have hsmall : 203 * (160 * witnessRatio) ≤ (6 : ℝ) := by norm_num [witnessRatio]
  unfold dottieHeight
  apply (le_div_iff₀ heightDelta_pos).mpr
  unfold heightDelta
  linarith [Real.pi_gt_three]

def mirror (w : ℂ) := 1 - conj w

/-- Phi uses the continued unit-coupling sum, evaluated at the halved input. -/
def phi (w : ℂ) := UnitSpectrum.continuation (w / 2)

theorem addresses_separate {w : ℂ} (hw : w ∈ rightRing) :
    phi w ≠ phi (mirror w) := by
  have h := QuarterReflectedReadings.disk_spectral_order height_ge
    (w := w) (Metric.mem_closedBall.mpr (show
      ‖w - GaussianDiskCount.rightCenter dottieHeight‖ ≤ 31/2048 from hw.2.le))
  exact fun he => (ne_of_lt h.2) (congrArg (fun z : ℂ => ‖z‖) he)

/-- The proposed contradiction succeeds precisely when a Gaussian zero
forces equality of the two original spectral addresses. G stays fixed
on both sides of this equivalence. -/
theorem address_collision_iff_ring_clear (G : ℂ → ℂ) :
    (∀ w ∈ rightRing, G w = 0 → phi w = phi (mirror w)) ↔
      ∀ w ∈ rightRing, G w ≠ 0 := by
  constructor
  · exact fun force w hw hz => addresses_separate hw (force w hw hz)
  · exact fun clear w hw hz => False.elim (clear w hw hz)

def inputOfRing {w : ℂ} (hw : w ∈ rightRing) : Input := by
  have h := QuarterReflectedReadings.right_disk_coordinates height_ge
    (w := w) (Metric.mem_closedBall.mpr (show
      ‖w - GaussianDiskCount.rightCenter dottieHeight‖ ≤ 31/2048 from hw.2.le))
  refine ⟨w, ?_⟩
  change (_ ≤ (w/2).re ∧ (w/2).re ≤ _) ∧ _ ≤ (w/2).im
  simp only [Complex.div_ofNat_re, Complex.div_ofNat_im]
  exact ⟨⟨by linarith [h.1], by linarith [h.2.1]⟩, h.2.2⟩

/-- Fix G, its companion D, and w in the actual annulus. A zero is
equivalent to the stated rotated pair together with exact input recovery
and distinct reflected addresses. No comparison function enters this lemma. -/
theorem fixed_reading_at_zero (G D : ℂ → ℂ) {w : ℂ} (hw : w ∈ rightRing) :
    let x := inputOfRing hw
    G w = 0 ↔
      jTurn (inChart (fun t => (G t.val, D t.val)) (chart x)) = (-star (D w), 0) ∧
      chart.symm (chart x) = x ∧ phi w ≠ phi (mirror w) := by
  dsimp only
  rw [same_reading]
  change G w = 0 ↔ (-star (D w), star (G w)) = (-star (D w), 0) ∧ _
  constructor
  · intro hz
    exact ⟨by simp [hz], same_input _, addresses_separate hw⟩
  · intro h
    have hzero : star (G w) = 0 := congrArg Prod.snd h.1
    simpa using hzero

/-- The eastward displacement is halfway between the two specified radii. -/
def rho := GaussianDiskCount.rightCenter dottieHeight + ((61 / 4096 : ℝ) : ℂ)

theorem rho_mem : rho ∈ rightRing := by
  change GaussianDiskCount.radius < ‖rho - GaussianDiskCount.rightCenter dottieHeight‖ ∧
    ‖rho - GaussianDiskCount.rightCenter dottieHeight‖ < (31 / 2048 : ℝ)
  norm_num [rho, GaussianDiskCount.radius, Complex.norm_real, Real.norm_eq_abs]

theorem mirror_rho_mem :
    GaussianDiskCount.radius < dist (mirror rho) (GaussianDiskCount.leftCenter dottieHeight) ∧
    dist (mirror rho) (GaussianDiskCount.leftCenter dottieHeight) < (31 / 2048 : ℝ) := by
  rw [← GaussianDiskCount.reflect_center, mirror, GaussianDiskCount.reflect_dist]
  exact rho_mem

private theorem east_mem_strip : rho / 2 ∈ QuarterOriginalUnivalent.strip := by
  change (_ ≤ (rho/2).re ∧ (rho/2).re ≤ _) ∧ _ ≤ (rho/2).im
  norm_num [rho, GaussianDiskCount.rightCenter, Complex.div_ofNat_re, Complex.div_ofNat_im]
  linarith [height_ge]

private theorem west_mem_strip : mirror rho / 2 ∈ QuarterOriginalUnivalent.strip := by
  change (_ ≤ (mirror rho/2).re ∧ (mirror rho/2).re ≤ _) ∧ _ ≤ (mirror rho/2).im
  simp only [mirror, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, zero_sub, neg_neg]
  norm_num [rho, GaussianDiskCount.rightCenter]
  linarith [height_ge]

def east : Input := ⟨rho, east_mem_strip⟩
def west : Input := ⟨mirror rho, west_mem_strip⟩

/-- Both roots are genuine addresses of the original spectral function. -/
def control (ξ : ℂ) := (ξ - phi rho) * (ξ - phi (mirror rho))

theorem control_zeros (w : Input) :
    control (address w) = 0 ↔ w = east ∨ w = west := by
  simp only [control, mul_eq_zero, sub_eq_zero]
  have inj : Function.Injective address := by
    intro x y h
    apply chart.injective
    exact Subtype.ext h
  change (address w = address east ∨ address w = address west) ↔ _
  simp only [inj.eq_iff]

/-- At either root, preserve any supplied total D.
The marked reading returns after four turns.
No value or regularity of the true Gaussian factor is postulated here. -/
theorem control_round_trip (D : Input → ℂ) {w : Input} (hw : w = east ∨ w = west) :
    let q := inChart (fun t => (control (address t), D t)) (chart w)
    q = (0, D w) ∧ jTurn q = (-star (D w), 0) ∧
      jTurn (jTurn (jTurn (jTurn q))) = q ∧ chart.symm (chart w) = w := by
  dsimp only
  rw [same_reading, (control_zeros w).mpr hw]
  exact ⟨rfl, (orbit_at_gaussian_zero _).1, four_jTurns _, same_input _⟩

end
end SuperZeta.RingReversibility

#print axioms SuperZeta.RingReversibility.address_collision_iff_ring_clear
#print axioms SuperZeta.RingReversibility.fixed_reading_at_zero
#print axioms SuperZeta.RingReversibility.rho_mem
#print axioms SuperZeta.RingReversibility.mirror_rho_mem
#print axioms SuperZeta.RingReversibility.control_zeros
#print axioms SuperZeta.RingReversibility.control_round_trip
