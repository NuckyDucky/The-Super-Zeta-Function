import SuperZeta.DedekindLift
import QuarticSignedOrders

/-! Reconstruct the two Hamilton axes using a reciprocal fixed pair and the
conductor of the specified quartic. The Gaussian value is hidden from stageValue. -/
namespace SuperZeta.QuarticStageAxes
noncomputable section
open Complex QuarticTurn QuarticOrderedTurns

structure Launch where
  L : ℂ
  P : ℂ
  Q : ℂ
  fixed : Reciprocal.step L (P, Q) = (P, Q)
  second_ne : -L * P ≠ 0
  ratio : L * Q / (-L * P) = I

theorem launch_exists : Nonempty Launch := by
  obtain ⟨L, U, V, hf, huv, hr, _⟩ := DedekindPhase.upper_half_plane I (by simp)
  have h₁ := congrArg Prod.fst huv
  have h₂ := congrArg Prod.snd huv
  change L * exp V = U at h₁
  change -L * exp U = V at h₂
  have hv : V ≠ 0 := by
    intro h
    rw [h, div_zero] at hr
    exact Complex.I_ne_zero hr.symm
  exact ⟨⟨L, exp U, exp V, hf, h₂.trans_ne hv, by rwa [h₁, h₂]⟩⟩

def generator (l : Launch) (m n : ℤ) : ℂ :=
  (m * (-l.L * l.P) + n * (l.L * l.Q)) / (-l.L * l.P)

theorem generator_coordinates (l : Launch) (m n : ℤ) :
    generator l m n = ⟨(m : ℝ), (n : ℝ)⟩ := by
  rw [generator, DedekindPhase.gaussian_generator_reading l.second_ne l.ratio]
  apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.mul_I_re,
    Complex.mul_I_im]

def weight (z : ℂ) : ℤ := FieldWeights.conductorReading ⌊z.re⌋ ⌊z.im⌋

theorem opposite_marks_73 (l : Launch) :
    weight (generator l 3 8) = -1 ∧ weight (generator l 3 (-8)) = 1 := by
  have decode (m n : ℤ) : weight (generator l m n) = FieldWeights.conductorReading m n := by
    rw [generator_coordinates, weight]
    change FieldWeights.conductorReading ⌊(m : ℝ)⌋ ⌊(n : ℝ)⌋ = _
    simp only [Int.floor_intCast]
  rw [decode, decode]
  exact QuarticKernel.sign_at_73

def theta (l : Launch) (u : ℝ) : ℝ := ∑' p : ℕ × ℕ,
  let z := generator l ((p.1 : ℤ) + 1) p.2
  (weight z : ℝ) * Real.exp (-u * normSq z)

theorem theta_eq (l : Launch) {u : ℝ} (hu : 0 < u) : theta l u = QuarticKernel.theta u := by
  rw [QuarticKernel.theta_quarter_lattice hu]
  apply tsum_congr
  intro p
  simp [generator_coordinates, weight, Complex.normSq_mk, pow_two]

theorem theta_reflection (l : Launch) {t : ℝ} (ht : 0 < t) :
    theta l (t / QuarticKernel.scale) = t⁻¹ * theta l (t⁻¹ / QuarticKernel.scale) := by
  rw [theta_eq l (div_pos ht QuarticKernel.scale_pos),
    theta_eq l (div_pos (inv_pos.mpr ht) QuarticKernel.scale_pos)]
  exact QuarticConductorSign.reflection ht

def kernel (l : Launch) (x : ℝ) :=
  Real.exp (x / 2) * theta l (Real.exp x / QuarticKernel.scale)

theorem kernel_eq (l : Launch) : kernel l = QuarticKernel.kernel := by
  funext x
  exact congrArg (Real.exp (x / 2) * ·)
    (theta_eq l (div_pos (Real.exp_pos _) QuarticKernel.scale_pos))

def stageValue (l : Launch) (w : ℂ) : ℂ :=
  PinchRadius.halfMellin (kernel l) ⟨w.re - 1/2, w.im⟩

theorem stage_eq_completed (l : Launch) (w : ℂ) :
    stageValue l w = ReflectedGaussianReading.completed w := by
  rw [stageValue, kernel_eq, ReflectedGaussianReading.completed, QuarticSignedOrders.kernels_agree]

theorem stage_eq_full (l : Launch) {w : ℂ} (ha : |w.re - 1/2| ≤ 1/20) :
    stageValue l w = QuarticSignedOrders.full w :=
  (stage_eq_completed l w).trans (QuarticSignedOrders.full_eq_completed w ha).symm

/-- A different sheet of the square launch retains exactly the same observable. -/
theorem launch_invariance (l l' : Launch) (w : ℂ) : stageValue l w = stageValue l' w :=
  (stage_eq_completed l w).trans (stage_eq_completed l' w).symm

theorem axes_at_address (l : Launch) (x : Input) :
    chart.symm (chart x) = x ∧
    (J * reading (chart x)).imJ = (stageValue l x.val).re ∧
    (J * reading (chart x)).imK = -(stageValue l x.val).im := by
  refine ⟨same_input x, ?_⟩
  rw [stage_eq_completed, reading, same_reading]
  simp [J, pack, HiddenQuarticQuaternion.hidden, Quaternion.mul_imJ, Quaternion.mul_imK]

theorem orders_differ_iff_axis_survives (l : Launch) (x : Input) :
    jk (reading (chart x)) ≠ kj (reading (chart x)) ↔
      (stageValue l x.val).re ≠ 0 ∨ (stageValue l x.val).im ≠ 0 := by
  rw [fixed_input_test, ← stage_eq_completed l]
  constructor
  · intro h
    by_cases hr : (stageValue l x.val).re = 0
    · exact Or.inr (fun hi => h (Complex.ext hr hi))
    · exact Or.inl hr
  · rintro (hr | hi) he
    · exact hr (congrArg Complex.re he)
    · exact hi (congrArg Complex.im he)

/-- The scalar Mellin comparison and the Hamilton discrepancy at the same original input. -/
theorem both_tests_at_address (l : Launch) (x : Input) :
    (address x = Reference.entireCorrection 1 (x.val / 2) ↔ riemannZeta x.val = 0) ∧
    jk (reading (chart x)) - kj (reading (chart x)) =
      pack (2 * I * star (stageValue l x.val)) 0 := by
  obtain ⟨⟨hl,hu⟩,_⟩ := x.property
  change 15/64 ≤ (x.val/2).re at hl
  change (x.val/2).re ≤ 17/64 at hu
  have h := (UnitSpectrum.equality_iff_riemann_zero (s := x.val/2)
    (by linarith) (by linarith)).2
  rw [show 2*(x.val/2) = x.val by ring] at h
  refine ⟨h, ?_⟩
  rw [stage_eq_completed, reading, same_reading, order_difference]
  rfl

theorem reflected_stage (l : Launch) (w : ℂ) :
    stageValue l (RingReversibility.mirror w) = star (stageValue l w) := by
  rw [stage_eq_completed, stage_eq_completed, ReflectedGaussianReading.completed_mirror]
  rfl

/-- At the two original spectral addresses, reflection preserves j and reverses k. -/
theorem axes_at_mirror_addresses (l : Launch) (x : Input) :
    let q := J * reading (chart x)
    let qMirror := J * reading (chart (ReflectedGaussianReading.reflectedInput x))
    qMirror.imJ = q.imJ ∧ qMirror.imK = -q.imK := by
  dsimp only
  obtain ⟨_, hj, hk⟩ := axes_at_address l x
  obtain ⟨_, hjm, hkm⟩ := axes_at_address l (ReflectedGaussianReading.reflectedInput x)
  rw [hj, hk, hjm, hkm]
  change (stageValue l (RingReversibility.mirror x.val)).re = _ ∧
    -(stageValue l (RingReversibility.mirror x.val)).im = _
  rw [reflected_stage]
  exact ⟨rfl, rfl⟩

/-- The squared length of the two stage-reconstructed axes measures the full arithmetic
    Mellin reading on the chart. In particular this applies at every right-ring input. -/
theorem axis_length_at_address (l : Launch) (x : Input) :
    let q := J * reading (chart x)
    q.imJ ^ 2 + q.imK ^ 2 = Complex.normSq (QuarticSignedOrders.full x.val) := by
  obtain ⟨⟨hl, hu⟩, _⟩ := x.property
  change 15/64 ≤ (x.val/2).re at hl
  change (x.val/2).re ≤ 17/64 at hu
  simp only [Complex.div_ofNat_re] at hl hu
  have hstrip : |x.val.re - 1/2| ≤ 1/20 := abs_le.mpr ⟨by linarith, by linarith⟩
  obtain ⟨_, hj, hk⟩ := axes_at_address l x
  dsimp only
  rw [hj, hk, stage_eq_full l hstrip, Complex.normSq_apply]
  ring

/-- This is the exclusion implication. The survival of an axis at each input
    is an explicit premise, distinct from recovery of its value. -/
theorem excludes_right_and_mirror (l : Launch)
    (survives : ∀ w ∈ GaussianRingMidpoint.rightRing,
      (stageValue l w).re ≠ 0 ∨ (stageValue l w).im ≠ 0)
    {w : ℂ} (hw : w ∈ GaussianRingMidpoint.rightRing) :
    ReflectedGaussianReading.completed w ≠ 0 ∧
      ReflectedGaussianReading.completed (RingReversibility.mirror w) ≠ 0 := by
  have h := survives w hw
  rw [stage_eq_completed] at h
  have hg : ReflectedGaussianReading.completed w ≠ 0 := by
    rintro he
    simp [he] at h
  exact ⟨hg, by simpa [ReflectedGaussianReading.completed_mirror] using hg⟩

end
end SuperZeta.QuarticStageAxes

#print axioms SuperZeta.QuarticStageAxes.launch_exists
#print axioms SuperZeta.QuarticStageAxes.opposite_marks_73
#print axioms SuperZeta.QuarticStageAxes.theta_reflection
#print axioms SuperZeta.QuarticStageAxes.stage_eq_full
#print axioms SuperZeta.QuarticStageAxes.axes_at_address
#print axioms SuperZeta.QuarticStageAxes.orders_differ_iff_axis_survives
#print axioms SuperZeta.QuarticStageAxes.excludes_right_and_mirror
