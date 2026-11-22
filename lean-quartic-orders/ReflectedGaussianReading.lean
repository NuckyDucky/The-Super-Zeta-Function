import RingReversibility
import SuperZeta.GaussianSidePair
import SuperZeta.FieldWeights

/-! The input involution and the Hamilton turn have different types.
We use the centered half-Mellin representation with the project's explicit
quartic conductor character. Its identification with the analytic Hecke
completion is the arithmetic Mellin identity in the Gaussian pinch paper. -/
namespace SuperZeta.ReflectedGaussianReading
noncomputable section
open QuarticTurn RingReversibility GaussianRingMidpoint
open scoped ComplexConjugate

/-- One generator m+ni per ideal, m positive and n nonnegative. -/
def theta (u : ℝ) : ℝ := ∑' p : ℕ × ℕ,
  let m : ℕ := p.1 + 1
  let n := p.2
  (FieldWeights.conductorReading m n : ℝ) *
    Real.exp (-((m ^ 2 + n ^ 2 : ℕ) : ℝ) * u)

def scale : ℝ := Real.sqrt (4 * 41 * 457 * 1414835497) / (2 * Real.pi)

def kernel (x : ℝ) := Real.exp (x / 2) * theta (Real.exp x / scale)

def completed (w : ℂ) := PinchRadius.halfMellin kernel ⟨w.re - 1/2, w.im⟩

theorem completed_mirror (w : ℂ) : completed (mirror w) = conj (completed w) := by
  have hr : (mirror w).re - 1/2 = -(w.re - 1/2) := by
    simp only [mirror, Complex.sub_re, Complex.one_re, Complex.conj_re]
    ring
  have hi : (mirror w).im = w.im := by simp [mirror]
  simpa only [completed, hr, hi] using GaussianSidePair.halfMellin_reflect kernel (w.re - 1/2) w.im

def reflectedInput (x : Input) : Input := ⟨mirror x.val, by
  obtain ⟨⟨hl, hu⟩, ht⟩ := x.property
  change 15/64 ≤ (x.val/2).re at hl
  change (x.val/2).re ≤ 17/64 at hu
  change 101 ≤ (x.val/2).im at ht
  change (_ ≤ (mirror x.val/2).re ∧ (mirror x.val/2).re ≤ _) ∧ _ ≤ (mirror x.val/2).im
  simp only [Complex.div_ofNat_re, Complex.div_ofNat_im] at hl hu ht
  simp only [mirror, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.sub_re,
    Complex.sub_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im,
    zero_sub, neg_neg]
  exact ⟨⟨by linarith, by linarith⟩, ht⟩⟩

def reflectedAddress (ξ : Set.range address) := chart (reflectedInput (chart.symm ξ))

theorem reflectedAddress_twice (ξ : Set.range address) :
    reflectedAddress (reflectedAddress ξ) = ξ := by
  have h (x : Input) : reflectedInput (reflectedInput x) = x := by
    apply Subtype.ext
    change 1 - conj (1 - conj x.val) = x.val
    simp
  simp only [reflectedAddress, chart.symm_apply_apply, h, chart.apply_symm_apply]

/-- A marked state consists of its original spectral address and two
complex components. D is arbitrary because j reads its other coordinate. -/
def state (x : Input) (D : ℂ → ℂ) := (chart x, (completed x.val, D x.val))

def turnAtAddress (p : Set.range address × (ℂ × ℂ)) := (p.1, jTurn p.2)

/-- The second component after the turn reads the completion at the mirror,
while the inverse address still picks out the original input. -/
theorem reading_and_input (x : Input) (D : ℂ → ℂ) :
    let out := turnAtAddress (state x D)
    out.2.2 = completed (mirror x.val) ∧ chart.symm out.1 = x ∧
      chart.symm (reflectedAddress out.1) = reflectedInput x := by
  dsimp only [turnAtAddress, state, jTurn, reflectedAddress]
  exact ⟨(completed_mirror _).symm, same_input _, by simp⟩

def returnsMirror (p : Set.range address × (ℂ × ℂ)) (w : ℂ) : Bool :=
  decide ((chart.symm p.1).val = mirror w)

theorem returnsMirror_false {w : ℂ} (hw : w ∈ rightRing) (D : ℂ → ℂ) :
    returnsMirror (turnAtAddress (state (inputOfRing hw) D)) w = false := by
  have h : w ≠ mirror w := fun he => addresses_separate hw (congrArg phi he)
  unfold returnsMirror
  change decide ((chart.symm (chart (inputOfRing hw))).val = mirror w) = false
  simp only [same_input]
  change decide (w = mirror w) = false
  simp [h]

/-- Assuming the user's hypothetical zero changes the reflected reading to
zero. It still does not send the inverse to the mirror. -/
theorem zero_case {w : ℂ} (hw : w ∈ rightRing) (D : ℂ → ℂ) (hz : completed w = 0) :
    let out := turnAtAddress (state (inputOfRing hw) D)
    out.2.2 = 0 ∧ completed (mirror w) = 0 ∧ returnsMirror out w = false := by
  have hm : completed (mirror w) = 0 := by rw [completed_mirror, hz]; simp
  exact ⟨(reading_and_input (inputOfRing hw) D).1.trans hm, hm, returnsMirror_false hw D⟩

/-- Hide the address and give a decoder only the completed Gaussian value.
For this fixed reflected pair, one rule can then recover both spectral
addresses exactly when the measured imaginary part is nonzero. The rule
may depend on the two candidates. -/
theorem decode_pair_iff {w : ℂ} (hw : w ∈ rightRing) :
    (∃ decode : ℂ → ℂ, decode (completed w) = phi w ∧
      decode (completed (mirror w)) = phi (mirror w)) ↔ (completed w).im ≠ 0 := by
  classical
  have same : completed (mirror w) = completed w ↔ (completed w).im = 0 := by
    rw [completed_mirror]
    constructor
    · intro h
      have hi := congrArg Complex.im h
      rw [Complex.conj_im] at hi
      linarith
    · intro hi
      apply Complex.ext
      · exact Complex.conj_re _
      · simp [hi]
  constructor
  · rintro ⟨decode, hr, hl⟩ hi
    exact addresses_separate hw (hr.symm.trans ((congrArg decode (same.mpr hi).symm).trans hl))
  · intro hi
    refine ⟨fun z => if z = completed w then phi w else phi (mirror w), by simp, ?_⟩
    exact if_neg (fun h => hi (same.mp h))

theorem zero_forbids_gaussian_only_inverse {w : ℂ} (hw : w ∈ rightRing)
    (hz : completed w = 0) :
    ¬ ∃ decode : ℂ → ℂ, decode (completed w) = phi w ∧
      decode (completed (mirror w)) = phi (mirror w) := by
  rw [decode_pair_iff hw, hz]
  simp

end
end SuperZeta.ReflectedGaussianReading

#print axioms SuperZeta.ReflectedGaussianReading.completed_mirror
#print axioms SuperZeta.ReflectedGaussianReading.reflectedAddress_twice
#print axioms SuperZeta.ReflectedGaussianReading.reading_and_input
#print axioms SuperZeta.ReflectedGaussianReading.returnsMirror_false
#print axioms SuperZeta.ReflectedGaussianReading.zero_case
#print axioms SuperZeta.ReflectedGaussianReading.decode_pair_iff
#print axioms SuperZeta.ReflectedGaussianReading.zero_forbids_gaussian_only_inverse
