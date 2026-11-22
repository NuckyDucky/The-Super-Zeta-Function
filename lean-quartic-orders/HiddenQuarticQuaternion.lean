import ReflectedGaussianReading
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace SuperZeta.HiddenQuarticQuaternion
noncomputable section
open RingReversibility GaussianRingMidpoint ReflectedGaussianReading
open scoped ComplexConjugate

abbrev disc : ℕ := 41 * 457 * 1414835497
local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

def atPrime (p : ℕ) [Fact (Nat.Prime p)] : DirichletCharacter ℂ p :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

def A : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
def B : DirichletCharacter ℂ disc :=
  DirichletCharacter.changeLevel (show 41 ∣ disc by decide) (atPrime 41) *
  DirichletCharacter.changeLevel (show 457 ∣ disc by decide) (atPrime 457) *
  DirichletCharacter.changeLevel (show 1414835497 ∣ disc by decide) (atPrime 1414835497)
def AB : DirichletCharacter ℂ (4 * disc) :=
  DirichletCharacter.changeLevel (show 4 ∣ 4 * disc by decide) A *
  DirichletCharacter.changeLevel (show disc ∣ 4 * disc by decide) B

def total (w : ℂ) := (riemannZeta w * AB.LFunction w + A.LFunction w * B.LFunction w) / 2

/-- The two complex coordinates of Λ + D j. No address or input is stored. -/
def hidden (w : ℂ) := (completed w, total w)

/-- A genuine observed quaternion with first coordinate zero gives both reflected zeros. -/
theorem observed_zero_iff {q : ℂ × ℂ} {w : ℂ}
    (record : q = hidden w ∨ q = hidden (mirror w)) :
    q.1 = 0 ↔ completed w = 0 ∧ completed (mirror w) = 0 := by
  have hr : completed (mirror w) = 0 ↔ completed w = 0 := by rw [completed_mirror]; simp
  rcases record with h | h <;> subst q <;> simp [hidden, hr]

/-- The original chart transports a zero at exactly the address of its input. -/
theorem zero_at_address (x : QuarticTurn.Input) :
    (QuarticTurn.inChart (fun y => hidden y.val) (QuarticTurn.chart x)).1 = 0 ↔
    completed x.val = 0 := by rw [QuarticTurn.same_reading]; rfl

/-- At a Gaussian zero, two candidates can be decoded exactly when their totals differ. -/
theorem address_decoder_iff {w : ℂ} (hw : w ∈ rightRing) (hz : completed w = 0) :
    (∃ f : ℂ × ℂ → ℂ, f (hidden w) = phi w ∧ f (hidden (mirror w)) = phi (mirror w)) ↔
      total w ≠ total (mirror w) := by
  classical
  have hm : completed (mirror w) = 0 := by rw [completed_mirror, hz]; simp
  constructor
  · rintro ⟨f, h₁, h₂⟩ he
    have eq : hidden w = hidden (mirror w) := Prod.ext (hz.trans hm.symm) he
    exact addresses_separate hw (h₁.symm.trans ((congrArg f eq).trans h₂))
  · intro he
    exact ⟨fun q => if q.2 = total w then phi w else phi (mirror w),
      if_pos rfl, if_neg (Ne.symm he)⟩

def completionFactor (w : ℂ) :=
  (ReflectedGaussianReading.scale : ℂ) ^ w * Complex.Gamma w

/-- Arithmetic input for the raw total. Keep both the reflection equation and
    the comparison of the gamma factors visible in the statement. -/
theorem magnitude_order_iff {w : ℂ}
    (reflection : completionFactor (mirror w) * total (mirror w) =
      conj (completionFactor w * total w))
    (left_pos : 0 < ‖completionFactor (mirror w)‖)
    (growth : ‖completionFactor (mirror w)‖ < ‖completionFactor w‖) :
    (‖total w‖ < ‖total (mirror w)‖ ↔ total w ≠ 0) ∧
    (total (mirror w) = 0 ↔ total w = 0) := by
  have eq := congrArg norm reflection
  simp only [norm_mul, Complex.norm_conj] at eq
  have mirror_zero : total (mirror w) = 0 ↔ total w = 0 := by
    have hl := ne_of_gt left_pos
    have hr := ne_of_gt (left_pos.trans growth)
    constructor
    · intro h
      rw [h, norm_zero, mul_zero] at eq
      exact norm_eq_zero.mp ((mul_eq_zero.mp eq.symm).resolve_left hr)
    · intro h
      rw [h, norm_zero, mul_zero] at eq
      exact norm_eq_zero.mp ((mul_eq_zero.mp eq).resolve_left hl)
  refine ⟨⟨fun lt h => ?_, fun hn => ?_⟩, mirror_zero⟩
  · simp [h, mirror_zero.mpr h] at lt
  · have ht := norm_pos_iff.mpr hn
    exact (mul_lt_mul_left left_pos).mp
      ((mul_lt_mul_of_pos_right growth ht).trans_eq eq.symm)

/-- Identify the launch input by comparing the measured j magnitude to the
    midpoint of the two candidate magnitudes. Also recover its original Φ. -/
def launch (w : ℂ) (q : ℂ × ℂ) : ℂ :=
  if ‖q.2‖ < (‖total w‖ + ‖total (mirror w)‖) / 2 then w else mirror w

theorem launch_and_address {u w : ℂ} (candidate : u = w ∨ u = mirror w)
    (order : ‖total w‖ < ‖total (mirror w)‖) :
    launch w (hidden u) = u ∧ phi (launch w (hidden u)) = phi u := by
  have lo : ‖total w‖ < (‖total w‖ + ‖total (mirror w)‖)/2 := by linarith
  have hi : ¬ ‖total (mirror w)‖ < (‖total w‖ + ‖total (mirror w)‖)/2 := by linarith
  rcases candidate with rfl | rfl <;> simp [launch, hidden, lo, hi]

end
end SuperZeta.HiddenQuarticQuaternion

#print axioms SuperZeta.HiddenQuarticQuaternion.observed_zero_iff
#print axioms SuperZeta.HiddenQuarticQuaternion.zero_at_address
#print axioms SuperZeta.HiddenQuarticQuaternion.address_decoder_iff
#print axioms SuperZeta.HiddenQuarticQuaternion.magnitude_order_iff
#print axioms SuperZeta.HiddenQuarticQuaternion.launch_and_address
