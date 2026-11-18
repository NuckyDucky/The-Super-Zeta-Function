import SuperZeta.Reciprocal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The two maps between the parabolic characteristic equation and the signed
cosine equations, including the ordered phase recovered from a cosine root. -/
namespace SuperZeta.Quartet
open Complex
noncomputable section

def characteristic (a : ℂ) : Prop := a^2 * exp (a-a⁻¹) = -1
def coordinate (a : ℂ) : ℂ := (a-a⁻¹)/(2*I)
def phase (b u : ℂ) : ℂ := b*I*exp (-(u*I))

theorem coordinate_mul (a : ℂ) : 2*(coordinate a*I) = a-a⁻¹ := by
  unfold coordinate
  field_simp
  ring

private theorem exp_double (z : ℂ) : exp (2*z) = (exp z)^2 := by
  rw [two_mul, exp_add, pow_two]

private theorem imaginary_square (z : ℂ) (hz : z^2 = -1) :
    z = I ∨ z = -I := by
  have hp : (z-I)*(z+I)=0 := by linear_combination hz - Complex.I_sq
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

theorem characteristic_sign {a : ℂ} (h : characteristic a) :
    ∃ b : ℂ, (b=1 ∨ b= -1) ∧ a*exp (coordinate a*I)=b*I := by
  unfold characteristic at h
  rw [← coordinate_mul a, exp_double] at h
  rw [← mul_pow] at h
  rcases imaginary_square _ h with h | h
  · exact ⟨1, Or.inl rfl, by simpa using h⟩
  · exact ⟨-1, Or.inr rfl, by simpa using h⟩

private theorem phase_inverse {b : ℂ} (hb : b=1 ∨ b= -1) (u : ℂ) :
    (phase b u)⁻¹ = -(b*I)*exp (u*I) := by
  rcases hb with rfl | rfl <;> simp [phase, Complex.exp_neg, mul_inv_rev, Complex.inv_I]
  <;> ring

theorem coordinate_phase {b : ℂ} (hb : b=1 ∨ b= -1) (u : ℂ) :
    coordinate (phase b u) = b*cos u := by
  unfold coordinate
  rw [phase_inverse hb]
  unfold phase Complex.cos
  rw [neg_mul]
  field_simp
  ring

theorem phase_recovers {a : ℂ} {b : ℂ}
    (hs : a*exp (coordinate a*I)=b*I) : phase b (coordinate a)=a := by
  unfold phase
  rw [← hs, exp_neg, mul_assoc, mul_inv_cancel₀ (exp_ne_zero _), mul_one]

/-- Every characteristic phase has a signed cosine root and its ordered inverse. -/
theorem to_signed_cosine {a : ℂ} (h : characteristic a) :
    ∃ b : ℂ, (b=1 ∨ b= -1) ∧ coordinate a = b*cos (coordinate a) ∧
      phase b (coordinate a) = a := by
  obtain ⟨b,hb,hs⟩ := characteristic_sign h
  have hr := phase_recovers hs
  exact ⟨b,hb,by simpa only [hr] using coordinate_phase hb (coordinate a),hr⟩

/-- A signed cosine root gives an actual multiplier-one characteristic phase. -/
theorem from_signed_cosine {b u : ℂ} (hb : b=1 ∨ b= -1) (hu : u=b*cos u) :
    coordinate (phase b u)=u ∧ characteristic (phase b u) := by
  have hcoord := (coordinate_phase hb u).trans hu.symm
  refine ⟨hcoord, ?_⟩
  unfold characteristic
  rw [← coordinate_mul, hcoord, exp_double, ← mul_pow]
  have he : phase b u * exp (u*I)=b*I := by
    unfold phase
    rw [exp_neg, mul_assoc, inv_mul_cancel₀ (exp_ne_zero _), mul_one]
  rw [he]
  rcases hb with rfl | rfl <;> simp

theorem determinant_root_iff (u : ℂ) :
    cos u ^ 2 - u ^ 2 = 0 ↔ ∃ a, characteristic a ∧ coordinate a = u := by
  constructor
  · intro h
    have hp : (u-cos u)*(u+cos u)=0 := by linear_combination -h
    rcases mul_eq_zero.mp hp with hp | hp
    · have he := from_signed_cosine (u:=u) (b:=1) (Or.inl rfl)
          (by simpa using sub_eq_zero.mp hp)
      exact ⟨_,he.2,he.1⟩
    · have he := from_signed_cosine (u:=u) (b:= -1) (Or.inr rfl)
          (by simpa using eq_neg_of_add_eq_zero_left hp)
      exact ⟨_,he.2,he.1⟩
  · rintro ⟨a,h,rfl⟩
    obtain ⟨b,hb,he,_⟩ := to_signed_cosine h
    rcases hb with rfl | rfl <;> simp at he
    all_goals nth_rw 2 [he]
    all_goals ring

/-- Recover both exponential phases and their actual lifted logarithms.
The original return at the first phase has multiplier one. -/
theorem recover_fixed_pair {a : ℂ} (ha : characteristic a) :
    let L := a / exp a⁻¹
    let p := (exp a, exp a⁻¹)
    Reciprocal.step L p = p ∧ Reciprocal.lifts L p = (a,a⁻¹) ∧
      deriv (Reciprocal.scalarReturn L) p.1 = 1 := by
  have hn : a ≠ 0 := by intro h; simp [h, characteristic] at ha
  unfold characteristic at ha
  rw [exp_sub] at ha
  have h₁ : a/exp a⁻¹ * exp a⁻¹ = a := div_mul_cancel₀ _ (exp_ne_zero _)
  have h₂ : -(a/exp a⁻¹) * exp a = a⁻¹ := by
    field_simp [hn, exp_ne_zero] at ha ⊢
    linear_combination -ha
  dsimp only
  have hf : Reciprocal.step (a / exp a⁻¹) (exp a, exp a⁻¹) = (exp a,exp a⁻¹) := by
    simp [Reciprocal.step, h₁, h₂]
  have hl : Reciprocal.lifts (a / exp a⁻¹) (exp a, exp a⁻¹) = (a,a⁻¹) := by
    simp [Reciprocal.lifts, h₁, h₂]
  refine ⟨hf, hl, ?_⟩
  simpa [hl, hn] using (Reciprocal.fixed_return_multiplier hf).2

end
end SuperZeta.Quartet
