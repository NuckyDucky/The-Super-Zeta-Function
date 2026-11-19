import SuperZeta.Oriented.TraceRecovery

noncomputable section
namespace DottieOriented.Rotation
open Complex TraceRecovery

/-- Applying a turn to the recorded unit direction. -/
def turn (δ : ℝ) (z : ℂ) := exp ((δ : ℂ)*I)*z

theorem undo (δ : ℝ) (z : ℂ) : turn (-δ) (turn δ z) = z := by
  simp only [turn, ofReal_neg, neg_mul, ← mul_assoc, ← exp_add, neg_add_cancel,
    exp_zero, one_mul]

theorem six_steps_meet :
    (turn (Real.pi/6) 1)^6 = -1 ∧ (turn (-(Real.pi/6)) 1)^6 = -1 := by
  have hp : (turn (Real.pi/6) 1)^6 = -1 := by
    simp only [turn,mul_one,← Complex.exp_nat_mul]
    convert Complex.exp_pi_mul_I using 2
    push_cast
    ring
  refine ⟨hp,?_⟩
  simp only [turn, ofReal_neg, neg_mul, Complex.exp_neg, mul_one, inv_pow]
  simp only [turn, mul_one] at hp
  rw [hp]; norm_num

/-- Squaring the spectral coordinate produces an exact global ambiguity, even
if both original sign channels are retained in order. -/
theorem reflected_determinant (σ φ : ℝ) (hσ : σ^2=1) (v : ℂ) :
    signedDet σ (Real.pi - φ) v = signedDet σ φ v := by
  obtain ⟨z,rfl⟩ : ∃ z : ℂ, z^2=v := ⟨_, Complex.cpow_nat_inv_pow v (n:=2) (by decide)⟩
  have hchar (w : ℂ) : signedCharacteristic σ (Real.pi-φ) w = -signedCharacteristic σ φ (-w) := by
    simp only [signedCharacteristic, ofReal_sub]
    rw [show w-((Real.pi:ℂ)-(φ:ℂ)) = w+(φ:ℂ)-(Real.pi:ℂ) by ring, Complex.cos_sub_pi,
      show -w-(φ:ℂ) = -(w+(φ:ℂ)) by ring, Complex.cos_neg]
    ring
  rw [signedDet_sq hσ, signedDet_sq hσ, hchar, hchar, neg_neg, Real.cos_pi_sub]
  push_cast
  ring

end DottieOriented.Rotation
