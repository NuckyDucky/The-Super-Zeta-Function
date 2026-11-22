import QuarticThetaNormalize
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace QuarticMurphyBridge
open QuarticFiniteFourier QuarticKernel

/-- The exact type of Murphy's `DBN.Gen.rootNumber_eq_one_of_real_primitive`. -/
def RealPrimitiveRootNumberOne : Prop :=
  ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    (∀ n : ℕ, (χ n).im = 0) → χ.rootNumber = 1

theorem character_real (n : ℕ) : (quarticCharacter n).im = 0 := by
  change ((jacobiSym ((n : ZMod D).val : ℤ) D : ℂ)).im = 0
  simp

/-- The arithmetic inputs to the external theorem are both proved for this character. -/
theorem root_number (murphy : RealPrimitiveRootNumberOne) : quarticCharacter.rootNumber = 1 :=
  murphy quarticCharacter quarticCharacter_primitive character_real

theorem amplitude (h : quarticCharacter.rootNumber = 1) :
    gaussAmplitude = (Real.sqrt D : ℂ) := by
  have hE : quarticCharacter.Even := quarticCharacter_at_neg_one
  have hs : (D : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt D : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg D)]
    push_cast
    rfl
  have hn : (Real.sqrt D : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by positivity : 0 < (D : ℝ))).ne'
  unfold DirichletCharacter.rootNumber at h
  rw [if_pos hE, pow_zero, div_one, hs, div_eq_iff hn, one_mul] at h
  exact h

theorem theta_reflection (hs : gaussAmplitude = (Real.sqrt D : ℂ))
    {t : ℝ} (ht : 0 < t) :
    theta (t / scale) = t⁻¹ * theta (t⁻¹ / scale) := by
  have hp : 0 < Real.sqrt (D : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hsq : Real.sqrt (D : ℝ)^2 = (D : ℝ) := Real.sq_sqrt (by positivity)
  have hd : 1 / ((D : ℝ) * (t / Real.sqrt D)) = t⁻¹ / Real.sqrt D := by
    field_simp [ht.ne', hp.ne']
    change Real.sqrt (D : ℝ) * (t * Real.sqrt (D : ℝ)) = (D : ℝ) * t
    rw [mul_left_comm, ← pow_two, hsq, mul_comm]
  have sc (u : ℝ) : Real.pi * (u / Real.sqrt D) = u / scale := by
    change Real.pi * (u / Real.sqrt (D : ℝ)) = u / (Real.sqrt (D : ℝ) / Real.pi)
    rw [div_div_eq_mul_div]
    ring
  have ha := gaussian_lattice_transform (div_pos ht hp)
  rw [hs, hd, gaussianLattice_theta (div_pos ht hp),
    gaussianLattice_theta (div_pos (inv_pos.mpr ht) hp), sc, sc] at ha
  have h' : Real.sqrt (D : ℝ) * (4 * theta (t / scale)) =
      (t / Real.sqrt D)⁻¹ * (4 * theta (t⁻¹ / scale)) := by exact_mod_cast ha
  rw [inv_div, div_eq_mul_inv (Real.sqrt (D : ℝ)) t] at h'
  apply mul_left_cancel₀ (show (4 : ℝ) * Real.sqrt D ≠ 0 by positivity)
  linear_combination h'

theorem reflection_of_murphy (murphy : RealPrimitiveRootNumberOne) {t : ℝ} (ht : 0 < t) :
    theta (t / scale) = t⁻¹ * theta (t⁻¹ / scale) :=
  theta_reflection (amplitude (root_number murphy)) ht

#print axioms reflection_of_murphy
end QuarticMurphyBridge
