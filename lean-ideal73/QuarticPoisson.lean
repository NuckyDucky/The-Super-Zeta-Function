import QuarticPrimitive
import QuarticDualArithmetic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

namespace QuarticFiniteFourier

set_option maxHeartbeats 1000000 in
theorem character_expansion (a b : ℤ) :
    gaussAmplitude * (QuarticDualArithmetic.conductorReading a b : ℂ) =
      ∑ h : ZMod D, signValue h * ZMod.stdAddChar (h*((a:ZMod D)+(R:ZMod D)*(b:ZMod D))) := by
  let k := (a : ZMod D) + (R : ZMod D) * (b : ZMod D)
  have hG := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar quarticCharacter_primitive k
  rw [quarticCharacter_quadratic.inv] at hG
  simp only [gaussSum, AddChar.mulShift_apply] at hG
  have hS : (quarticCharacter k : ℂ) =
      (QuarticDualArithmetic.conductorReading a b : ℂ) := by
    change signValue ((a:ZMod D)+(R:ZMod D)*(b:ZMod D)) = _
    rw [sign_at_integer_point]
    unfold QuarticDualArithmetic.conductorReading QuarticModel.archivedGaussianSign
    ring_nf
  calc
    _ = quarticCharacter k * gaussAmplitude := by rw [hS, mul_comm]
    _ = ∑ h : ZMod D, quarticCharacter h * ZMod.stdAddChar (h*k) := by
      simpa only [gaussAmplitude, gaussSum, mul_comm k] using hG.symm
    _ = _ := rfl

/-- One coordinate of the rationally twisted Gaussian. The result retains
the additive shift of its Fourier frequencies. -/
theorem twisted_gaussian (A y : ℝ) (hA : 0 < A) :
    (∑' n : ℤ, Complex.exp (-Real.pi*(A:ℂ)*(n:ℂ)^2+
      2*Real.pi*Complex.I*(y:ℂ)*(n:ℂ))) =
      (1 / (A:ℂ)^(1/2:ℂ)) *
        ∑' n : ℤ, Complex.exp (-Real.pi/(A:ℂ)*((n:ℂ)-(y:ℂ))^2) := by
  have hy : Complex.I * (Complex.I * (y : ℂ)) = -(y : ℂ) := by
    rw [← mul_assoc, ← pow_two, Complex.I_sq, neg_one_mul]
  simpa only [← mul_assoc, ← hy, sub_eq_add_neg] using
    Complex.tsum_exp_neg_quadratic (a := (A:ℂ)) (by simpa using hA) (Complex.I*(y:ℂ))

#print axioms character_expansion
#print axioms twisted_gaussian

end QuarticFiniteFourier
