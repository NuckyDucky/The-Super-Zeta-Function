import SuperZeta.Quartet
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

namespace SuperZeta.QuarterLiftOrientation
open Complex Reciprocal
noncomputable section

/-- With the stage labels exchanged, the same recurrence uses the opposite logarithm. -/
theorem swap_step (L P Q : ℂ) :
    step (-L) (Q,P) = (step L (P,Q)).swap := by simp [step,Prod.swap]

theorem swapped_fixed {L P Q : ℂ} (h : step L (P,Q) = (P,Q)) :
    step (-L) (Q,P) = (Q,P) := by rw [swap_step,h]; rfl

/-- The ordered fixed pair distinguishes the output quotient from its reciprocal. -/
theorem output_ratio {L P Q : ℂ} (h : step L (P,Q) = (P,Q)) :
    Q/P = exp (-L*P-L*Q) := by
  obtain ⟨hp,hq⟩ := (fixed_iff _ _ _).mp h
  rw [Complex.exp_sub,←hp,←hq]

/-- Exchanging the ordered exponents negates the cosine coordinate. Squaring it
identifies the two orientations before taking any spectral power. -/
theorem swap_spectral_power (a s : ℂ) :
    Quartet.coordinate a⁻¹ = -Quartet.coordinate a ∧
    ((Quartet.coordinate a⁻¹)^2)^(-s) = ((Quartet.coordinate a)^2)^(-s) := by
  have hc : Quartet.coordinate a⁻¹ = -Quartet.coordinate a := by
    simp only [Quartet.coordinate, inv_inv]; ring
  exact ⟨hc, by rw [hc,neg_sq]⟩

end
end SuperZeta.QuarterLiftOrientation
