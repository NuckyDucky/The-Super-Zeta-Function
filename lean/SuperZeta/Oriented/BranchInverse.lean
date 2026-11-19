import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

noncomputable section
namespace DottieOriented.Branch
open Set

/-- From the hypotheses certified on the physical interval: an angle in the
endpoint range identifies one and only one height, including its marked state
when a cap root has been selected. No inverse function is postulated. -/
theorem unique_parameter {a b t : ℝ} (hab : a ≤ b) (θ : ℝ → ℝ)
    (hc : ContinuousOn θ (Icc a b))
    (hs : ∀ x ∈ Ioo a b, 0 < deriv θ x)
    (ht : t ∈ Icc (θ a) (θ b)) :
    ∃! y, y ∈ Icc a b ∧ θ y = t := by
  have hmono := strictMonoOn_of_deriv_pos (convex_Icc a b) hc
    (by simpa only [interior_Icc] using hs)
  obtain ⟨y,hy,he⟩ := intermediate_value_Icc hab hc ht
  refine ⟨y, ⟨hy,he⟩, ?_⟩
  rintro z ⟨hz,hz'⟩
  exact hmono.injOn hz hy (hz'.trans he.symm)

/-- Apply the branch theorem to a turn and its inverse, with the intermediate
state quantified rather than supplied as an inverse function. -/
theorem return_angle_round_trip {a b y δ : ℝ} (hab : a ≤ b) (θ : ℝ → ℝ)
    (hc : ContinuousOn θ (Icc a b))
    (hs : ∀ x ∈ Ioo a b, 0 < deriv θ x)
    (hy : y ∈ Icc a b) (target : θ y - δ ∈ Icc (θ a) (θ b)) :
    ∃! z, (z ∈ Icc a b ∧ θ z = θ y - δ) ∧
       ∀ k ∈ Icc a b, θ k = θ z + δ → k = y := by
  obtain ⟨z,⟨hz,he⟩,hu⟩ := unique_parameter hab θ hc hs target
  have hm := strictMonoOn_of_deriv_pos (convex_Icc a b) hc
    (by simpa only [interior_Icc] using hs)
  exact ⟨z, ⟨⟨hz,he⟩,fun k hk h => hm.injOn hk hy (by linarith)⟩,fun k h => hu k h.1⟩

/-- Exact endpoint arithmetic of the separate FLINT two-probe replay. These
are its reported rational endpoints, not a Lean evaluation of the orbit. -/
theorem printed_return_interval :
    let a : ℚ := 940586535337511818345564356157 / 1844674407370955161600000000000
    let b : ℚ := 376234614135004727338225742467 / 737869762948382064640000000000
    let y : ℚ := 127473245627943 / 250000000000000
    a < y ∧ y < b ∧ b-a < 1/10^29 := by norm_num

end DottieOriented.Branch
