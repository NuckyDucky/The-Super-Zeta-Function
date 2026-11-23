import QuarticMellinFold
import QuarticGridTail

open MeasureTheory Set

namespace QuarticKernel

/-- The two concrete inputs still needed for the Mellin certificate. The
function here is the full Mellin transform, with its right-half-plane
identification proved independently by `rightMellin`. -/
theorem assemble_mellin_from_reflection_and_cells
    (reflection : ∀ t : ℝ, 0 < t → theta (t/scale) = t⁻¹ * theta (t⁻¹/scale))
    (cells : ∀ j < 1116, ∀ x ∈ Icc (QuarticGrid.node j : ℝ) (QuarticGrid.node (j+1) : ℝ),
      (QuarticGrid.lowerK j : ℝ) ≤ kernel x ∧ kernel x ≤ (QuarticGrid.upperK j : ℝ)) :
    GaussianSideSign.Certificate (mellin (fun x : ℝ => (theta (x/scale) : ℂ))) kernel := by
  apply QuarticGrid.assemble_from_grid _ _ cells
  intro a t ha _
  exact mellin_fold_in_rectangle (theta_reflection_iff_kernel_even.mp reflection) a t ha

#check @assemble_mellin_from_reflection_and_cells
#print axioms assemble_mellin_from_reflection_and_cells

end QuarticKernel
