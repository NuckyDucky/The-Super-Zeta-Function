import QuarticThetaNormalize
import QuarticMellinCertificate
import QuarticOuterCells

open MeasureTheory Set

namespace QuarticKernel

set_option maxRecDepth 20000 in
private theorem first_grid_floor : 0 < (QuarticGrid.lowerK 0 : ℝ) := by
  have h : QuarticGrid.data[0]?.getD (0,0) = (2101203285,2236894332) := by decide
  rw [QuarticGrid.lowerK, h]
  norm_num

/-- For this quartic the grid also fixes the sign in the theta transformation.
The only input here is the bound on each of the remaining core cells. -/
theorem assemble_mellin_from_cells
    (cells : ∀ j < 1051, ∀ x ∈ Icc (QuarticGrid.node j : ℝ) (QuarticGrid.node (j+1) : ℝ),
      (QuarticGrid.lowerK j : ℝ) ≤ kernel x ∧ kernel x ≤ (QuarticGrid.upperK j : ℝ)) :
    GaussianSideSign.Certificate (mellin (fun x : ℝ => (theta (x/scale) : ℂ))) kernel := by
  have h0 : (0:ℝ) ∈ Icc (QuarticGrid.node 0 : ℝ) (QuarticGrid.node (0+1) : ℝ) := by
    norm_num [QuarticGrid.node]
  have hK := first_grid_floor.trans_le (cells 0 (by decide) 0 h0).1
  have hθ : 0 < theta (1/scale) := by
    simpa [kernel] using hK
  apply assemble_mellin_from_reflection_and_cells (theta_reflection_of_center_nonzero hθ.ne')
  intro j hj x hx
  by_cases h : j < 1051
  · exact cells j h x hx
  · exact QuarticGrid.encloses_outer_core j (le_of_not_gt h) hj x hx

#check @assemble_mellin_from_cells
#print axioms assemble_mellin_from_cells

end QuarticKernel
