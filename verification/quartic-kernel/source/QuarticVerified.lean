import QuarticCheckedShell
import QuarticCheckedCells
import QuarticSharpReading

namespace QuarticKernel

noncomputable def completedQuartic : ℂ → ℂ :=
  mellin (fun x : ℝ => (theta (x/scale) : ℂ))

theorem actual_quartic_certificate :
    GaussianSideSign.Certificate completedQuartic kernel :=
  checkCoreCells_sound actual_cells_pass actual_bin_count actual_checked_shells.2.1
    actual_checked_shells.2.2 actual_checked_shells.1

theorem verified_quartic_direction {a t : ℝ} (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) :
    (completedQuartic (GaussianSideSign.point a t)).im =
      a*t*GaussianSideIntegral.slope kernel a t ∧ 400000 < GaussianSideIntegral.slope kernel a t :=
  sharp_quantitative_reading actual_quartic_certificate ha ht

theorem verified_quartic_zero_on_line {a t : ℝ} (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100)
    (hz : completedQuartic (GaussianSideSign.point a t) = 0) :
    (GaussianSideSign.point a t).re = 1/2 :=
  GaussianSideSign.zero_requires_line_whole_rectangle actual_quartic_certificate ha ht hz

#print axioms actual_quartic_certificate
#check @verified_quartic_direction
#print axioms verified_quartic_direction
#check @verified_quartic_zero_on_line
#print axioms verified_quartic_zero_on_line

end QuarticKernel
