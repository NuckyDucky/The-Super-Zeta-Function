import QuarticCheckedShellKernel
import QuarticCheckedCellsKernel
import QuarticSharpReading

namespace QuarticKernel

set_option maxRecDepth 24000

noncomputable def completedQuarticKernel : ℂ → ℂ :=
  mellin (fun x : ℝ => (theta (x/scale) : ℂ))

theorem actual_quartic_certificate_kernel :
    GaussianSideSign.Certificate completedQuarticKernel kernel :=
  checkCoreCells_sound actual_cells_kernel (by decide : binCount actualBins = 33554431)
    actual_checked_shells_kernel.2.1 actual_checked_shells_kernel.2.2
    actual_checked_shells_kernel.1

theorem verified_quartic_direction_kernel {a t : ℝ} (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) :
    (completedQuarticKernel (GaussianSideSign.point a t)).im =
      a*t*GaussianSideIntegral.slope kernel a t ∧ 400000 < GaussianSideIntegral.slope kernel a t :=
  sharp_quantitative_reading actual_quartic_certificate_kernel ha ht

theorem verified_quartic_zero_on_line_kernel {a t : ℝ} (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100)
    (hz : completedQuarticKernel (GaussianSideSign.point a t) = 0) :
    (GaussianSideSign.point a t).re = 1/2 :=
  GaussianSideSign.zero_requires_line_whole_rectangle actual_quartic_certificate_kernel ha ht hz

#print axioms actual_quartic_certificate_kernel
#print axioms verified_quartic_direction_kernel
#print axioms verified_quartic_zero_on_line_kernel

end QuarticKernel
