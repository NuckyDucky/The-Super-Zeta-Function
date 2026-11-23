import QuarticVerifiedKernel

namespace QuarticUseCheck

open QuarticKernel SuperZeta

theorem right_reading :
    1000 < (completedQuarticKernel (GaussianSideSign.point (1 / 100) (1 / 4))).im := by
  obtain ⟨hIm, hSlope⟩ :=
    verified_quartic_direction_kernel (a := 1 / 100) (t := 1 / 4)
      (by norm_num [abs_le]) (by norm_num [abs_le])
  rw [hIm]
  linarith only [hSlope]

theorem left_reading :
    (completedQuarticKernel (GaussianSideSign.point (-1 / 100) (1 / 4))).im < -1000 := by
  obtain ⟨hIm, hSlope⟩ :=
    verified_quartic_direction_kernel (a := -1 / 100) (t := 1 / 4)
      (by norm_num [abs_le]) (by norm_num [abs_le])
  rw [hIm]
  linarith only [hSlope]

theorem center_reading :
    (completedQuarticKernel (GaussianSideSign.point 0 (1 / 4))).im = 0 := by
  rw [(verified_quartic_direction_kernel (a := 0) (t := 1 / 4)
    (by norm_num) (by norm_num [abs_le])).1]
  simp

theorem opposite_readings :
    (completedQuarticKernel (GaussianSideSign.point (-1 / 100) (1 / 4))).im =
      -(completedQuarticKernel (GaussianSideSign.point (1 / 100) (1 / 4))).im := by
  have sinhc_neg (x : ℝ) : GaussianSideIntegral.sinhc (-x) =
      GaussianSideIntegral.sinhc x := by
    simp [GaussianSideIntegral.sinhc, Real.sinh_neg]
  have slope_eq (a t : ℝ) : GaussianSideIntegral.slope kernel (-a) t =
      GaussianSideIntegral.slope kernel a t := by
    simp only [GaussianSideIntegral.slope, neg_mul, sinhc_neg]
  rw [(verified_quartic_direction_kernel (a := -1 / 100)
      (t := 1 / 4) (by norm_num [abs_le]) (by norm_num [abs_le])).1,
    (verified_quartic_direction_kernel (a := 1 / 100)
      (t := 1 / 4) (by norm_num [abs_le]) (by norm_num [abs_le])).1,
    show (-1 : ℝ) / 100 = -(1 / 100) by ring, slope_eq]
  ring

#print axioms right_reading
#print axioms left_reading
#print axioms center_reading
#print axioms opposite_readings

end QuarticUseCheck
