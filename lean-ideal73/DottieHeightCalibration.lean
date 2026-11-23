import ArchivedDottieHeight
import ArchivedQuarticZeroTransport
import Mathlib.Topology.Order.IntermediateValue

/-! The height calibration of the archived cap-selected return, allowing the
horizontal witness displacement to vary. The cap capture and winding are
dynamical inputs to this calibration. -/

namespace SuperZeta.StirlingCorrection

open Real Set
noncomputable section

abbrev archivedDottieFlank : ℝ := 0.00000004749479070945369
abbrev archivedDottieMidIm : ℝ := 0.509892982511772
abbrev archivedDottieFlankSlack : ℝ := 0.0000000000000000000014

def dottieFlankRatio (x : ℝ) : ℝ := (x / archivedDottieMidIm)^2

/-- The one-winding height for 320 occurrences of one marked arrow. -/
def dottieHeightAtFlank (x : ℝ) : ℝ := 2*π / (160 * log (1 + dottieFlankRatio x))

theorem dottie_height_at_archived_flank :
    dottieHeightAtFlank archivedDottieFlank = dottieHeight := rfl

private theorem flank_denominator_pos {x : ℝ} (hx : 0 < x) :
    0 < 160 * log (1 + dottieFlankRatio x) := by
  have hr : 0 < dottieFlankRatio x := by unfold dottieFlankRatio; positivity
  exact mul_pos (by norm_num) (log_pos (by linarith))

private theorem flank_height_continuousOn {a b : ℝ} (ha : 0 < a) :
    ContinuousOn dottieHeightAtFlank (Icc a b) := by
  have harg : Continuous (fun x : ℝ => 1 + dottieFlankRatio x) := by
    unfold dottieFlankRatio
    fun_prop
  intro x hx
  have harg_ne : 1 + dottieFlankRatio x ≠ 0 := by
    unfold dottieFlankRatio
    positivity
  have hlog : ContinuousAt (fun z : ℝ => log (1 + dottieFlankRatio z)) x :=
    ContinuousAt.comp (f := fun z : ℝ => 1 + dottieFlankRatio z)
      (continuousAt_log harg_ne) harg.continuousAt
  exact (continuousAt_const.div (continuousAt_const.mul hlog)
    (flank_denominator_pos (ha.trans_le hx.1)).ne').continuousWithinAt

private theorem log_one_add_bounds {r : ℝ} (hr : 0 ≤ r) (hr' : r < 1) :
    r - r^2/2 - r^3/(1-r) ≤ log (1+r) ∧
    log (1+r) ≤ r - r^2/2 + r^3/(1-r) := by
  have hsmall : |-r| < 1 := by simpa [abs_of_nonneg hr] using hr'
  have h := abs_log_sub_add_sum_range_le hsmall 2
  have hsum : (∑ i ∈ Finset.range 2, (-r)^(i+1)/(i+1)) = -(r-r^2/2) := by
    norm_num [Finset.sum_range_succ]
    ring
  rw [hsum, abs_neg, abs_of_nonneg hr, sub_neg_eq_add, neg_add_eq_sub] at h
  obtain ⟨hlo,hhi⟩ := abs_le.mp h
  exact ⟨by linarith, by linarith⟩

theorem dottie_flank_height_endpoints :
    dottieHeightAtFlank (archivedDottieFlank + archivedDottieFlankSlack) < dottieHeight - 1/4 ∧
    dottieHeight + 1/4 < dottieHeightAtFlank (archivedDottieFlank - archivedDottieFlankSlack) := by
  let a := archivedDottieFlank - archivedDottieFlankSlack
  let b := archivedDottieFlank + archivedDottieFlankSlack
  obtain ⟨hTlo,hThi⟩ := dottieHeight_enclosure
  have hblo := (log_one_add_bounds (r := dottieFlankRatio b) (sq_nonneg _)
    (by norm_num [dottieFlankRatio,b])).1
  have hahi := (log_one_add_bounds (r := dottieFlankRatio a) (sq_nonneg _)
    (by norm_num [dottieFlankRatio,a])).2
  change dottieHeightAtFlank b < dottieHeight - 1/4 ∧
    dottieHeight + 1/4 < dottieHeightAtFlank a
  constructor
  · suffices h : dottieHeightAtFlank b < 4526119322477.695393315398 by linarith
    unfold dottieHeightAtFlank
    apply (div_lt_iff₀ (flank_denominator_pos (x := b) (by norm_num [b]))).2
    calc
      _ < 2 * 3.14159265358979323847 := by linarith [Real.pi_lt_d20]
      _ < 4526119322477.695393315398 * (160 *
        (dottieFlankRatio b - (dottieFlankRatio b)^2/2 -
          (dottieFlankRatio b)^3/(1-dottieFlankRatio b))) := by norm_num [dottieFlankRatio,b]
      _ ≤ _ := by gcongr
  · suffices h : 4526119322478.195393329807 < dottieHeightAtFlank a by linarith
    unfold dottieHeightAtFlank
    apply (lt_div_iff₀ (flank_denominator_pos (x := a) (by norm_num [a]))).2
    calc
      _ ≤ 4526119322478.195393329807 * (160 *
        (dottieFlankRatio a - (dottieFlankRatio a)^2/2 +
          (dottieFlankRatio a)^3/(1-dottieFlankRatio a))) := by gcongr
      _ < 2 * 3.14159265358979323846 := by norm_num [dottieFlankRatio,a]
      _ < _ := by linarith [Real.pi_gt_d20]

/-- A displacement in the indicated band gives any prescribed height in the
original half-unit spectral window, for the archived one-winding calibration. -/
theorem dottie_flank_reaches_archived_window {T : ℝ}
    (hT : T ∈ Icc (dottieHeight - 1/4) (dottieHeight + 1/4)) :
    ∃ x ∈ Icc (archivedDottieFlank - archivedDottieFlankSlack)
        (archivedDottieFlank + archivedDottieFlankSlack), dottieHeightAtFlank x = T := by
  obtain ⟨hlo,hhi⟩ := dottie_flank_height_endpoints
  apply intermediate_value_Icc' (f := dottieHeightAtFlank) (by norm_num)
    (flank_height_continuousOn (by norm_num))
  exact ⟨hlo.le.trans hT.1,hT.2.trans hhi.le⟩

/-- Points in this rectangle lie in a right disk whose reference height comes
from the same flank interval. This is a geometric coverage statement. -/
theorem dottie_flank_covers_right_rectangle {w : ℂ}
    (hre : w.re ∈ Icc (1/2 + 1/2048) (1/2 + 63/2048))
    (him : w.im + 1/512 ∈ Icc (dottieHeight - 1/4) (dottieHeight + 1/4)) :
    ∃ x ∈ Icc (archivedDottieFlank - archivedDottieFlankSlack)
        (archivedDottieFlank + archivedDottieFlankSlack),
      dottieHeightAtFlank x = w.im + 1/512 ∧
      w ∈ Metric.closedBall (QuarticModel.archivedRightCenter (dottieHeightAtFlank x)) (31/2048) := by
  obtain ⟨x,hx,he⟩ := dottie_flank_reaches_archived_window him
  refine ⟨x,hx,he,?_⟩
  rw [he, Metric.mem_closedBall, dist_eq_norm]
  have hd : w - QuarticModel.archivedRightCenter (w.im + 1/512) =
      ((w.re - 33/64 : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · change w.im - (w.im + 1/512 - 1/512) = 0
      ring
  rw [hd, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hre.1],by linarith [hre.2]⟩

#print axioms dottie_height_at_archived_flank
#print axioms dottie_flank_height_endpoints
#print axioms dottie_flank_reaches_archived_window
#print axioms dottie_flank_covers_right_rectangle

end
end SuperZeta.StirlingCorrection
