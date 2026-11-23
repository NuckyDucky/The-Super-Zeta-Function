import DottieLowerHorizontalBound
import DottieLowerRightBound
import DottieReferenceQuantitative
import ArchivedDottieRetainedBudget

/-! Assemble the three bounds for the exact smoothing difference. The same
unconditional absolute estimate applies to the original retained prefix
and to the lower omitted norms. -/

namespace QuarticModel

open Complex Finset
open scoped ComplexConjugate
open SuperZeta.StirlingCorrection
open private dottie_finite_sharp_side_eq_sum from DottieLowerContourData
open private dottieSharpSide from ArchivedDottieTailPartition
set_option autoImplicit false

theorem dottie_smoothing_side_uniform_absolute (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^13) {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieRangeSide S w-dottieFiniteSharpSide S w‖ ≤ 9/10^39 := by
  have ht : 21 < w.im := by linarith only [(abs_le.mp hi).1,dottieHeight_enclosure.1]
  rw [dottie_lower_side_eq_finite_contour S (by linarith only [hr.1]) ht
    (fun n hn => (hS n hn).1.ne')]
  let den : ℂ := 2*(Real.pi : ℂ)*(archivedDottieCompletionScale : ℂ)
  let L := dottieLeftSegment S w
  let A := dottieLowerHorizontalEdge S w (-20)
  let B := dottieLowerHorizontalEdge S w 20
  let R := dottieRightExterior S w
  have hL : ‖L/den‖ ≤ 6/10^39 := dottie_normalized_left_segment_bound S hS hr hi
  have hA : ‖A/den‖ ≤ 1/10^39 := dottie_normalized_lower_horizontal_bound S hS hr hi (by norm_num)
  have hB : ‖B/den‖ ≤ 1/10^39 := dottie_normalized_lower_horizontal_bound S hS hr hi (by norm_num)
  have hR : ‖R/den‖ ≤ 1/10^39 := dottie_normalized_right_exterior_bound S hS hr hi
  change ‖(L+I*(A-B)+R)/den‖ ≤ _
  rw [show (L+I*(A-B)+R)/den = L/den+I*(A/den-B/den)+R/den by ring]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [norm_mul, norm_I, one_mul]
  linarith only [hL,hA,hB,hR,norm_sub_le (A/den) (B/den)]

private theorem reflected_data {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    (1-conj w).re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048) ∧
      |(1-conj w).im-dottieHeight| ≤ 35/2048 := by
  refine ⟨?_,by simpa using hi⟩
  simp only [sub_re, one_re, conj_re]
  exact ⟨by linarith only [hr.2],by linarith only [hr.1]⟩

private theorem reflected_smoothing_absolute (S : Finset ℕ)
    (hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^13) {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖(dottieRangeSide S w - dottieFiniteSharpSide S w) +
      conj (dottieRangeSide S (1-conj w)-dottieFiniteSharpSide S (1-conj w))‖ ≤ 18/10^39 := by
  obtain ⟨hmr,hmi⟩ := reflected_data hr hi
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj]
  exact (add_le_add (dottie_smoothing_side_uniform_absolute S hS hr hi)
    (dottie_smoothing_side_uniform_absolute S hS hmr hmi)).trans (by norm_num)

theorem dottie_lower_omitted_smoothing_uniform_absolute {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieOmittedLowerSmoothingError w‖ ≤ 18/10^39 := by
  rw [dottie_lower_smoothing_eq_two_sides (by linarith only [hr.1]) (by linarith only [hr.2])]
  apply reflected_smoothing_absolute (Finset.Ioc dottiePrefixEnd dottieOmittedSharpEnd) ?_ hr hi
  intro n hn
  obtain ⟨h₀,h₁⟩ := Finset.mem_Ioc.mp hn
  exact ⟨(Nat.zero_le _).trans_lt h₀,h₁⟩

theorem dottie_retained_prefix_smoothing_uniform_absolute {w : ℂ}
    (hr : w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048))
    (hi : |w.im-dottieHeight| ≤ 35/2048) :
    ‖dottieSmoothedPrefix w-dottieSharpPrefix w‖ ≤ 18/10^39 := by
  let S := Finset.Ioc 0 dottiePrefixEnd
  have hS : ∀ n ∈ S, 0 < n ∧ n ≤ 10^13 := by
    intro n hn
    obtain ⟨h₀,h₁⟩ := Finset.mem_Ioc.mp hn
    exact ⟨h₀,h₁.trans (by decide +kernel)⟩
  have hn : ∀ n ∈ S, n ≠ 0 := fun n h => (hS n h).1.ne'
  have hz : 0 ∉ S := by simp [S]
  have hset : Finset.range (dottiePrefixEnd+1) = insert 0 S := by
    ext n
    simp only [S, Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  obtain ⟨hmr,_⟩ := reflected_data hr hi
  have hSmooth : dottieSmoothedPrefix w =
      dottieRangeSide S w + conj (dottieRangeSide S (1-conj w)) := by
    have hzero : dottieSmoothTerm w 0 = 0 := by simp [dottieSmoothTerm,dottieSmoothSide]
    rw [dottieSmoothedPrefix, hset, Finset.sum_insert hz, hzero, zero_add,
      dottie_range_side_eq_sum S (by linarith only [hr.1]) hn,
      dottie_range_side_eq_sum S (by linarith only [hmr.1]) hn, map_sum, ← Finset.sum_add_distrib]
    rfl
  have hSharp : dottieSharpPrefix w =
      dottieFiniteSharpSide S w + conj (dottieFiniteSharpSide S (1-conj w)) := by
    have hzero (v : ℂ) : dottieSharpSide v 0 = 0 := by simp [dottieSharpSide]
    rw [dottieSharpPrefix, hset, Finset.sum_insert hz]
    simp only [hzero,map_zero,zero_add]
    rw [dottie_finite_sharp_side_eq_sum S hn, dottie_finite_sharp_side_eq_sum S hn,
      map_sum, ← Finset.sum_add_distrib]
  rw [hSmooth,hSharp]
  have he (a b c d : ℂ) : (a+conj b)-(c+conj d) = (a-c)+conj (b-d) := by
    rw [map_sub]
    ring
  rw [he]
  exact reflected_smoothing_absolute S hS hr hi

theorem dottie_right_sphere_coordinate_bounds {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    w.re ∈ Set.Icc (1/2-63/2048) (1/2+63/2048) ∧ |w.im-dottieHeight| ≤ 35/2048 := by
  have hdist : ‖w-archivedRightCenter dottieHeight‖ = 31/2048 := by
    simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
  have hre := Complex.abs_re_le_norm (w-archivedRightCenter dottieHeight)
  have him := Complex.abs_im_le_norm (w-archivedRightCenter dottieHeight)
  rw [hdist, sub_re] at hre
  rw [hdist, sub_im] at him
  norm_num [archivedRightCenter] at hre him
  exact ⟨⟨by linarith only [(abs_le.mp hre).1], by linarith only [(abs_le.mp hre).2]⟩,
    abs_le.mpr ⟨by linarith only [(abs_le.mp him).1], by linarith only [(abs_le.mp him).2]⟩⟩

theorem dottie_lower_omitted_budget_of_candidate_equality
    (hscore : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 = dottiePairedCandidateTicks)
    {w : ℂ} (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖dottieOmittedLowerSmoothingError w‖ ≤ (1/1000)*((w.re-1/2)*dottieCircleReference) := by
  obtain ⟨hr,hi⟩ := dottie_right_sphere_coordinate_bounds hw
  have hs := dottieCircleReference_lower_of_candidate_equality hscore
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  refine (dottie_lower_omitted_smoothing_uniform_absolute hr hi).trans ?_
  have hh := mul_le_mul hx hs (by norm_num) (by linarith only [hx])
  nlinarith only [hh]

theorem dottie_retained_prefix_budget_of_candidate_equality
    (hscore : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 = dottiePairedCandidateTicks)
    {w : ℂ} (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖dottieSmoothedPrefix w-dottieSharpPrefix w‖ ≤ (1/100000000)*dottieCircleReference := by
  obtain ⟨hr,hi⟩ := dottie_right_sphere_coordinate_bounds hw
  have hs := dottieCircleReference_lower_of_candidate_equality hscore
  exact (dottie_retained_prefix_smoothing_uniform_absolute hr hi).trans (by linarith only [hs])

#print axioms dottie_smoothing_side_uniform_absolute
#print axioms dottie_lower_omitted_smoothing_uniform_absolute
#print axioms dottie_retained_prefix_smoothing_uniform_absolute
#print axioms dottie_right_sphere_coordinate_bounds
#print axioms dottie_lower_omitted_budget_of_candidate_equality
#print axioms dottie_retained_prefix_budget_of_candidate_equality

end QuarticModel
