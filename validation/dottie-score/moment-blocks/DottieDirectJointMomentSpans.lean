import DottieDirectJointMomentRows
import DottieJointSharpCircle

namespace QuarticModel.DottieFixedIntervals

open SuperZeta.StirlingCorrection

set_option autoImplicit false

theorem dottie_direct_joint_moment_row_length (width N a : ℕ) :
    (dottieDirectJointMomentRow width N a).length = width := by
  simp only [dottieDirectJointMomentRow, dottieMomentTicksAdd, List.length_zipWith,
    dottie_joint_moment_row_head_length, (dottie_direct_joint_moment_block_agrees _ _ _ _).1,
    min_self]

/-- Sum a contiguous span of the direct row evaluations. -/
def dottieDirectJointMomentSpan (width N lo len : ℕ) : List (ℤ × ℤ) :=
  (List.range len).foldl (fun total j =>
    dottieMomentTicksAdd total (dottieDirectJointMomentRow width N (lo+j)))
    (List.replicate width (0,0))

private theorem directMomentSpan_succ (width N lo len : ℕ) :
    dottieDirectJointMomentSpan width N lo (len+1) =
      dottieMomentTicksAdd (dottieDirectJointMomentSpan width N lo len)
        (dottieDirectJointMomentRow width N (lo+len)) := by
  simp only [dottieDirectJointMomentSpan, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem dottie_direct_joint_moment_span_agrees (width N lo len : ℕ) :
    (dottieDirectJointMomentSpan width N lo len).length = width ∧
      ∀ k < width, (dottieDirectJointMomentSpan width N lo len).getD k (0,0) =
        (dottiePairedRowSpan N (fun n => momentWeightRealTicks n k) lo len,
         dottiePairedRowSpan N (fun n => momentWeightImagTicks n k) lo len) := by
  induction len with
  | zero =>
    refine ⟨List.length_replicate, fun k hk => ?_⟩
    simp only [dottieDirectJointMomentSpan, List.range_zero, List.foldl_nil,
      dottiePairedRowSpan]
    exact List.getD_replicate ((0,0) : ℤ × ℤ) hk
  | succ len ih =>
    rw [directMomentSpan_succ]
    have hRight := dottie_direct_joint_moment_row_length width N (lo+len)
    refine ⟨?_, fun k hk => ?_⟩
    · simp only [dottieMomentTicksAdd, List.length_zipWith, ih.1, hRight, min_self]
    · have hkl : k < (dottieDirectJointMomentSpan width N lo len).length := by
        simpa only [ih.1] using hk
      have hkr : k < (dottieDirectJointMomentRow width N (lo+len)).length := by
        simpa only [hRight] using hk
      exact dottie_joint_moment_span_add N lo len 1 _ _ hkl hkr (ih.2 k hk)
        (dottie_direct_joint_moment_row_getD width N (lo+len) hk)

/-- The direct full-prefix candidate can enter the original circle proof once its value is checked. -/
theorem dottie_sharp_margin_of_direct_span (ticks : List (ℤ × ℤ))
    (hValue : dottieDirectJointMomentSpan 11 dottiePrefixEnd 0 dottiePrefixEnd.sqrt = ticks)
    (hFit : dottieSharpScoresFit ticks = true)
    (hReference : dottieRelativeReferenceProjection ≤ 171687/10^6) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.37*((w.re-1/2)*dottieCircleReference)) := by
  apply dottie_sharp_margin_of_joint_scores ticks _ hFit hReference
  intro k
  have h := (dottie_direct_joint_moment_span_agrees 11 dottiePrefixEnd 0 dottiePrefixEnd.sqrt).2
    k k.isLt
  rw [hValue] at h
  exact ⟨(congrArg Prod.fst h).symm, (congrArg Prod.snd h).symm⟩

#print axioms dottie_direct_joint_moment_span_agrees
#print axioms dottie_sharp_margin_of_direct_span

end QuarticModel.DottieFixedIntervals
