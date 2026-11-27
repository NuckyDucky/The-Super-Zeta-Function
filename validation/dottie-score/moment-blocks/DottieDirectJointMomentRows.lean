import DottieFastSharpWeights
import DottieJointMomentRows

/-! Joint sharp scores with the checked Gaussian character evaluated directly. -/

namespace QuarticModel.DottieFixedIntervals

open private fastAdd from DottieFastSharpWeights
open private addMomentPair addMomentPair_length addMomentPair_getD from DottieJointMomentScore
open private pairTermWithSign from DottieStructuralPairBlocks

set_option autoImplicit false
set_option maxHeartbeats 1000000

private def addLookupPair (width a lo : ℕ) (total : List (ℤ × ℤ)) (offset : ℕ) :
    List (ℤ × ℤ) :=
  let b := lo + offset
  let sign := dottieLookupRowSign ((a:ℤ)+1) ((b:ℤ)+1) +
    dottieLookupRowSign ((b:ℤ)+1) ((a:ℤ)+1)
  fastAdd sign ((a+1)^2+(b+1)^2) width total

private theorem fastAdd_eq (s : ℤ) (n width : ℕ) (total : List (ℤ × ℤ)) :
    fastAdd s n width total = addMomentPair s n width total := by
  simp only [fastAdd, addMomentPair, dottie_fast_joint_moment_weight_eq]

private theorem addLookupPair_length (width a lo offset : ℕ) (total : List (ℤ × ℤ))
    (hTotal : total.length = width) :
    (addLookupPair width a lo total offset).length = width := by
  unfold addLookupPair
  rw [fastAdd_eq]
  exact addMomentPair_length _ _ _ _ hTotal

private theorem addLookupPair_getD (width a lo offset : ℕ) (total : List (ℤ × ℤ))
    (hTotal : total.length = width) {k : ℕ} (hk : k < width) :
    (addLookupPair width a lo total offset).getD k (0,0) =
      ((total.getD k (0,0)).1 +
        pairTermWithSign dottieLookupRowSign (fun n => momentWeightRealTicks n k) a (lo+offset),
       (total.getD k (0,0)).2 +
        pairTermWithSign dottieLookupRowSign (fun n => momentWeightImagTicks n k) a (lo+offset)) := by
  unfold addLookupPair
  rw [fastAdd_eq, addMomentPair_getD _ _ _ _ hTotal hk]
  rfl

private theorem lookupFold_agrees (width a lo : ℕ) (offsets : List ℕ) (total : List (ℤ × ℤ))
    (hTotal : total.length = width) :
    (offsets.foldl (addLookupPair width a lo) total).length = width ∧
      ∀ k < width, (offsets.foldl (addLookupPair width a lo) total).getD k (0,0) =
        (offsets.foldl (fun acc j => acc +
            pairTermWithSign dottieLookupRowSign (fun n => momentWeightRealTicks n k) a (lo+j))
            (total.getD k (0,0)).1,
         offsets.foldl (fun acc j => acc +
            pairTermWithSign dottieLookupRowSign (fun n => momentWeightImagTicks n k) a (lo+j))
            (total.getD k (0,0)).2) := by
  induction offsets generalizing total with
  | nil => exact ⟨hTotal, fun _ _ => rfl⟩
  | cons j offsets ih =>
    have hNext := addLookupPair_length width a lo j total hTotal
    have h := ih (addLookupPair width a lo total j) hNext
    refine ⟨h.1, fun k hk => ?_⟩
    simpa only [List.foldl_cons, addLookupPair_getD _ _ _ _ _ hTotal hk] using h.2 k hk

/-- Compute the eleven complex subtotals without preparing a packed sign witness. -/
def dottieDirectJointMomentBlock (width a lo len : ℕ) : List (ℤ × ℤ) :=
  (List.range len).foldl (addLookupPair width a lo) (List.replicate width (0,0))

theorem dottie_direct_joint_moment_block_agrees (width a lo len : ℕ) :
    (dottieDirectJointMomentBlock width a lo len).length = width ∧
      ∀ k < width, (dottieDirectJointMomentBlock width a lo len).getD k (0,0) =
        (dottiePairRowBlock (fun n => momentWeightRealTicks n k) a lo len,
         dottiePairRowBlock (fun n => momentWeightImagTicks n k) a lo len) := by
  have h := lookupFold_agrees width a lo (List.range len) (List.replicate width (0,0))
    List.length_replicate
  refine ⟨h.1, fun k hk => ?_⟩
  have hZero : (List.replicate width ((0,0) : ℤ × ℤ)).getD k (0,0) = (0,0) :=
    List.getD_replicate (0,0) hk
  have hK := h.2 k hk
  rw [hZero] at hK
  change (dottieDirectJointMomentBlock width a lo len).getD k (0,0) =
    (dottiePairRowBlockWithSign dottieLookupRowSign (fun n => momentWeightRealTicks n k) a lo len,
     dottiePairRowBlockWithSign dottieLookupRowSign (fun n => momentWeightImagTicks n k) a lo len) at hK
  simpa only [dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq] using hK

/-- Compute the complete row, including its axis and any diagonal. -/
def dottieDirectJointMomentRow (width N a : ℕ) : List (ℤ × ℤ) :=
  dottieMomentTicksAdd (dottieJointMomentRowHead width N a)
    (dottieDirectJointMomentBlock width a 0 (dottiePairRowSize N a))

theorem dottie_direct_joint_moment_row_getD (width N a : ℕ) {k : ℕ} (hk : k < width) :
    (dottieDirectJointMomentRow width N a).getD k (0,0) =
      (dottiePairedRowSpan N (fun n => momentWeightRealTicks n k) a 1,
       dottiePairedRowSpan N (fun n => momentWeightImagTicks n k) a 1) := by
  have h := dottie_direct_joint_moment_block_agrees width a 0 (dottiePairRowSize N a)
  exact dottie_joint_moment_row_getD width N a _ h.1 hk (h.2 k hk)

#print axioms dottie_direct_joint_moment_block_agrees
#print axioms dottie_direct_joint_moment_row_getD

end QuarticModel.DottieFixedIntervals
