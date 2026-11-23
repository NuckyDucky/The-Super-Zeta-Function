import DottieSymmetricScore
import DottieQuickScore

/-! Independently checkable blocks after pairing points with swapped
positive coordinates. Both block indices are zero-based. -/

open Finset

namespace QuarticModel

open private rowLimit axisTerm positiveTerm pairedTerm from DottieSymmetricScore

def dottiePairRowSize (N a : ℕ) : ℕ := min a (rowLimit N a)

/-- The axis and diagonal have a single representative each. -/
def dottiePairRowHead (N : ℕ) (f : ℕ → ℤ) (a : ℕ) : ℤ :=
  axisTerm f a + if a < rowLimit N a then positiveTerm f ⟨a,a⟩ else 0

def dottiePairRowBlock (f : ℕ → ℤ) (a lo len : ℕ) : ℤ :=
  (List.range len).foldl (fun s j => s + pairedTerm f ⟨a,lo+j⟩) 0

theorem dottiePairRowBlock_eq_sum (f : ℕ → ℤ) (a lo len : ℕ) :
    dottiePairRowBlock f a lo len = ∑ j ∈ range len, pairedTerm f ⟨a,lo+j⟩ := by
  induction len with
  | zero => simp [dottiePairRowBlock]
  | succ len ih =>
    rw [Finset.sum_range_succ]
    simp only [dottiePairRowBlock, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
    rw [← ih]

theorem dottiePairRowBlock_add (f : ℕ → ℤ) (a lo left right : ℕ) :
    dottiePairRowBlock f a lo (left+right) =
      dottiePairRowBlock f a lo left + dottiePairRowBlock f a (lo+left) right := by
  simp only [dottiePairRowBlock_eq_sum, Finset.sum_range_add, Nat.add_assoc]

private theorem pairRowBlock_eq_full_blocks (f : ℕ → ℤ) (a width count : ℕ) :
    dottiePairRowBlock f a 0 (count*width) =
      ∑ k ∈ range count, dottiePairRowBlock f a (k*width) width := by
  induction count with
  | zero => simp [dottiePairRowBlock]
  | succ count ih =>
    rw [Nat.succ_mul, dottiePairRowBlock_add, ih, Finset.sum_range_succ, Nat.zero_add]

theorem dottiePairRowBlock_eq_blocks (f : ℕ → ℤ) (a len width : ℕ) :
    dottiePairRowBlock f a 0 len =
      (∑ k ∈ range (len/width), dottiePairRowBlock f a (k*width) width) +
      dottiePairRowBlock f a ((len/width)*width) (len%width) := by
  conv_lhs => rw [← Nat.div_add_mod' len width]
  rw [dottiePairRowBlock_add, pairRowBlock_eq_full_blocks, Nat.zero_add]

theorem dottieSymmetricScore_eq_blocks (N : ℕ) (f : ℕ → ℤ) (width : ℕ) :
    dottieSymmetricScore N f = ∑ a ∈ range N.sqrt,
      (dottiePairRowHead N f a +
        ((∑ k ∈ range (dottiePairRowSize N a/width), dottiePairRowBlock f a (k*width) width) +
        dottiePairRowBlock f a ((dottiePairRowSize N a/width)*width) (dottiePairRowSize N a%width))) := by
  unfold dottieSymmetricScore
  apply sum_congr rfl
  intro a _
  rw [← dottiePairRowBlock_eq_blocks, dottiePairRowBlock_eq_sum]
  simp only [dottiePairRowHead, dottiePairRowSize, Nat.zero_add, add_assoc]

/-- Pairing and skipping zero signs leaves the cached-log score exact. -/
theorem dottieQuickReferenceScore_eq_symmetric :
    dottieQuickReferenceScore = dottieSymmetricScore 276824064 dottieQuickWeightTicks :=
  (dottieSymmetricScore_eq_dottieTriangleScore _ _).symm

theorem dottieCircleReference_pos_of_symmetric_score
    (h : 7*(fixedCosScale:ℤ)^5 < 50*dottieSymmetricScore 276824064 dottieQuickWeightTicks) :
    0 < dottieCircleReference := by
  apply dottieCircleReference_pos_of_quick_score
  rw [dottieQuickReferenceScore_eq_symmetric]
  exact h

#print axioms dottiePairRowBlock_add
#print axioms dottiePairRowBlock_eq_blocks
#print axioms dottieSymmetricScore_eq_blocks
#print axioms dottieQuickReferenceScore_eq_symmetric
#print axioms dottieCircleReference_pos_of_symmetric_score

end QuarticModel
