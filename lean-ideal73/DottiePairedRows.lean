import DottieSymmetricChunks

/-! Consecutive row spans can be verified and assembled independently.
The row span uses zero-based indices. -/

open Finset

namespace QuarticModel

private def pairedRowTotal (N : ℕ) (f : ℕ → ℤ) (a : ℕ) : ℤ :=
  dottiePairRowHead N f a + dottiePairRowBlock f a 0 (dottiePairRowSize N a)

/-- Sum a contiguous range of axis, diagonal, and off-diagonal pairs. -/
def dottiePairedRowSpan (N : ℕ) (f : ℕ → ℤ) (lo len : ℕ) : ℤ :=
  (List.range len).foldl (fun s a => s + pairedRowTotal N f (lo+a)) 0

private theorem dottiePairedRowSpan_eq_sum (N : ℕ) (f : ℕ → ℤ) (lo len : ℕ) :
    dottiePairedRowSpan N f lo len = ∑ j ∈ range len, pairedRowTotal N f (lo+j) := by
  induction len with
  | zero => simp [dottiePairedRowSpan]
  | succ len ih =>
    rw [Finset.sum_range_succ]
    simp only [dottiePairedRowSpan, List.range_succ, List.foldl_append, List.foldl_cons,
      List.foldl_nil] at ih ⊢
    rw [← ih]

theorem dottiePairedRowSpan_add (N : ℕ) (f : ℕ → ℤ) (lo left right : ℕ) :
    dottiePairedRowSpan N f lo (left+right) =
      dottiePairedRowSpan N f lo left + dottiePairedRowSpan N f (lo+left) right := by
  simp only [dottiePairedRowSpan_eq_sum, Finset.sum_range_add, Nat.add_assoc]

theorem dottiePairedRowSpan_one (N : ℕ) (f : ℕ → ℤ) (a : ℕ) :
    dottiePairedRowSpan N f a 1 =
      dottiePairRowHead N f a + dottiePairRowBlock f a 0 (dottiePairRowSize N a) := by
  simp [dottiePairedRowSpan_eq_sum, pairedRowTotal]

theorem dottieSymmetricScore_eq_row_span (N : ℕ) (f : ℕ → ℤ) :
    dottieSymmetricScore N f = dottiePairedRowSpan N f 0 N.sqrt := by
  rw [dottieSymmetricScore_eq_blocks N f 1024, dottiePairedRowSpan_eq_sum]
  refine sum_congr rfl (fun a _ => ?_)
  rw [← dottiePairRowBlock_eq_blocks, Nat.zero_add]
  rfl

theorem dottieQuickReferenceScore_eq_row_span :
    dottieQuickReferenceScore = dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 := by
  rw [dottieQuickReferenceScore_eq_symmetric, dottieSymmetricScore_eq_row_span,
    show Nat.sqrt 276824064 = 16638 by decide +kernel]

#print axioms dottiePairedRowSpan_add
#print axioms dottiePairedRowSpan_one
#print axioms dottieSymmetricScore_eq_row_span
#print axioms dottieQuickReferenceScore_eq_row_span

end QuarticModel
