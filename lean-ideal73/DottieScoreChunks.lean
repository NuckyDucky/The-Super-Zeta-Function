import DottieReferenceScore
import Mathlib.Algebra.BigOperators.Intervals

/-! Check disjoint portions of a Gaussian lattice row separately, and
recombine their integer values into exactly the reference score. -/

open Finset

namespace QuarticModel

private def weightedRowTerm (f : ℕ → ℤ) (a b : ℕ) : ℤ :=
  let c := dottieRowSign (a : ℤ) (b : ℤ)
  if c = 0 then 0 else c * f (a^2+b^2)

private theorem weightedRowTerm_eq (f : ℕ → ℤ) (a b : ℕ) :
    weightedRowTerm f a b = dottieRowSign (a : ℤ) (b : ℤ) * f (a^2+b^2) := by
  dsimp only [weightedRowTerm]
  split <;> simp_all

/-- The portion of the row `(a,b)` with `lo ≤ b < lo+len`, evaluated with
one integer accumulator. A zero sign skips evaluation of its weight. -/
def dottieRowChunk (f : ℕ → ℤ) (a lo len : ℕ) : ℤ :=
  (List.range len).foldl (fun s j => s + weightedRowTerm f a (lo+j)) 0

theorem dottieRowChunk_eq_sum (f : ℕ → ℤ) (a lo len : ℕ) :
    dottieRowChunk f a lo len = ∑ j ∈ range len,
      dottieRowSign (a : ℤ) ((lo+j : ℕ) : ℤ) * f (a^2+(lo+j)^2) := by
  induction len with
  | zero => simp [dottieRowChunk]
  | succ len ih =>
    rw [Finset.sum_range_succ]
    simp only [dottieRowChunk, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      weightedRowTerm_eq] at ih ⊢
    rw [← ih]

theorem dottieRowChunk_add (f : ℕ → ℤ) (a lo left right : ℕ) :
    dottieRowChunk f a lo (left+right) =
      dottieRowChunk f a lo left + dottieRowChunk f a (lo+left) right := by
  simp only [dottieRowChunk_eq_sum, Finset.sum_range_add, Nat.add_assoc]

private theorem dottieRowChunk_eq_full_blocks (f : ℕ → ℤ) (a width count : ℕ) :
    dottieRowChunk f a 0 (count*width) =
      ∑ k ∈ range count, dottieRowChunk f a (k*width) width := by
  induction count with
  | zero => simp [dottieRowChunk]
  | succ count ih =>
    rw [Nat.succ_mul, dottieRowChunk_add, ih, Finset.sum_range_succ, Nat.zero_add]

/-- Full blocks and the final short block cover each row exactly. -/
theorem dottieRowChunk_eq_blocks (f : ℕ → ℤ) (a len width : ℕ) :
    dottieRowChunk f a 0 len =
      (∑ k ∈ range (len/width), dottieRowChunk f a (k*width) width) +
      dottieRowChunk f a ((len/width)*width) (len%width) := by
  conv_lhs => rw [← Nat.div_add_mod' len width]
  rw [dottieRowChunk_add, dottieRowChunk_eq_full_blocks, Nat.zero_add]

/-- Number of original lattice points with real coordinate `a` in the
archived reference cutoff. The row index starts at `a=1`. -/
def dottieReferenceRowSize (a : ℕ) : ℕ := Nat.sqrt (276824064-a^2)+1

theorem dottieReferenceScoreRows_eq_chunks : dottieReferenceScoreRows =
    ∑ r ∈ range (Nat.sqrt 276824064),
      dottieRowChunk dottieWeightTicks (r+1) 0 (dottieReferenceRowSize (r+1)) := by
  simp only [dottieReferenceScoreRows, dottieTriangleScore, dottieRowChunk_eq_sum, Nat.zero_add, Nat.cast_add,
    Nat.cast_one, dottieReferenceRowSize]

/-- A checked value for each full block and each remainder gives the exact
integer total used in the positivity theorem. -/
theorem dottieReferenceScoreRows_eq_block_sums (width : ℕ) :
    dottieReferenceScoreRows = ∑ r ∈ range (Nat.sqrt 276824064),
      ((∑ k ∈ range (dottieReferenceRowSize (r+1)/width),
        dottieRowChunk dottieWeightTicks (r+1) (k*width) width) +
        dottieRowChunk dottieWeightTicks (r+1) ((dottieReferenceRowSize (r+1)/width)*width)
          (dottieReferenceRowSize (r+1)%width)) := by
  rw [dottieReferenceScoreRows_eq_chunks]
  exact sum_congr rfl (fun r _ => dottieRowChunk_eq_blocks dottieWeightTicks (r+1) _ width)

#print axioms dottieRowChunk_eq_sum
#print axioms dottieRowChunk_add
#print axioms dottieRowChunk_eq_blocks
#print axioms dottieReferenceScoreRows_eq_chunks
#print axioms dottieReferenceScoreRows_eq_block_sums

end QuarticModel
