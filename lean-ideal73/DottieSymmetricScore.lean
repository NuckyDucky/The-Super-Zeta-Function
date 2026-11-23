import DottieTriangleScore
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace QuarticModel

open Finset

private abbrev PositiveRow := Σ _ : ℕ, ℕ

private def rowLimit (N a : ℕ) : ℕ := (N - (a+1)^2).sqrt

private def positiveRows (N : ℕ) : Finset PositiveRow :=
  (range N.sqrt).sigma (fun a => range (rowLimit N a))

private def swapCoordinates (p : PositiveRow) : PositiveRow := ⟨p.2, p.1⟩

private def positiveNorm (p : PositiveRow) : ℕ := (p.1+1)^2 + (p.2+1)^2

private def positiveSign (p : PositiveRow) : ℤ :=
  dottieRowSign ((p.1 : ℤ)+1) ((p.2 : ℤ)+1)

private def axisTerm (f : ℕ → ℤ) (a : ℕ) : ℤ :=
  dottieRowSign ((a : ℤ)+1) 0 * f ((a+1)^2)

private def positiveTerm (f : ℕ → ℤ) (p : PositiveRow) : ℤ :=
  positiveSign p * f (positiveNorm p)

private def pairedTerm (f : ℕ → ℤ) (p : PositiveRow) : ℤ :=
  let sign := positiveSign p + positiveSign (swapCoordinates p)
  if sign = 0 then 0 else sign * f (positiveNorm p)

/-- Evaluate each axis point and diagonal point once. For a pair with two
different positive coordinates, compute the weight once when its combined
sign is nonzero. Both loop indices are one less than their coordinates. -/
def dottieSymmetricScore (N : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ a ∈ range N.sqrt,
    let last := rowLimit N a
    axisTerm f a + ((if a < last then positiveTerm f ⟨a, a⟩ else 0) +
      ∑ b ∈ range (min a last), pairedTerm f ⟨a, b⟩)

private theorem swap_twice (p : PositiveRow) : swapCoordinates (swapCoordinates p) = p := by
  cases p
  rfl

private theorem swap_norm (p : PositiveRow) : positiveNorm (swapCoordinates p) = positiveNorm p :=
  Nat.add_comm _ _

private theorem pairedTerm_eq (f : ℕ → ℤ) (p : PositiveRow) :
    pairedTerm f p = positiveTerm f p + positiveTerm f (swapCoordinates p) := by
  simp only [pairedTerm, positiveTerm, swap_norm, ← add_mul]
  split <;> simp_all only [zero_mul]

private theorem mem_positiveRows {N : ℕ} {p : PositiveRow} :
    p ∈ positiveRows N ↔ positiveNorm p ≤ N := by
  rw [positiveRows, Finset.mem_sigma, Finset.mem_range, Finset.mem_range]
  constructor
  · rintro ⟨ha, hb⟩
    have ha' : (p.1+1)^2 ≤ N := Nat.le_sqrt'.mp (Nat.succ_le_of_lt ha)
    have hb' : (p.2+1)^2 ≤ N-(p.1+1)^2 := Nat.le_sqrt'.mp (Nat.succ_le_of_lt hb)
    dsimp only [positiveNorm]
    omega
  · intro hn
    dsimp only [positiveNorm] at hn
    constructor
    · apply Nat.lt_of_succ_le
      apply Nat.le_sqrt'.mpr
      change (p.1+1)^2 ≤ N
      omega
    · apply Nat.lt_of_succ_le
      apply Nat.le_sqrt'.mpr
      change (p.2+1)^2 ≤ N - (p.1+1)^2
      omega

private theorem swap_mem_positiveRows {N : ℕ} {p : PositiveRow} (hp : p ∈ positiveRows N) :
    swapCoordinates p ∈ positiveRows N := by
  rw [mem_positiveRows, swap_norm]
  exact mem_positiveRows.mp hp

private theorem triangle_axis_split (N : ℕ) (f : ℕ → ℤ) :
    dottieTriangleScore N f = (∑ a ∈ range N.sqrt, axisTerm f a) +
      ∑ p ∈ positiveRows N, positiveTerm f p := by
  simp only [dottieTriangleScore, positiveRows, Finset.sum_sigma]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_range_succ', add_comm]
  simp [axisTerm, positiveTerm, positiveSign, positiveNorm, rowLimit]

private theorem positive_compare_split (s : Finset PositiveRow) (f : ℕ → ℤ) :
    (∑ p ∈ s, positiveTerm f p) =
      (∑ p ∈ s.filter (fun p => p.1 = p.2), positiveTerm f p) +
      ((∑ p ∈ s.filter (fun p => p.2 < p.1), positiveTerm f p) +
        ∑ p ∈ s.filter (fun p => p.1 < p.2), positiveTerm f p) := by
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rcases lt_trichotomy p.1 p.2 with h | h | h
  · simp [h, h.ne, not_lt_of_ge h.le]
  · simp [h]
  · simp [h, h.ne', not_lt_of_ge h.le]

private theorem upper_sum_eq_swapped_lower (N : ℕ) (f : ℕ → ℤ) :
    (∑ p ∈ (positiveRows N).filter (fun p => p.1 < p.2), positiveTerm f p) =
      ∑ p ∈ (positiveRows N).filter (fun p => p.2 < p.1), positiveTerm f (swapCoordinates p) := by
  refine Finset.sum_bij' (fun p _ => swapCoordinates p) (fun p _ => swapCoordinates p)
    ?_ ?_ (fun p _ => swap_twice p) (fun p _ => swap_twice p) ?_
  · intro p hp
    obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨swap_mem_positiveRows hmem, hlt⟩
  · intro p hp
    obtain ⟨hmem, hlt⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨swap_mem_positiveRows hmem, hlt⟩
  · intro p _
    rw [swap_twice]

private theorem diagonal_sum (N : ℕ) (f : ℕ → ℤ) :
    (∑ p ∈ (positiveRows N).filter (fun p => p.1 = p.2), positiveTerm f p) =
      ∑ a ∈ range N.sqrt, if a < rowLimit N a then positiveTerm f ⟨a,a⟩ else 0 := by
  simp only [Finset.sum_filter, positiveRows, Finset.sum_sigma, Finset.sum_ite_eq, Finset.mem_range]

private theorem lower_pair_sum (N : ℕ) (f : ℕ → ℤ) :
    (∑ p ∈ (positiveRows N).filter (fun p => p.2 < p.1), pairedTerm f p) =
      ∑ a ∈ range N.sqrt, ∑ b ∈ range (min a (rowLimit N a)), pairedTerm f ⟨a,b⟩ := by
  simp only [Finset.sum_filter, positiveRows, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b ∈ range (rowLimit N a), if b < a then pairedTerm f ⟨a,b⟩ else 0) = _
  rw [← Finset.sum_filter]
  have h : (range (rowLimit N a)).filter (fun b => b < a) = range (min a (rowLimit N a)) := by
    ext b
    simp [and_comm]
  rw [h]

/-- Swapping the positive coordinates preserves every norm weight. The exact
triangular score is therefore unchanged by combining each off-diagonal pair. -/
theorem dottieSymmetricScore_eq_dottieTriangleScore (N : ℕ) (f : ℕ → ℤ) :
    dottieSymmetricScore N f = dottieTriangleScore N f := by
  symm
  rw [triangle_axis_split, positive_compare_split, upper_sum_eq_swapped_lower,
    ← Finset.sum_add_distrib]
  simp_rw [← pairedTerm_eq]
  rw [diagonal_sum, lower_pair_sum]
  simp only [dottieSymmetricScore, Finset.sum_add_distrib]

#print axioms dottieSymmetricScore
#print axioms dottieSymmetricScore_eq_dottieTriangleScore

end QuarticModel
