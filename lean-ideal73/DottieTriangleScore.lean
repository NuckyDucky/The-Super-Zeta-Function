import ArchivedQuarticLatticeCoefficients
import DottieRowSign
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace QuarticModel

open Finset
open private onArchivedShell rowIndex shellRows from ArchivedQuarticLatticeCoefficients

/-- Visit the first-quadrant lattice points of positive norm at most `N`.
The outer index is one less than the real coordinate. -/
def dottieTriangleScore (N : ℕ) (f : ℕ → ℤ) : ℤ :=
  ∑ a ∈ range N.sqrt, ∑ b ∈ range ((N - (a + 1)^2).sqrt + 1),
    dottieRowSign ((a : ℤ) + 1) b * f ((a + 1)^2 + b^2)

/-- The triangular enumeration preserves the exact sign and the norm weight
of every archived row. -/
theorem dottieTriangleScore_eq_archivedLatticeCoeff (N : ℕ) (f : ℕ → ℤ) :
    dottieTriangleScore N f = ∑ n ∈ range N, archivedLatticeCoeff (n + 1) * f (n + 1) := by
  classical
  let source := (range N).sigma (fun n => shellRows (n + 1))
  let target := (range N.sqrt).sigma (fun a => range ((N - (a + 1)^2).sqrt + 1))
  let normAt (q : Σ _ : ℕ, ℕ) := (q.1 + 1)^2 + q.2^2
  let toTriangle (p : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨p.2, (rowIndex (p.1 + 1) p.2).2⟩
  let toShell (q : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨normAt q - 1, q.1⟩
  have hnorm_pos (q : Σ _ : ℕ, ℕ) : 0 < normAt q := by
    dsimp [normAt]
    positivity
  have hnorm_pred (q : Σ _ : ℕ, ℕ) : (toShell q).1 + 1 = normAt q :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt (hnorm_pos q))
  have hnorm (p : Σ _ : ℕ, ℕ) (hp : p ∈ source) : normAt (toTriangle p) = p.1 + 1 :=
    (mem_filter.mp (mem_sigma.mp hp).2).2
  have htriangle (p : Σ _ : ℕ, ℕ) (hp : p ∈ source) : toTriangle p ∈ target := by
    have h := mem_sigma.mp hp
    have hn : p.1 + 1 ≤ N := Nat.succ_le_of_lt (mem_range.mp h.1)
    have hj := mem_range.mp (mem_filter.mp h.2).1
    apply mem_sigma.mpr
    refine ⟨mem_range.mpr (hj.trans_le (Nat.sqrt_le_sqrt hn)), mem_range.mpr ?_⟩
    exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt (Nat.sub_le_sub_right hn _))
  have hshell (q : Σ _ : ℕ, ℕ) (hq : q ∈ target) : toShell q ∈ source := by
    have h := mem_sigma.mp hq
    have ha : (q.1 + 1)^2 ≤ N := Nat.le_sqrt'.mp (Nat.succ_le_of_lt (mem_range.mp h.1))
    have hb : q.2^2 ≤ N - (q.1 + 1)^2 := Nat.le_sqrt'.mp (Nat.le_of_lt_succ (mem_range.mp h.2))
    have hn : normAt q ≤ N := by
      change (q.1 + 1)^2 + q.2^2 ≤ N
      omega
    apply mem_sigma.mpr
    refine ⟨mem_range.mpr ?_, ?_⟩
    · change normAt q - 1 < N
      have hp := hnorm_pos q
      omega
    · change q.1 ∈ shellRows ((toShell q).1 + 1)
      rw [hnorm_pred, shellRows]
      refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_of_succ_le (Nat.le_sqrt'.mpr ?_)), ?_⟩
      · exact Nat.le_add_right _ _
      · simp [onArchivedShell, normAt, Nat.sqrt_eq']
  have hleft (p : Σ _ : ℕ, ℕ) (hp : p ∈ source) : toShell (toTriangle p) = p := by
    refine Sigma.ext ?_ (heq_of_eq rfl)
    change normAt (toTriangle p) - 1 = p.1
    simp [hnorm p hp]
  have hright (q : Σ _ : ℕ, ℕ) : toTriangle (toShell q) = q := by
    refine Sigma.ext rfl (heq_of_eq ?_)
    change (((toShell q).1 + 1) - (q.1 + 1)^2).sqrt = q.2
    rw [hnorm_pred]
    simp [normAt, Nat.sqrt_eq']
  symm
  calc
    _ = ∑ p ∈ source, archivedLatticeRow (p.1 + 1) p.2 * f (p.1 + 1) := by
      simp only [source, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro n _
      rw [archivedLatticeCoeff, Finset.sum_mul, shellRows, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : onArchivedShell (n + 1) j <;> simp [archivedLatticeRow, h]
    _ = ∑ q ∈ target, dottieRowSign ((q.1 : ℤ) + 1) q.2 * f (normAt q) := by
      refine Finset.sum_bij' (fun p _ => toTriangle p) (fun q _ => toShell q)
        htriangle hshell hleft (fun q _ => hright q) ?_
      intro p hp
      have h := (mem_filter.mp (mem_sigma.mp hp).2).2
      simp only [archivedLatticeRow, if_pos h, dottieRowSign_eq_archivedGaussianSign, hnorm p hp, toTriangle]
    _ = dottieTriangleScore N f := by
      simp only [target, Finset.sum_sigma, normAt, dottieTriangleScore]

#print axioms dottieTriangleScore
#print axioms dottieTriangleScore_eq_archivedLatticeCoeff

end QuarticModel
