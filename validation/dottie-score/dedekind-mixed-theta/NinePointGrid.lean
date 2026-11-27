import ComplexNewtonCotes

/-! Collapse the shared endpoints of adjacent nine-point quadrature panels. -/

namespace FieldTarget

open scoped BigOperators

noncomputable section

private def initialWeight (j : ℕ) : ℤ :=
  ninePointWeight ⟨j % 8, (Nat.mod_lt _ (by decide : 0 < 8)).trans (by decide : 8 < 9)⟩

private abbrev rightEndpoint (N j : ℕ) : Prop :=
  0 < j ∧ j ≤ 8 * N ∧ j % 8 = 0

/-- The two contributions at each shared grid point are added before evaluation. -/
def ninePointGridWeight (N j : ℕ) : ℤ :=
  (if j < 8 * N then initialWeight j else 0) +
    (if rightEndpoint N j then ninePointWeight (Fin.last 8) else 0)

def ninePointGridPoint (a h : ℝ) (j : ℕ) : ℝ :=
  a + (j : ℝ) * (h / 4)

private theorem sum_eight_blocks {V : Type*} [AddCommMonoid V] (f : ℕ → V) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ i ∈ Finset.range 8, f (8 * k + i)) =
      ∑ j ∈ Finset.range (8 * N), f j := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]

private theorem sum_right_endpoints (f : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range N, f (8 * (k + 1))) =
      ∑ j ∈ Finset.range (8 * N + 1), if rightEndpoint N j then f j else 0 := by
  have hImage : (Finset.range N).image (fun k ↦ 8 * (k + 1)) =
      (Finset.range (8 * N + 1)).filter (rightEndpoint N) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range, rightEndpoint]
    constructor
    · rintro ⟨k, hk, rfl⟩
      omega
    · rintro ⟨_, hPos, hUpper, hMod⟩
      refine ⟨j / 8 - 1, ?_, ?_⟩ <;> omega
  rw [← Finset.sum_filter, ← hImage, Finset.sum_image]
  intro i _ j _ hij
  change 8 * (i + 1) = 8 * (j + 1) at hij
  omega

private theorem sum_shared_grid (f : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range N, ∑ i : Fin 9, (ninePointWeight i : ℂ) * f (8 * k + i.val)) =
      ∑ j ∈ Finset.range (8 * N + 1), (ninePointGridWeight N j : ℂ) * f j := by
  let inner (j : ℕ) := (initialWeight j : ℂ) * f j
  let ends (j : ℕ) := (ninePointWeight (Fin.last 8) : ℂ) * f j
  have hPanel (k : ℕ) :
      (∑ i : Fin 9, (ninePointWeight i : ℂ) * f (8 * k + i.val)) =
        (∑ i ∈ Finset.range 8, inner (8 * k + i)) + ends (8 * (k + 1)) := by
    rw [Fin.sum_univ_castSucc, ← Fin.sum_univ_eq_sum_range (fun i ↦ inner (8 * k + i)) 8]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have hm : (8 * k + i.val) % 8 = i.val := by have := i.isLt; omega
      simp only [inner, initialWeight, hm, Fin.val_castSucc]
      rfl
  have hInner :
      (∑ j ∈ Finset.range (8 * N), inner j) =
        ∑ j ∈ Finset.range (8 * N + 1), if j < 8 * N then inner j else 0 := by
    rw [Finset.sum_range_succ]
    simp only [lt_irrefl, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj]
  simp_rw [hPanel]
  rw [Finset.sum_add_distrib, sum_eight_blocks, hInner, sum_right_endpoints, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hEarly : j < 8 * N <;> by_cases hEnd : rightEndpoint N j <;>
    simp [ninePointGridWeight, hEarly, hEnd, inner, ends, add_mul]

/-- The composite rule is exactly a weighted sum at the `8 * N + 1` equally spaced
grid points. This also handles the empty rule when `N = 0`. -/
theorem ninePointComposite_eq_grid (f : ℝ → ℂ) (a h : ℝ) (N : ℕ) :
    ninePointComposite f a h N =
      ((2 * h / 28350 : ℝ) : ℂ) *
        ∑ j ∈ Finset.range (8 * N + 1), (ninePointGridWeight N j : ℂ) * f (ninePointGridPoint a h j) := by
  have hNode (k : ℕ) (i : Fin 9) :
      a + (2 * (k : ℝ) + 1) * h + h * (ninePointOffset i : ℝ) =
        ninePointGridPoint a h (8 * k + i.val) := by
    unfold ninePointOffset ninePointGridPoint
    push_cast
    ring
  unfold ninePointComposite ninePointRule
  simp_rw [hNode]
  rw [← Finset.mul_sum]
  congr 1
  exact sum_shared_grid (fun j ↦ f (ninePointGridPoint a h j)) N

/-- An exact integer calculation bounds the weight mass used by the 32-panel rule. -/
theorem ninePointGrid32_weight_abs_sum :
    ∑ j ∈ Finset.range 257, |ninePointGridWeight 32 j| = (1316544 : ℤ) := by
  decide +kernel

#print axioms ninePointComposite_eq_grid
#print axioms ninePointGrid32_weight_abs_sum

end

end FieldTarget

