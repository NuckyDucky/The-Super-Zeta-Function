import QuarticKernel
import QuarticPrefix

namespace QuarticKernel

private def validRow (n j : ℕ) : Prop :=
  (j+1)^2 + (n-(j+1)^2).sqrt^2 = n

private instance (n j : ℕ) : Decidable (validRow n j) := by
  unfold validRow
  infer_instance

private def selectedRows (n : ℕ) := (Finset.range n.sqrt).filter (validRow n)

private def latticeRows (N j : ℕ) := Finset.range ((N-(j+1)^2).sqrt+1)

private def toLattice (p : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ :=
  ⟨p.2, (p.1-(p.2+1)^2).sqrt⟩

private def toNorm (p : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ :=
  ⟨(p.1+1)^2+p.2^2, p.1⟩

private theorem row_off {n j : ℕ} (h : ¬ validRow n j) : row n j = 0 := by
  have hn := h
  simp only [validRow, pow_two] at hn
  simp only [row, if_neg hn]

private theorem toLattice_mem {N : ℕ} {p : Σ _ : ℕ, ℕ}
    (hp : p ∈ (Finset.range (N+1)).sigma selectedRows) :
    toLattice p ∈ (Finset.range N.sqrt).sigma (latticeRows N) := by
  have h := Finset.mem_sigma.mp hp
  have hn := Nat.le_of_lt_succ (Finset.mem_range.mp h.1)
  have hj := Finset.mem_range.mp (Finset.mem_filter.mp h.2).1
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_range.mpr (hj.trans_le (Nat.sqrt_le_sqrt hn)), ?_⟩
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (Nat.sqrt_le_sqrt (Nat.sub_le_sub_right hn _))

private theorem toNorm_mem {N : ℕ} {p : Σ _ : ℕ, ℕ}
    (hp : p ∈ (Finset.range N.sqrt).sigma (latticeRows N)) :
    toNorm p ∈ (Finset.range (N+1)).sigma selectedRows := by
  have h := Finset.mem_sigma.mp hp
  have ha := Nat.le_sqrt'.mp (Finset.mem_range.mp h.1)
  have hb := Nat.le_sqrt'.mp (Nat.le_of_lt_succ (Finset.mem_range.mp h.2))
  apply Finset.mem_sigma.mpr
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le ?_), ?_⟩
  · change (p.1+1)^2+p.2^2 ≤ N
    change (p.1+1)^2 ≤ N at ha
    change p.2^2 ≤ N-(p.1+1)^2 at hb
    omega
  · change p.1 ∈ selectedRows ((p.1+1)^2+p.2^2)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (Nat.lt_of_succ_le (Nat.le_sqrt'.2 (Nat.le_add_right _ _))),
      by simp [validRow, Nat.sqrt_eq']⟩

private theorem norm_inverse {N : ℕ} {p : Σ _ : ℕ, ℕ}
    (hp : p ∈ (Finset.range (N+1)).sigma selectedRows) :
    toNorm (toLattice p) = p := by
  have hv := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
  rcases p with ⟨n,j⟩
  refine Sigma.ext ?_ (heq_of_eq rfl)
  exact hv

private theorem lattice_inverse (p : Σ _ : ℕ, ℕ) : toLattice (toNorm p) = p := by
  cases p
  simp [toLattice, toNorm, Nat.sqrt_eq']

/-- Weighted norm sums equal the direct quarter-lattice enumeration. This
allows bin totals to be computed by visiting each lattice point once. -/
theorem weighted_coefficients (N : ℕ) (weight : ℕ → ℤ) :
    (∑ n ∈ Finset.range (N+1), coeff n * weight n) =
      ∑ a ∈ Finset.range N.sqrt, ∑ b ∈ latticeRows N a,
        SuperZeta.FieldWeights.conductorReading (a+1) b * weight ((a+1)^2+b^2) := by
  calc
    _ = ∑ p ∈ (Finset.range (N+1)).sigma selectedRows, row p.1 p.2 * weight p.1 := by
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro n _
      rw [coeff, Finset.sum_mul, selectedRows, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : validRow n j
      · rw [if_pos h]
      · rw [if_neg h, row_off h, zero_mul]
    _ = ∑ p ∈ (Finset.range N.sqrt).sigma (latticeRows N),
        SuperZeta.FieldWeights.conductorReading (p.1+1) p.2 * weight (toNorm p).1 := by
      refine Finset.sum_bij' (fun p _ => toLattice p) (fun p _ => toNorm p)
        (fun _ hp => toLattice_mem hp) (fun _ hp => toNorm_mem hp)
        (fun _ hp => norm_inverse hp) (fun p _ => lattice_inverse p) ?_
      intro p hp
      rw [norm_inverse hp]
      have hv := (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
      have hv' := hv
      simp only [validRow, pow_two] at hv'
      simp only [row, if_pos hv', toLattice, pow_two, Nat.cast_add, Nat.cast_one]
    _ = _ := by rw [Finset.sum_sigma]; rfl

#print axioms weighted_coefficients

def evalWeighted (N : ℕ) (weight : ℕ → ℤ) : ℤ :=
  ∑ a ∈ Finset.range N.sqrt, ∑ b ∈ latticeRows N a,
    evalMark (a+1) b * weight ((a+1)^2+b^2)

theorem evalWeighted_eq (N : ℕ) (weight : ℕ → ℤ) :
    evalWeighted N weight = ∑ n ∈ Finset.range (N+1), coeff n*weight n := by
  rw [weighted_coefficients]
  simp only [evalWeighted, evalMark_eq, Nat.cast_add, Nat.cast_one]

theorem prefix_bin_weighted (a m : ℕ) :
    (∑ i ∈ Finset.range m, prefixSum (a+i+1)) =
      (m:ℤ)*prefixSum a + ∑ i ∈ Finset.range m, ((m:ℤ)-i)*coeff (a+i+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Finset.sum_range_succ]
    rw [ih]
    have hh : prefixSum (a+m+1) =
        prefixSum a + ∑ i ∈ Finset.range (m+1), coeff (a+i+1) := by
      unfold prefixSum
      rw [show a+m+1=a+(m+1) by omega, Finset.sum_range_add]
    rw [hh]
    simp only [Finset.sum_range_succ, Nat.cast_succ]
    have hsum : (∑ i ∈ Finset.range m, (((m:ℤ)+1)-i)*coeff (a+i+1)) =
        (∑ i ∈ Finset.range m, ((m:ℤ)-i)*coeff (a+i+1)) +
          ∑ i ∈ Finset.range m, coeff (a+i+1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    ring

#print axioms evalWeighted_eq
#print axioms prefix_bin_weighted

end QuarticKernel
