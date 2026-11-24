import GaussianQuarterLattice
import QuarticSignedMultiplicativity

/-! Replay the archived square-root row enumeration on the toolchain of
the field proof and identify its coefficients with the signed ideal sum. -/

namespace QuarticModel

open ArithmeticFunction FieldCoefficientTransfer
open scoped Classical

private def rowIndex (n j : ℕ) : ℕ × ℕ := (j, (n-(j+1)^2).sqrt)

private def onArchivedShell (n j : ℕ) : Prop :=
  (j+1)^2 + (n-(j+1)^2).sqrt^2 = n

private noncomputable def shellRows (n : ℕ) : Finset ℕ :=
  (Finset.range n.sqrt).filter (onArchivedShell n)

/-- The row from `verification/quartic-kernel/source/QuarticKernel.lean`,
with the same three conductor symbols evaluated by `archivedGaussianSign`. -/
noncomputable def archivedLatticeRow (n j : ℕ) : ℤ :=
  if onArchivedShell n j then archivedGaussianSign ⟨(j : ℤ)+1, (rowIndex n j).2⟩ else 0

noncomputable def archivedLatticeCoeff (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range n.sqrt, archivedLatticeRow n j

private noncomputable def archivedShellEquiv (n : ℕ) (hn : n ≠ 0) :
    ↥(shellRows n) ≃ GaussianNormFiber n := by
  let f (j : ↥(shellRows n)) : GaussianNormFiber n :=
    ⟨gaussianQuarterIdeal (rowIndex n j.val),
      (gaussianQuarterIdeal_norm _).trans ((Finset.mem_filter.mp j.property).2)⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro i j h
    have he := congrArg Subtype.val h
    change gaussianQuarterIdeal (rowIndex n i.val) = gaussianQuarterIdeal (rowIndex n j.val) at he
    exact Subtype.ext (congrArg Prod.fst
      (gaussianQuarterIdealEquiv.injective (Subtype.ext he)))
  · intro I
    have hI : I.val ≠ ⊥ := by
      intro h
      exact hn (I.property.symm.trans (h ▸ Ideal.absNorm_bot))
    obtain ⟨p,hp⟩ := gaussianQuarterIdealEquiv.surjective ⟨I.val,hI⟩
    have hval : gaussianQuarterIdeal p = I.val := congrArg Subtype.val hp
    have hnorm := (gaussianQuarterIdeal_norm p).symm.trans ((congrArg Ideal.absNorm hval).trans I.property)
    have hj : p.1 < n.sqrt := by
      have hle : (p.1+1)^2 ≤ n := hnorm ▸ Nat.le_add_right _ _
      exact Nat.le_sqrt'.mpr hle
    have hrow : rowIndex n p.1 = p := by
      rw [rowIndex, ← hnorm, Nat.add_sub_cancel_left, Nat.sqrt_eq']
    have hshell : onArchivedShell n p.1 := by
      change ((rowIndex n p.1).1+1)^2 + (rowIndex n p.1).2^2 = n
      rw [hrow]
      exact hnorm
    refine ⟨⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,hshell⟩⟩, Subtype.ext ?_⟩
    change gaussianQuarterIdeal (rowIndex n p.1) = I.val
    exact (congrArg gaussianQuarterIdeal hrow).trans hval

theorem archivedLatticeCoeff_eq_signedIdealNormSum (n : ℕ) (hn : n ≠ 0) :
    (archivedLatticeCoeff n : ℂ) = signedIdealNormSum n := by
  unfold signedIdealNormSum
  rw [← (archivedShellEquiv n hn).tsum_eq (fun I => (archivedIdealCharacter I.val : ℂ)), tsum_fintype]
  unfold archivedLatticeCoeff archivedLatticeRow
  rw [Int.cast_sum]
  simp_rw [Int.cast_ite, Int.cast_zero]
  rw [← Finset.sum_filter]
  have he (j : ↥(shellRows n)) :
      archivedIdealCharacter ((archivedShellEquiv n hn j).val) =
        archivedGaussianSign ⟨(j.val : ℤ)+1, (rowIndex n j.val).2⟩ := by
    exact gaussianQuarterIdeal_signed_weight (rowIndex n j.val)
  simp_rw [he]
  exact (Finset.sum_coe_sort (shellRows n)
    (fun j => (archivedGaussianSign ⟨(j : ℤ)+1, (rowIndex n j).2⟩ : ℂ))).symm

theorem signedIdealCoefficients_eq_archivedLatticeCoeff (n : ℕ) :
    signedIdealCoefficients n = (archivedLatticeCoeff n : ℂ) := by
  by_cases hn : n = 0
  · simp [hn, archivedLatticeCoeff]
  · simpa [signedIdealCoefficients, toArithmeticFunction, hn] using
      (archivedLatticeCoeff_eq_signedIdealNormSum n hn).symm

theorem idealCounts_eq_archivedLattice_convolution :
    idealCounts K = zetaCoeff * betaCoeff * toArithmeticFunction (fun n => (archivedLatticeCoeff n : ℂ)) := by
  have hg : signedIdealCoefficients = toArithmeticFunction (fun n => (archivedLatticeCoeff n : ℂ)) := by
    ext n
    rw [signedIdealCoefficients_eq_archivedLatticeCoeff]
    by_cases h : n = 0 <;> simp [toArithmeticFunction, h, archivedLatticeCoeff]
  rw [← hg]
  exact idealCounts_eq_archived_convolution

#print axioms archivedLatticeCoeff_eq_signedIdealNormSum
#print axioms signedIdealCoefficients_eq_archivedLatticeCoeff
#print axioms idealCounts_eq_archivedLattice_convolution

end QuarticModel
