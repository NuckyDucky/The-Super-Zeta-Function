import GaussianQuarticClosure
import GaussianCMPrimeBarrier
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Label the eight automorphisms of the concrete quartic splitting
field by their permutations of the four marked roots. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open NumberField Polynomial

noncomputable section

/-- Going halfway around the index cycle negates the corresponding root. -/
def rootAt (j : ZMod 4) : L := ![alpha, beta, -alpha, -beta] (show Fin 4 from j)

theorem rootAt_add_two (j : ZMod 4) : rootAt (j + 2) = -rootAt j := by
  fin_cases j
  · rfl
  · rfl
  · exact (neg_neg alpha).symm
  · exact (neg_neg beta).symm

theorem rootAt_injective : Function.Injective rootAt := by
  have hAB : alpha ≠ beta := fun h => alpha_sq_ne_beta_sq (congrArg (fun u : L => u ^ 2) h)
  have hABn : alpha ≠ -beta := by
    intro h
    apply alpha_sq_ne_beta_sq
    rw [h]
    ring
  have hAnB : -alpha ≠ beta := by
    intro h
    exact hABn (by simpa only [neg_neg] using congrArg Neg.neg h)
  have hAn : alpha ≠ -alpha := by
    intro h
    have hh : (2 : L) * alpha = 0 := by linear_combination h
    exact mul_ne_zero (by norm_num) alpha_ne_zero hh
  have hBn : beta ≠ -beta := by
    intro h
    have hh : (2 : L) * beta = 0 := by linear_combination h
    exact mul_ne_zero (by norm_num) beta_ne_zero hh
  intro j k hjk
  fin_cases j <;> fin_cases k <;> simp_all [rootAt] <;> rfl

theorem rootAt_mem (j : ZMod 4) : rootAt j ∈ QuarticModel.rationalPolynomial.rootSet L := by
  rw [mem_iff_marked_root]
  fin_cases j <;> simp [rootAt]

/-- An index for every root, with the original quartic root at index zero. -/
def rootIndexEquiv : ZMod 4 ≃ {z : L // z ∈ QuarticModel.rationalPolynomial.rootSet L} :=
  Equiv.ofBijective (fun j => ⟨rootAt j, rootAt_mem j⟩)
    ⟨fun x y h => rootAt_injective (congrArg Subtype.val h), by
      rintro ⟨z, hz⟩
      rcases (mem_iff_marked_root z).mp hz with rfl | rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨3, rfl⟩⟩

private def autOnRoots (σ : L ≃ₐ[ℚ] L) :
    Equiv.Perm {z : L // z ∈ QuarticModel.rationalPolynomial.rootSet L} where
  toFun z := ⟨σ z.val, rootSet_mapsTo σ.toAlgHom z.property⟩
  invFun z := ⟨σ.symm z.val, rootSet_mapsTo σ.symm.toAlgHom z.property⟩
  left_inv z := Subtype.ext (σ.symm_apply_apply z.val)
  right_inv z := Subtype.ext (σ.apply_symm_apply z.val)

def rootPermutation (σ : L ≃ₐ[ℚ] L) : Equiv.Perm (ZMod 4) :=
  rootIndexEquiv.trans ((autOnRoots σ).trans rootIndexEquiv.symm)

theorem rootAt_permutation (σ : L ≃ₐ[ℚ] L) (j : ZMod 4) :
    rootAt (rootPermutation σ j) = σ (rootAt j) :=
  congrArg Subtype.val (rootIndexEquiv.apply_symm_apply (autOnRoots σ (rootIndexEquiv j)))

theorem rootPermutation_add_two (σ : L ≃ₐ[ℚ] L) (j : ZMod 4) :
    rootPermutation σ (j + 2) = rootPermutation σ j + 2 := by
  apply rootAt_injective
  simp only [rootAt_permutation, rootAt_add_two, map_neg]

/-- The permutations of the marked indices associated to Mathlib's
rotation and reflection conventions for the dihedral group. -/
def d4Action (g : GaussianClosureGroup) (j : ZMod 4) : ZMod 4 :=
  match g with
  | .r a => j + a
  | .sr a => -(j + a)

private theorem d4Action_mul (g h : GaussianClosureGroup) (j : ZMod 4) :
    d4Action (g * h) j = d4Action g (d4Action h j) := by
  cases g <;> cases h <;> simp [d4Action] <;> ring

private theorem d4Action_add_two (g : GaussianClosureGroup) (j : ZMod 4) :
    d4Action g (j + 2) = d4Action g j + 2 := by
  revert g j
  decide +kernel

private theorem d4Action_eq (g h : GaussianClosureGroup) :
    (∀ j, d4Action g j = d4Action h j) → g = h := by
  revert g h
  decide +kernel

private theorem rootIndex_agree {f g : ZMod 4 → ZMod 4}
    (hf : ∀ j, f (j + 2) = f j + 2) (hg : ∀ j, g (j + 2) = g j + 2)
    (h₀ : f 0 = g 0) (h₁ : f 1 = g 1) : ∀ j, f j = g j := by
  have h₂ : f 2 = g 2 := by
    have he : f (0 + 2) = g (0 + 2) := by rw [hf, hg, h₀]
    simpa only [zero_add] using he
  have h₃ : f 3 = g 3 := by
    have he : f (1 + 2) = g (1 + 2) := by rw [hf, hg, h₁]
    exact he
  intro j
  fin_cases j
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃

private theorem d4Label_exists (π : Equiv.Perm (ZMod 4))
    (hπ : ∀ j, π (j + 2) = π j + 2) : ∃ g, ∀ j, d4Action g j = π j := by
  have hStep : ∀ a b : ZMod 4, b ≠ a → b ≠ a + 2 →
      b = a + 1 ∨ b = a - 1 := by decide +kernel
  have h₀ : π 1 ≠ π 0 := fun h => (by decide : (1 : ZMod 4) ≠ 0) (π.injective h)
  have h₂ : π 1 ≠ π 0 + 2 := by
    intro h
    have he : π 2 = π 0 + 2 := by simpa only [zero_add] using hπ 0
    exact (by decide : (1 : ZMod 4) ≠ 2) (π.injective (h.trans he.symm))
  rcases hStep (π 0) (π 1) h₀ h₂ with h | h
  · refine ⟨.r (π 0), rootIndex_agree (d4Action_add_two _) hπ ?_ ?_⟩
    · simp [d4Action]
    · rw [h]
      simp [d4Action, add_comm]
  · refine ⟨.sr (-(π 0)), rootIndex_agree (d4Action_add_two _) hπ ?_ ?_⟩
    · simp [d4Action]
    · rw [h]
      simp [d4Action]
      ring

private noncomputable def d4Label (σ : L ≃ₐ[ℚ] L) : GaussianClosureGroup :=
  (d4Label_exists (rootPermutation σ) (rootPermutation_add_two σ)).choose

private theorem d4Label_action (σ : L ≃ₐ[ℚ] L) (j : ZMod 4) :
    d4Action (d4Label σ) j = rootPermutation σ j :=
  (d4Label_exists (rootPermutation σ) (rootPermutation_add_two σ)).choose_spec j

def closureGaloisLabels : (L ≃ₐ[ℚ] L) →* GaussianClosureGroup where
  toFun := d4Label
  map_one' := by
    apply d4Action_eq
    intro j
    apply rootAt_injective
    rw [d4Label_action, rootAt_permutation]
    change rootAt j = rootAt (d4Action (.r 0) j)
    simp only [d4Action, add_zero]
  map_mul' σ τ := by
    apply d4Action_eq
    intro j
    apply rootAt_injective
    rw [d4Label_action, rootAt_permutation, d4Action_mul, d4Label_action, d4Label_action,
      rootAt_permutation, rootAt_permutation]
    rfl

theorem closureGaloisLabels_on_root (σ : L ≃ₐ[ℚ] L) (j : ZMod 4) :
    rootAt (d4Action (closureGaloisLabels σ) j) = σ (rootAt j) := by
  change rootAt (d4Action (d4Label σ) j) = σ (rootAt j)
  rw [d4Label_action, rootAt_permutation]

theorem closureGaloisLabels_injective : Function.Injective closureGaloisLabels := by
  intro σ τ h
  have hh (j : ZMod 4) : σ (rootAt j) = τ (rootAt j) := by
    rw [← closureGaloisLabels_on_root σ, ← closureGaloisLabels_on_root τ, h]
  have he : σ.toAlgHom = τ.toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top adjoin_marked_roots
    intro z hz
    rcases (by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hz : z = alpha ∨ z = beta)
      with rfl | rfl
    · exact hh 0
    · exact hh 1
  apply AlgEquiv.ext
  intro z
  exact DFunLike.congr_fun he z

/-- The actual quartic's degree-eight splitting field has the marked \(D_4\) group. -/
def closureGaloisEquiv : (L ≃ₐ[ℚ] L) ≃* GaussianClosureGroup := by
  let : Fintype (L ≃ₐ[ℚ] L) := Fintype.ofFinite _
  refine MulEquiv.ofBijective closureGaloisLabels ?_
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨closureGaloisLabels_injective, ?_⟩
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ L, degree_eight, DihedralGroup.card]

theorem central_negates_marked_roots :
    closureGaloisEquiv.symm gaussianCentralElement alpha = -alpha ∧
      closureGaloisEquiv.symm gaussianCentralElement beta = -beta := by
  let σ := closureGaloisEquiv.symm gaussianCentralElement
  have hLabel : closureGaloisLabels σ = gaussianCentralElement :=
    closureGaloisEquiv.apply_symm_apply _
  have h0 := closureGaloisLabels_on_root σ (0 : ZMod 4)
  have h1 := closureGaloisLabels_on_root σ (1 : ZMod 4)
  rw [hLabel] at h0 h1
  exact ⟨h0.symm, h1.symm⟩

/-- The exact marked action on the ring of integers of the splitting field. -/
def integerAction : GaussianClosureGroup →* (𝓞 L ≃+* 𝓞 L) where
  toFun g := RingOfIntegers.mapRingEquiv (closureGaloisEquiv.symm g).toRingEquiv
  map_one' := by
    apply RingEquiv.ext
    intro z
    apply Subtype.ext
    change closureGaloisEquiv.symm 1 (z : L) = z
    rw [map_one]
    rfl
  map_mul' g h := by
    apply RingEquiv.ext
    intro z
    apply Subtype.ext
    change closureGaloisEquiv.symm (g * h) (z : L) =
      closureGaloisEquiv.symm g (closureGaloisEquiv.symm h (z : L))
    rw [map_mul]
    rfl

#print axioms rootIndexEquiv
#print axioms closureGaloisEquiv
#print axioms central_negates_marked_roots
#print axioms integerAction

end
end GaussianQuarticClosure
end AlpogeSuperZeta
