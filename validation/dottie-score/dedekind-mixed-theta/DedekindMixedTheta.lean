import DedekindFieldInputs
import DedekindFieldUniverses
import DedekindZetaZeroFree.LFunctions.Dedekind.HolomorphicContinuation
import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.WeakPairPoleClearing
import DedekindZetaZeroFree.Theta.Inversion.MixedPairGlobalSelfDuality

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex
open DedekindZetaZeroFree.AbelianQuotient
open scoped ComplexConjugate

private theorem gammaReciprocal_eq_inv (K : Type) [Field K] [NumberField K] (w : ℂ) :
    zetaGammaReciprocal K w = (dedekindGammaFactor K w)⁻¹ := by
  rw [zetaGammaReciprocal, dedekindGammaFactor,
    show -w / 2 = -(w / 2) by ring, Complex.cpow_neg]
  simp only [mul_inv_rev, inv_pow]
  ac_rfl

/-- The mixed theta Mellin transform completes the ideal-counting continuation. -/
theorem exists_dedekind_continuation_with_mixedTheta
    (K : Type) [Field K] [NumberField K] :
    ∃ Z : ℂ → ℂ, IsDedekindZeta K Z ∧
      ∀ w : ℂ, 0 < w.re → w.re < 1 →
        dedekindGammaFactor K w * Z w = (Theta.mixedThetaPair K).Λ w := by
  let P : WeakFEPair ℂ := Theta.mixedThetaPair K
  have hk : P.k = 1 := Theta.mixedThetaPair_k K
  obtain ⟨u, hu, hqu⟩ :=
    entire_division_at_zero (zetaGammaReciprocal K)
      (zetaGammaReciprocal_differentiable K) (zetaGammaReciprocal_zero K)
  let Z : ℂ → ℂ := fun w => zetaGammaReciprocal K w * P.Λ₀ w - u w * P.f₀
    - zetaGammaReciprocal K w * (P.ε / (1 - w)) * P.g₀
  have hZ : DifferentiableOn ℂ Z ({1}ᶜ : Set ℂ) ∧
      ∀ w : ℂ, w ≠ 0 → w ≠ 1 → Z w = zetaGammaReciprocal K w * P.Λ w :=
    weakFE_uncompletion P hk (zetaGammaReciprocal K) u
      (zetaGammaReciprocal_differentiable K) hu hqu
  have hCompleted (w : ℂ) (hwpos : 0 < w.re) (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
      dedekindGammaFactor K w * Z w = P.Λ w := by
    rw [hZ.2 w hw0 hw1, gammaReciprocal_eq_inv, ← mul_assoc,
      mul_inv_cancel₀ (dedekindGammaFactor_ne_zero K hwpos), one_mul]
  refine ⟨Z, ⟨hZ.1, ?_⟩, ?_⟩
  · intro w hw
    have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw
    have hw1 : w ≠ 1 := by rintro rfl; norm_num at hw
    have hm : P.Λ w = zetaGammaFactor K w * NumberField.dedekindZeta K w :=
      (P.hasMellin (s := w) (by rwa [hk])).2.symm.trans
        (Theta.hasMellin_mixedThetaPair K hw).2
    rw [hZ.2 w hw0 hw1, hm, ← mul_assoc, zetaGammaReciprocal_mul_factor K w hw, one_mul]
  intro w hw₀ hw₁
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw₀
  have hw1 : w ≠ 1 := by rintro rfl; norm_num at hw₁
  exact hCompleted w hw₀ hw0 hw1

/-- The same mixed theta pair supplies both the continuing function and its
completed functional equation, including for fields with real places. -/
theorem exists_dedekind_continuation_with_functionalEquation
    (K : Type) [Field K] [NumberField K] :
    ∃ Z : ℂ → ℂ, IsDedekindZeta K Z ∧
      ∀ w : ℂ, 0 < w.re → w.re < 1 →
        dedekindGammaFactor K (1 - w) * Z (1 - w) = dedekindGammaFactor K w * Z w := by
  let P := Theta.mixedThetaPair K
  have hk : P.k = 1 := Theta.mixedThetaPair_k K
  obtain ⟨Z, hZ, hMellin⟩ := exists_dedekind_continuation_with_mixedTheta K
  refine ⟨Z, hZ, ?_⟩
  intro w hw₀ hw₁
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw₀
  have hw1 : w ≠ 1 := by rintro rfl; norm_num at hw₁
  have hpos : 0 < (1 - w).re := by simp; linarith
  have hlt : (1 - w).re < 1 := by simp; linarith
  rw [hMellin _ hpos hlt, hMellin _ hw₀ hw₁]
  exact (DedekindZetaZeroFree.Hecke.weakFEPair_selfDual_reflection P hk
    (DedekindZetaZeroFree.Hecke.mixedThetaPair_global_selfDual K)
    (DedekindZetaZeroFree.Hecke.mixedThetaPair_global_g₀_eq_f₀ K)
    (DedekindZetaZeroFree.Hecke.mixedThetaPair_global_ε_eq_one K) w hw0 hw1).symm

/-- Clearing both simple poles leaves the same constant at every candidate point. -/
theorem mixedTheta_completion_eq_sub
    (K : Type) [Field K] [NumberField K] {Z : ℂ → ℂ} (hZ : IsDedekindZeta K Z)
    (w : ℂ) (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    w * (1 - w) * (dedekindGammaFactor K w * Z w) =
      w * (1 - w) * (Theta.mixedThetaPair K).Λ₀ w - (Theta.mixedThetaPair K).f₀ := by
  let P := Theta.mixedThetaPair K
  have hk : P.k = 1 := Theta.mixedThetaPair_k K
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw₀
  have hw1 : w ≠ 1 := by rintro rfl; norm_num at hw₁
  obtain ⟨W, hW, hMellin⟩ := exists_dedekind_continuation_with_mixedTheta K
  rw [continuation_eq_off_one hZ hW hw1, hMellin w hw₀ hw₁]
  change w * (1 - w) * P.Λ w = w * (1 - w) * P.Λ₀ w - P.f₀
  calc
    _ = -DedekindZetaZeroFree.Hecke.poleCleared P w := by
      rw [DedekindZetaZeroFree.Hecke.poleCleared_eq P hk w hw0 hw1]
      ring
    _ = _ := by
      have hg : P.g₀ = P.f₀ := DedekindZetaZeroFree.Hecke.mixedThetaPair_global_g₀_eq_f₀ K
      have he : P.ε = 1 := DedekindZetaZeroFree.Hecke.mixedThetaPair_global_ε_eq_one K
      rw [DedekindZetaZeroFree.Hecke.poleCleared, hg, he]
      ring

/-- The concrete normalized Mellin reading equals its constant precisely at
a zero of the Dedekind continuation, with the same complex input. -/
theorem mixedTheta_reading_eq_iff_zero
    (K : Type) [Field K] [NumberField K] {Z : ℂ → ℂ} (hZ : IsDedekindZeta K Z)
    (w : ℂ) (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    w * (1 - w) * (Theta.mixedThetaPair K).Λ₀ w = (Theta.mixedThetaPair K).f₀ ↔
      Z w = 0 := by
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hw₀
  have hw1 : w ≠ 1 := by rintro rfl; norm_num at hw₁
  have hscale : w * (1 - w) ≠ 0 := mul_ne_zero hw0 (sub_ne_zero.mpr hw1.symm)
  calc
    _ ↔ w * (1 - w) * (Theta.mixedThetaPair K).Λ₀ w - (Theta.mixedThetaPair K).f₀ = 0 :=
      sub_eq_zero.symm
    _ ↔ _ := by
      rw [← mixedTheta_completion_eq_sub K hZ w hw₀ hw₁]
      simp [hscale, dedekindGammaFactor_ne_zero K hw₀]

/-- The horizontal zero reflection holds for a continuing function of any number
field, with no restriction on its Lean universe. -/
theorem exists_dedekind_continuation_with_reflection
    (K : Type*) [Field K] [NumberField K] :
    ∃ Z : ℂ → ℂ, IsDedekindZeta K Z ∧
      ∀ w : ℂ, 0 < w.re → w.re < 1 → Z w = 0 → Z (1 - conj w) = 0 := by
  apply exists_dedekind_continuation_of_small_fields
  intro F _ _
  obtain ⟨Z, hZ, hFE⟩ := exists_dedekind_continuation_with_functionalEquation F
  exact ⟨Z, hZ, continuation_reflects_zeros_of_functionalEquation hZ hFE⟩

#print axioms exists_dedekind_continuation_with_mixedTheta
#print axioms exists_dedekind_continuation_with_functionalEquation
#print axioms mixedTheta_completion_eq_sub
#print axioms mixedTheta_reading_eq_iff_zero
#print axioms exists_dedekind_continuation_with_reflection

end FieldTarget
