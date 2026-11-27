import DedekindDiscriminant23EulerProduct
import DedekindZetaZeroFree.LFunctions.Dedekind.IdealClassConeSeries

namespace FieldTarget

open scoped NumberField nonZeroDivisors
open NumberField
open DedekindZetaZeroFree.AbelianQuotient.Theta

noncomputable section

local notation "F23" => (discriminant23QuadraticSubfield : Type)
local notation "I23" => (Ideal (𝓞 F23))⁰
local notation "C23" => ClassGroup (𝓞 F23)

private theorem norm_classCharacter (C : C23) : ‖discriminant23ClassCharacter C‖ = 1 := by
  apply Complex.norm_eq_one_of_pow_eq_one (n := 3) _ (by decide)
  rw [← discriminant23_class_number, ← map_pow]
  exact congrArg discriminant23ClassCharacter (pow_card_eq_one (x := C)) |>.trans
    (map_one discriminant23ClassCharacter)

/-- The actual character series groups into the ideal-class Dirichlet series
that are read by the class theta Mellin transform. -/
theorem discriminant23_classSeries_eq_sum_partial (k : ℕ) {w : ℂ} (hw : 1 < w.re) :
    discriminant23ClassSeries k w =
      ∑ C : C23, discriminant23ClassCharacter C ^ k * partialDedekindZeta F23 C w := by
  classical
  let f : I23 → ℂ := fun I ↦
    discriminant23ClassCharacter (ClassGroup.mk0 I) ^ k *
      ((I.val.absNorm : ℂ) ^ (-w))
  let f0 : Ideal (𝓞 F23) → ℂ := fun I ↦
    discriminant23ClassWeight k I * ((I.absNorm : ℂ) ^ (-w))
  have hSupp : Function.support f0 ⊆ {I | I ≠ ⊥} := by
    intro I hI hb
    subst I
    apply hI
    simp [f0, discriminant23ClassWeight]
  let e : I23 ≃ {I : Ideal (𝓞 F23) // I ≠ ⊥} :=
    Equiv.subtypeEquivRight (fun I ↦ mem_nonZeroDivisors_iff_ne_zero)
  have hReindex : (∑' I : I23, f I) = discriminant23ClassSeries k w := by
    unfold discriminant23ClassSeries
    change (∑' I : I23, f I) = ∑' I : Ideal (𝓞 F23), f0 I
    rw [← tsum_subtype_eq_of_support_subset hSupp]
    calc
      (∑' I : I23, f I) = ∑' I : I23, f0 (e I).val := by
        apply tsum_congr
        intro I
        have hI : I.val ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
        change f I = f0 I.val
        simp [f, f0, discriminant23ClassWeight, hI]
      _ = _ := e.tsum_eq fun I ↦ f0 I.val
  have hf : Summable f := by
    have hbase := DedekindZetaZeroFree.Odlyzko.summable_norm_idealInverseNormPower F23 hw
    have h := hbase.comp_injective
      (show Function.Injective (fun I : I23 ↦ I.val) from Subtype.val_injective)
    refine (h.congr ?_).of_norm
    intro I
    change ‖DedekindZetaZeroFree.Odlyzko.idealInverseNormPower F23 w I.val‖ = ‖f I‖
    rw [DedekindZetaZeroFree.Odlyzko.idealInverseNormPower_of_ne_zero F23 w
      (nonZeroDivisors.coe_ne_zero I)]
    simp only [f, norm_mul, norm_pow, norm_classCharacter, one_pow, one_mul]
  let c : I23 → C23 := ClassGroup.mk0
  have h := hf.hasSum.tsum_fiberwise c
  have hClass (C : C23) :
      (∑' I : c ⁻¹' {C}, f I.val) =
        discriminant23ClassCharacter C ^ k * partialDedekindZeta F23 C w := by
    refine ((hasSum_inverseIdealClass_inverseNormPower F23 C hw).mul_left
      (discriminant23ClassCharacter C ^ k)).congr_fun ?_ |>.tsum_eq
    intro I
    have hI : ClassGroup.mk0 I.val = C := I.property
    simp [f, hI]
  simpa only [hClass, hReindex, tsum_fintype] using h.tsum_eq.symm

#check @discriminant23_classSeries_eq_sum_partial
#print axioms discriminant23_classSeries_eq_sum_partial

end
end FieldTarget
