import QuarticConductorSign
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace AlpogeSuperZeta

open Complex Filter Set QuarticModel FieldCoefficientTransfer
open scoped Topology

/-- The rational cofactor is the nontrivial character mod four. -/
theorem quartic_beta_character_ne_one : chi4 ≠ 1 := by
  intro he
  have h := congrArg (fun χ : DirichletCharacter ℂ 4 => χ (3 : ZMod 4)) he
  have hχ : chi4 (3 : ZMod 4) = -1 := by
    change ((ZMod.χ₄ (3 : ZMod 4) : ℤ) : ℂ) = -1
    rw [show ZMod.χ₄ (3 : ZMod 4) = -1 from ZMod.χ₄_nat_three_mod_four (n := 3) rfl]
    norm_num
  have hsq : (3 : ZMod 4) * 3 = 1 := by decide
  have hu : IsUnit (3 : ZMod 4) := ⟨⟨3, 3, hsq, hsq⟩, rfl⟩
  change chi4 (3 : ZMod 4) = (1 : DirichletCharacter ℂ 4) (3 : ZMod 4) at h
  rw [hχ, MulChar.one_apply hu] at h
  norm_num at h

/-- Identify the endpoint used in Alpöge's pole construction by matching
the analytic class number limit to the actual field factorization. -/
theorem quartic_cofactor_product_at_one :
    chi4.LFunction 1 * archivedGaussianFactor 1 =
      (NumberField.dedekindZeta_residue QuarticModel.K : ℂ) := by
  have hc : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
    intro x hx
    change (x : ℂ) ≠ 1
    exact_mod_cast (ne_of_gt (show 1 < x from hx))
  have hcn : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) :=
    hc.mono_right nhdsWithin_le_nhds
  have hζ := riemannZeta_residue_one.comp hc
  have hb := (DirichletCharacter.differentiableAt_LFunction chi4 1
    (Or.inr quartic_beta_character_ne_one)).continuousAt.tendsto.comp hcn
  have hg := (archivedGaussianFactor_entire 1).continuousAt.tendsto.comp hcn
  have hmodel := (hζ.mul hb).mul hg
  have hfield := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT QuarticModel.K
  have hx : ∀ᶠ x : ℝ in 𝓝[>] (1 : ℝ), x ∈ Ioi (1 : ℝ) := eventually_mem_nhdsWithin
  refine tendsto_nhds_unique ?_ hfield
  refine (show Tendsto _ _ (𝓝 (chi4.LFunction 1 * archivedGaussianFactor 1)) from
    by simpa only [one_mul] using hmodel).congr' ?_
  filter_upwards [hx] with x hxr
  have hw : 1 < (x : ℂ).re := by simpa using (show 1 < x from hxr)
  change ((x : ℂ) - 1) * riemannZeta (x : ℂ) * chi4.LFunction (x : ℂ) *
      archivedGaussianFactor (x : ℂ) =
    ((x : ℂ) - 1) * NumberField.dedekindZeta QuarticModel.K (x : ℂ)
  rw [← archivedQuarticZeta_isDedekind.2 _ hw, archivedQuarticZeta]
  ring

theorem quartic_gaussian_one_ne_zero : archivedGaussianFactor 1 ≠ 0 := by
  intro he
  have hv := quartic_cofactor_product_at_one
  rw [he, mul_zero] at hv
  exact (Complex.ofReal_ne_zero.mpr
    (NumberField.dedekindZeta_residue_ne_zero QuarticModel.K)) hv.symm

#print axioms quartic_cofactor_product_at_one
#print axioms quartic_gaussian_one_ne_zero

end AlpogeSuperZeta
