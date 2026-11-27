import DedekindMixedThetaFactorSlope
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

namespace FieldTarget

set_option autoImplicit false

open Complex NumberField
open DedekindZetaZeroFree.AbelianQuotient

/-- The Gaussian quadratic field, with `i` a primitive fourth root of unity. -/
abbrev GaussianQuadraticField := CyclotomicField 4 ℚ

theorem gaussianQuadratic_isCyclotomic : IsCyclotomicExtension {4} ℚ GaussianQuadraticField := by
  let _ : NeZero (4 : ℚ) := ⟨by norm_num⟩
  exact CyclotomicField.isCyclotomicExtension 4 ℚ

attribute [local instance] gaussianQuadratic_isCyclotomic

theorem gaussianQuadratic_discr : NumberField.discr GaussianQuadraticField = -4 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : IsCyclotomicExtension {(2 : ℕ)^2} ℚ GaussianQuadraticField := gaussianQuadratic_isCyclotomic
  have h := IsCyclotomicExtension.Rat.discr_prime_pow 2 2 GaussianQuadraticField
  have hp : (2 : ℕ)^2 = 4 := by decide
  have ht : Nat.totient 4 = 2 := by decide
  norm_num [hp, ht] at h
  exact h

theorem gaussianQuadratic_signature :
    InfinitePlace.nrRealPlaces GaussianQuadraticField = 0 ∧
      InfinitePlace.nrComplexPlaces GaussianQuadraticField = 1 := by
  refine ⟨IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero GaussianQuadraticField
    (n := 4) (by decide), ?_⟩
  have h := IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two
    4 GaussianQuadraticField
  have ht : Nat.totient 4 = 2 := by decide
  simpa [ht] using h

theorem gaussianQuadratic_completionRatio {w : ℂ} (hw : 0 < w.re) :
    zetaGammaFactor GaussianQuadraticField w / Gammaℝ w = (4 : ℂ)^(w / 2) * Gammaℝ (w + 1) := by
  have hA : zetaGammaFactor GaussianQuadraticField w = (4 : ℂ)^(w / 2) * Gammaℂ w := by
    norm_num [zetaGammaFactor, gaussianQuadratic_discr, gaussianQuadratic_signature.1,
      gaussianQuadratic_signature.2]
  rw [hA, ← Gammaℝ_mul_Gammaℝ_add_one]
  exact (div_eq_iff (Gammaℝ_ne_zero_of_re_pos hw)).2 (by ring)

/-- The standard mod-four Dirichlet beta character in the field factorization. -/
def gaussianQuadraticChar : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

private theorem gaussianQuadraticChar_ne_one : gaussianQuadraticChar ≠ 1 := by
  intro h
  have hthree : IsUnit (3 : ZMod 4) := by decide
  have hχ : ZMod.χ₄ (3 : ZMod 4) = -1 := by decide
  have hv : gaussianQuadraticChar (3 : ZMod 4) = -1 := by
    change ((ZMod.χ₄ (3 : ZMod 4) : ℤ) : ℂ) = -1
    rw [hχ]
    norm_num
  have he : gaussianQuadraticChar (3 : ZMod 4) = 1 := by
    rw [h]
    exact MulChar.one_apply hthree
  rw [he] at hv
  norm_num at hv

/-- Beta together with the ratio of the Gaussian and rational completion factors. -/
noncomputable def gaussianQuadraticWeightedBeta (w : ℂ) : ℂ :=
  (4 : ℂ)^(w / 2) * Gammaℝ (w + 1) * gaussianQuadraticChar.LFunction w

theorem gaussianQuadraticWeightedBeta_differentiableOn :
    DifferentiableOn ℂ gaussianQuadraticWeightedBeta {w : ℂ | 0 < w.re} := by
  have hexp : Differentiable ℂ (fun w : ℂ ↦ (4 : ℂ) ^ (w / 2)) :=
    (differentiable_id.div_const (2 : ℂ)).const_cpow (Or.inl (by norm_num))
  have hΓ : DifferentiableOn ℂ (fun w : ℂ ↦ Gammaℝ (w + 1)) {w : ℂ | 0 < w.re} := by
    intro w hw
    have hr : 0 < (w + 1).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith [show 0 < w.re from hw]
    have hG : DifferentiableAt ℂ Gammaℝ (w + 1) := by
      have hi := (differentiable_Gammaℝ_inv (w + 1)).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hr))
      have he : (fun z : ℂ ↦ (Gammaℝ z)⁻¹)⁻¹ = Gammaℝ := by
        funext z
        exact inv_inv (Gammaℝ z)
      rwa [he] at hi
    have hshift : DifferentiableAt ℂ (fun z : ℂ ↦ z + 1) w :=
      (differentiable_id.add_const (1 : ℂ)) w
    exact (hG.comp w hshift).differentiableWithinAt
  exact (hexp.differentiableOn.mul hΓ).mul
    (DirichletCharacter.differentiable_LFunction gaussianQuadraticChar_ne_one).differentiableOn

/-- The exact Gaussian band input after the Euler-product identification. -/
theorem gaussianQuadratic_dottie_band_of_beta_slope
    (hEuler : ∀ w : ℂ, 1 < w.re →
      NumberField.dedekindZeta GaussianQuadraticField w =
        riemannZeta w * gaussianQuadraticChar.LFunction w)
    {L : ℝ} (hL : 0 ≤ L)
    (hslope : 2 * (gaussianQuadraticWeightedBeta 1 * completedRiemannZeta₀ 1 +
      deriv gaussianQuadraticWeightedBeta 1).re <
        ‖gaussianQuadraticWeightedBeta 1‖ / (1 + (L + 31/128)^2)) :
    HasFiniteDottieBoundaryCertificate (mixedThetaContinuation GaussianQuadraticField)
      (mixedThetaCompletedReading GaussianQuadraticField) (-L) L := by
  apply finite_dottie_boundary_of_dedekind_factor_slope GaussianQuadraticField
    gaussianQuadraticWeightedBeta gaussianQuadraticWeightedBeta_differentiableOn hEuler _ hL hslope
  intro w hw
  rw [gaussianQuadratic_completionRatio (lt_trans zero_lt_one hw)]
  rfl

#check @gaussianQuadratic_completionRatio
#check @gaussianQuadratic_dottie_band_of_beta_slope
#print axioms gaussianQuadratic_discr
#print axioms gaussianQuadratic_signature
#print axioms gaussianQuadratic_completionRatio
#print axioms gaussianQuadraticWeightedBeta_differentiableOn
#print axioms gaussianQuadratic_dottie_band_of_beta_slope

end FieldTarget
