import Discriminant23GaussHeat
import GaussianFixedPointHorner
import Discriminant23ClassMellinTruncation

namespace FieldTarget

open Complex Finset

noncomputable section

set_option exponentiation.threshold 512

def gaussThetaForm (principal : Bool) : ℤ → ℤ → ℤ :=
  if principal then discriminant23PrincipalForm else discriminant23OtherForm

private def principalCoeffs : Array ℕ := #[
  0, 2, 0, 0, 2, 0, 4, 0, 4, 2, 0, 0,
  4, 0, 0, 0, 2, 0, 4, 0, 0, 0, 0, 2,
  4, 2, 4, 4, 0, 0, 0, 0, 4, 0, 0, 0,
  6, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, 0,
  8, 2, 0, 0, 4, 0, 4, 0, 0, 0, 4, 4,
  0, 0, 4, 0, 6, 0, 0, 0, 0, 0, 0, 0,
  8, 0, 0, 0, 0, 0, 4, 0, 0
]

private def otherCoeffs : Array ℕ := #[
  0, 0, 2, 2, 2, 0, 2, 0, 2, 2, 0, 0,
  4, 2, 0, 0, 4, 0, 4, 0, 0, 0, 0, 0,
  6, 0, 2, 2, 0, 2, 0, 2, 4, 0, 0, 0,
  6, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 2,
  6, 0, 2, 0, 4, 0, 6, 0, 0, 0, 2, 0,
  0, 0, 2, 0, 4, 0, 0, 0, 0, 2, 0, 2,
  8, 2, 0, 2, 0, 0, 6, 0, 0
]

def gaussThetaCoeff (principal : Bool) (k : ℕ) : ℕ :=
  (if principal then principalCoeffs else otherCoeffs)[k]?.getD 0

private def thetaMultiplicity (principal : Bool) (k : ℕ) : ℕ :=
  ((characterThetaTermsUpTo (gaussThetaForm principal) 80).filter
    (fun xy ↦ (gaussThetaForm principal xy.1 xy.2).toNat = k)).card

set_option maxRecDepth 4096 in
private theorem principal_coefficients_checked :
    ∀ k : Fin 81, gaussThetaCoeff true k = thetaMultiplicity true k := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem other_coefficients_checked :
    ∀ k : Fin 81, gaussThetaCoeff false k = thetaMultiplicity false k := by
  decide +kernel

theorem gaussThetaPolynomial_eq (principal : Bool) (q : ℂ) :
    (∑ xy ∈ characterThetaTermsUpTo (gaussThetaForm principal) 80,
      q ^ (gaussThetaForm principal xy.1 xy.2).toNat) =
      ∑ k ∈ range 81, (gaussThetaCoeff principal k : ℂ) * q ^ k := by
  let Q := gaussThetaForm principal
  have hMap : ∀ xy ∈ characterThetaTermsUpTo Q 80, (Q xy.1 xy.2).toNat ∈ range 81 := by
    intro xy hxy
    rw [characterThetaTermsUpTo] at hxy
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hxy).2.2)
  rw [← sum_fiberwise_of_maps_to' hMap (fun k ↦ q ^ k)]
  apply sum_congr rfl
  intro k hk
  rw [sum_const, nsmul_eq_mul]
  have hCount : gaussThetaCoeff principal k = thetaMultiplicity principal k := by
    cases principal
    · exact other_coefficients_checked ⟨k, mem_range.mp hk⟩
    · exact principal_coefficients_checked ⟨k, mem_range.mp hk⟩
  rw [hCount]
  rfl

private theorem thetaCoeff_moment_le (principal : Bool) :
    (∑ k ∈ range 81, (k : ℝ) * ‖(gaussThetaCoeff principal k : ℂ)‖) ≤ 4500 := by
  simp only [← Complex.ofReal_natCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  have h : (∑ k ∈ range 81, k * gaussThetaCoeff principal k) ≤ 4500 := by
    cases principal <;> decide +kernel
  exact_mod_cast h

def gaussPanelHeat (p : ℕ) (i : Fin 24) : ℝ :=
  Real.exp (-discriminant23ThetaScale * Real.exp (gaussPanelNode p i))

def gaussPanelHeatClippedNumerator (p : ℕ) (i : Fin 24) : ℤ :=
  max 0 (min (gaussExpScale : ℤ) (gaussPanelHeatNumerator p i))

private theorem clippedHeat_eq (p : ℕ) (i : Fin 24) :
    gaussExpGrid (gaussPanelHeatClippedNumerator p i) =
      max 0 (min 1 (gaussExpGrid (gaussPanelHeatNumerator p i))) := by
  have hScale : 0 < (gaussExpScale : ℝ) := by norm_num [gaussExpScale]
  have hInv : 0 ≤ (gaussExpScale : ℝ)⁻¹ := inv_nonneg.mpr hScale.le
  simp only [gaussExpGrid, gaussPanelHeatClippedNumerator, Int.cast_max, Int.cast_min,
    Int.cast_zero, Int.cast_natCast, div_eq_mul_inv, max_mul_of_nonneg _ _ hInv,
    min_mul_of_nonneg _ _ hInv, zero_mul, mul_inv_cancel₀ hScale.ne']

private theorem heat_mem_unit (p : ℕ) (i : Fin 24) :
    0 ≤ gaussPanelHeat p i ∧ gaussPanelHeat p i ≤ 1 := by
  have hC : 0 ≤ discriminant23ThetaScale :=
    (by positivity : (0 : ℝ) ≤ 445815737633141664182226312842035173730 / 2 ^ 128).trans
      discriminant23_thetaScale_dyadic_128.1
  exact ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) (Real.exp_nonneg _))⟩

private theorem clippedHeat_bounds {p : ℕ} (hp : p < 32) (i : Fin 24) :
    let r := gaussExpGrid (gaussPanelHeatClippedNumerator p i)
    0 ≤ r ∧ r ≤ 1 ∧ |gaussPanelHeat p i - r| ≤ 3 / 10 ^ 37 := by
  rw [clippedHeat_eq]
  let r := gaussExpGrid (gaussPanelHeatNumerator p i)
  have h : |gaussPanelHeat p i - r| ≤ (3 / 10 ^ 37 : ℝ) := discriminant23_gaussPanelHeat_error hp i
  have hU := heat_mem_unit p i
  refine ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _), abs_le.mpr ⟨?_, ?_⟩⟩
  · have hUpper : max 0 (min 1 r) ≤ gaussPanelHeat p i + 3 / 10 ^ 37 :=
      max_le (by linarith only [hU.1]) ((min_le_right _ _).trans (by linarith only [(abs_le.mp h).1]))
    linarith only [hUpper]
  · have hLower : gaussPanelHeat p i - 3 / 10 ^ 37 ≤ max 0 (min 1 r) :=
      (le_min (by linarith only [hU.2]) (by linarith only [(abs_le.mp h).2])).trans (le_max_right _ _)
    linarith only [hLower]

private theorem gaussianScaled_real (n : ℤ) :
    gaussianScaled ⟨n, 0⟩ gaussExpScale = (gaussExpGrid n : ℂ) := by
  simp [gaussianScaled, gaussExpGrid, GaussianInt.toComplex_def']

def gaussPanelThetaNumerator (principal : Bool) (p : ℕ) (i : Fin 24) : GaussianInt :=
  gaussianFixedPointHorner (fun k ↦ gaussThetaCoeff principal k)
    ⟨gaussPanelHeatClippedNumerator p i, 0⟩ gaussExpScale 0 81

def gaussThetaOfHeat (principal : Bool) (q : ℤ) : ℤ :=
  intFixedPointHorner (fun k ↦ gaussThetaCoeff principal k)
    (max 0 (min (gaussExpScale : ℤ) q)) gaussExpScale 0 81

theorem gaussPanelThetaNumerator_eq (principal : Bool) (p : ℕ) (i : Fin 24) :
    gaussPanelThetaNumerator principal p i =
      ⟨gaussThetaOfHeat principal (gaussPanelHeatNumerator p i), 0⟩ := by
  rw [gaussPanelThetaNumerator, gaussianFixedPointHorner_real_eq]
  rfl

/-- The exact theta polynomial at the real Gauss heat input is enclosed by
the dyadic value computed by Horner's rule. -/
theorem discriminant23_gaussPanelTheta_error (principal : Bool) {p : ℕ} (hp : p < 32) (i : Fin 24) :
    ‖(∑ xy ∈ characterThetaTermsUpTo (gaussThetaForm principal) 80,
      (gaussPanelHeat p i : ℂ) ^ (gaussThetaForm principal xy.1 xy.2).toNat) -
      gaussianScaled (gaussPanelThetaNumerator principal p i) gaussExpScale‖ ≤ 2 / 10 ^ 33 := by
  let q : ℂ := (gaussPanelHeat p i : ℂ)
  let v : ℂ := gaussianScaled ⟨gaussPanelHeatClippedNumerator p i, 0⟩ gaussExpScale
  obtain ⟨hv₀, hv₁, hvE⟩ := clippedHeat_bounds hp i
  have hq : ‖q‖ ≤ 1 := by
    dsimp only [q]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (heat_mem_unit p i).1]
    exact (heat_mem_unit p i).2
  have hv : ‖v‖ ≤ 1 := by
    dsimp only [v]
    rw [gaussianScaled_real, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv₀]
    exact hv₁
  have hE : ‖q - v‖ ≤ (3 / 10 ^ 37 : ℝ) := by
    dsimp only [q, v]
    rw [gaussianScaled_real, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hvE
  have h₁ := norm_polynomial_sub_le_on_unit_disk (fun k ↦ (gaussThetaCoeff principal k : ℂ)) 81 hq hv
  have hModel := h₁.trans (mul_le_mul (thetaCoeff_moment_le principal) hE (norm_nonneg _) (by norm_num))
  have h₂ := norm_polynomial_sub_gaussianFixedPointHorner_le
    (fun k ↦ (gaussThetaCoeff principal k : ℤ)) ⟨gaussPanelHeatClippedNumerator p i, 0⟩
    (s := gaussExpScale) (by norm_num [gaussExpScale]) hv 0 81
  have hRound : ‖(∑ k ∈ range 81, (gaussThetaCoeff principal k : ℂ) * v ^ k) -
      gaussianScaled (gaussPanelThetaNumerator principal p i) gaussExpScale‖ ≤
      81 * (2 / (gaussExpScale : ℝ)) := by
    simpa only [zero_add, Int.cast_natCast, Nat.cast_ofNat, v, gaussPanelThetaNumerator] using h₂
  rw [gaussThetaPolynomial_eq]
  calc
    _ ≤ ‖(∑ k ∈ range 81, (gaussThetaCoeff principal k : ℂ) * q ^ k) -
          ∑ k ∈ range 81, (gaussThetaCoeff principal k : ℂ) * v ^ k‖ +
        ‖(∑ k ∈ range 81, (gaussThetaCoeff principal k : ℂ) * v ^ k) -
          gaussianScaled (gaussPanelThetaNumerator principal p i) gaussExpScale‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        ((∑ k ∈ range 81, (gaussThetaCoeff principal k : ℂ) * q ^ k) -
          ∑ k ∈ range 81, (gaussThetaCoeff principal k : ℂ) * v ^ k)
        ((∑ k ∈ range 81, (gaussThetaCoeff principal k : ℂ) * v ^ k) -
          gaussianScaled (gaussPanelThetaNumerator principal p i) gaussExpScale)
    _ ≤ _ := (add_le_add hModel hRound).trans (by norm_num [gaussExpScale])

#print axioms gaussThetaPolynomial_eq
#print axioms discriminant23_gaussPanelTheta_error

end
end FieldTarget
