import GaussianDyadicPairBounds

/-! A cofinal upper bound for the remaining signed interior pairs
supplies the positive-area criterion for the archived quartic. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open ArtinPrimitiveRootsConjecture FieldTarget MeasureTheory QuarticModel Set

noncomputable section

theorem archivedGaussianHermitePositiveArea_le_secondMoment
    (hDir : DirichletLZerosOnLine) {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) :
    ∃ B ≥ (0 : ℝ), ∀ U V : ℝ, Real.log (2 * ((archivedGaussianRationalLevel : ℝ) + 1)) ≤ U →
      U ≤ V →
      4 * (∫ u in Icc U V, archivedGaussianHermiteWeightedPositive θ u) ≤
        archivedGaussianDyadicSecondMoment θ U V + B * (V - U) := by
  obtain ⟨C, hC, hMass⟩ := dyadicFrobeniusLogMass_pair_main_term hDir hθ hθ₁
  refine ⟨1 + 2 * C, by positivity, fun U V hU hUV => ?_⟩
  have hD : (2 * (26509772707289 + 1) : ℝ) ≤ 2 * ((archivedGaussianRationalLevel : ℝ) + 1) := by
    norm_num [archivedGaussianRationalLevel]
  have hLog : Real.log (2 * (26509772707289 + 1)) ≤ U :=
    (Real.log_le_log (by norm_num) hD).trans hU
  have hPos := archivedGaussianHermiteWeightedPositive_integrableOn
    (θ := θ) (V := V) (by linarith) hLog
  have hM := archivedGaussianDyadicSecondMoment_integrableOn θ U V
  have hConst : IntegrableOn (fun _ : ℝ => 1 + 2 * C) (Icc U V) := integrableOn_const (by simp)
  have hInt : (∫ u in Icc U V, (archivedGaussianDyadicPrimeWindow (Real.exp u)) ^ 2 *
        Real.exp (-2 * θ * u) + (1 + 2 * C)) =
      archivedGaussianDyadicSecondMoment θ U V + (1 + 2 * C) * (V - U) := by
    rw [integral_add hM hConst, setIntegral_const, Real.volume_real_Icc_of_le hUV,
      smul_eq_mul, mul_comm (V - U) (1 + 2 * C)]
    rfl
  rw [← hInt, ← integral_const_mul]
  apply setIntegral_mono_on (hPos.const_mul _) (hM.add hConst) measurableSet_Icc
  intro u hu
  have hX : (2 * ((archivedGaussianRationalLevel : ℝ) + 1)) ≤ Real.exp u :=
    (Real.exp_log (by positivity : (0 : ℝ) < 2 * ((archivedGaussianRationalLevel : ℝ) + 1))).ge.trans
      (Real.exp_le_exp.mpr (hU.trans hu.1))
  have hE : 4 * archivedGaussianHermiteValueExcess (Real.exp u) ≤
      archivedGaussianDyadicPrimeWindow (Real.exp u) + 2 * C * (Real.exp u) ^ θ := by
    rw [archivedGaussianHermiteValueExcess_eq (hD.trans hX), archivedGaussianCentralPrimeExcess,
      archivedGaussianDyadicPrimeWindow_eq_frobenius (hD.trans hX)]
    linarith only [(abs_le.mp (hMass _ hX)).2]
  let a := archivedGaussianDyadicPrimeWindow (Real.exp u)
  let f := Real.exp (-θ * u)
  have hF : 0 ≤ f := Real.exp_nonneg _
  have hf : (Real.exp u) ^ θ * f = 1 := by
    dsimp only [f]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm u θ, ← Real.exp_add,
      show θ * u + -θ * u = 0 by ring, Real.exp_zero]
  have hs : (a * f) ^ 2 = a ^ 2 * Real.exp (-2 * θ * u) := by
    rw [mul_pow, pow_two f]
    dsimp only [f]
    rw [← Real.exp_add, show -θ * u + -θ * u = -2 * θ * u by ring]
  change 4 * (max 0 (archivedGaussianHermiteValueExcess (Real.exp u)) * f) ≤
    a ^ 2 * Real.exp (-2 * θ * u) + (1 + 2 * C)
  rw [← hs]
  rcases le_total 0 (archivedGaussianHermiteValueExcess (Real.exp u)) with h | h
  · rw [max_eq_right h, ← mul_assoc]
    calc
      _ ≤ (a + 2 * C * (Real.exp u) ^ θ) * f := mul_le_mul_of_nonneg_right hE hF
      _ = a * f + 2 * C := by rw [add_mul, mul_assoc (2 * C), hf, mul_one]
      _ ≤ _ := by nlinarith only [sq_nonneg (a * f - 1 / 2)]
  · rw [max_eq_left h, zero_mul, mul_zero]
    positivity

/-- A single fixed exponent and width with an arbitrarily late subpower
upper bound on the remaining signed pairs. -/
def ArchivedGaussianDyadicInteriorMomentBound (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U ≥ U₀,
    archivedGaussianDyadicInteriorMoment θ U ((1 + δ) * U) ≤ Real.exp (η * U)

theorem archivedGaussianHermiteAreaBound_of_dyadicInteriorMoment
    (hDir : DirichletLZerosOnLine) {θ δ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ)
    (hPairs : ArchivedGaussianDyadicInteriorMomentBound θ δ) :
    ArchivedGaussianHermiteAreaBound θ δ := by
  obtain ⟨B, hB, hArea⟩ := archivedGaussianHermitePositiveArea_le_secondMoment hDir hθ hθ₁
  obtain ⟨C, hC, hMoment⟩ := archivedGaussianDyadicSecondMoment_le_interior_add hθ
  intro η hη U₀
  let X₀ : ℝ := 2 * ((archivedGaussianRationalLevel : ℝ) + 1)
  let A := 2 + C + 2 * B * δ / η
  let start := max (max U₀ (Real.log X₀)) (2 * A / η)
  obtain ⟨U, hU, hPairsU⟩ := hPairs (η / 2) (by positivity) start
  have hUU₀ : U₀ ≤ U := (le_max_left _ _).trans ((le_max_left _ _).trans hU)
  have hLog : Real.log X₀ ≤ U := (le_max_right _ _).trans ((le_max_left _ _).trans hU)
  have hU₀ : 0 ≤ U := (Real.log_nonneg (by norm_num [X₀, archivedGaussianRationalLevel])).trans hLog
  have hWidth : U ≤ (1 + δ) * U := by nlinarith [mul_nonneg hδ.le hU₀]
  let e := Real.exp ((η / 2) * U)
  have he₁ : 1 ≤ e := Real.one_le_exp (by positivity)
  have he₀ : 0 ≤ e := Real.exp_nonneg _
  have he : (η / 2) * U ≤ e := by linarith [Real.add_one_le_exp ((η / 2) * U)]
  have hAe : A ≤ e := by
    have hSize : 2 * A / η ≤ U := (le_max_right _ _).trans hU
    have hA := (div_le_iff₀ hη).mp hSize
    exact (show A ≤ (η / 2) * U by linarith only [hA]).trans he
  have hBe : B * δ * U ≤ (2 * B * δ / η) * e := by
    have hEq : B * δ * U = (2 * B * δ / η) * ((η / 2) * U) := by
      field_simp [hη.ne']
    rw [hEq]
    exact mul_le_mul_of_nonneg_left he (by positivity)
  have hCe : C ≤ C * e := by simpa only [mul_one] using mul_le_mul_of_nonneg_left he₁ hC
  have hI :=
    (hArea U ((1 + δ) * U) hLog hWidth).trans
      (add_le_add (hMoment U ((1 + δ) * U)) (le_refl (B * ((1 + δ) * U - U))))
  have hBound : 4 * (∫ u in Icc U ((1 + δ) * U), archivedGaussianHermiteWeightedPositive θ u) ≤
      Real.exp (η * U) := by
    calc
      _ ≤ A * e := by dsimp only [A, e] at *; linarith only [hI, hBe, hCe, hPairsU]
      _ ≤ e * e := mul_le_mul_of_nonneg_right hAe he₀
      _ = _ := by dsimp only [e]; rw [← Real.exp_add]; congr 1; ring
  exact ⟨U, hUU₀, by linarith [Real.exp_nonneg (η * U)]⟩

theorem archivedQuarticZeta_strip_of_dyadicInteriorMoment
    (hDir : DirichletLZerosOnLine) {θ δ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ)
    (hPairs : ArchivedGaussianDyadicInteriorMomentBound θ δ)
    {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) (hw : archivedQuarticZeta w = 0) :
    1 - θ ≤ w.re ∧ w.re ≤ θ :=
  archivedQuarticZeta_strip_of_hermite_positive_area hDir hθ hθ₁ hδ
    (archivedGaussianHermiteAreaBound_of_dyadicInteriorMoment hDir hθ hθ₁ hδ hPairs) hw₀ hw₁ hw

theorem quartic_rh_of_dyadicInteriorMoment
    (hDir : DirichletLZerosOnLine)
    (hPairs : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ > 0, ArchivedGaussianDyadicInteriorMomentBound θ δ) :
    DedekindZetaRH QuarticModel.K := by
  apply quartic_rh_of_archived_gaussian_hermite_positive_area hDir
  intro θ hθ hθ₁
  obtain ⟨δ, hδ, hW⟩ := hPairs θ hθ hθ₁
  exact ⟨δ, hδ, archivedGaussianHermiteAreaBound_of_dyadicInteriorMoment hDir hθ hθ₁ hδ hW⟩

#print ArchivedGaussianDyadicInteriorMomentBound
#check archivedQuarticZeta_strip_of_dyadicInteriorMoment
#check quartic_rh_of_dyadicInteriorMoment
#print axioms archivedGaussianHermitePositiveArea_le_secondMoment
#print axioms archivedGaussianHermiteAreaBound_of_dyadicInteriorMoment
#print axioms archivedQuarticZeta_strip_of_dyadicInteriorMoment
#print axioms quartic_rh_of_dyadicInteriorMoment

end
end GaussianQuarticClosure
end AlpogeSuperZeta
