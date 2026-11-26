import GaussianWindowPort
import Mathlib.NumberTheory.LSeries.Positivity

/-! The real-pole premise of the window theorem holds for the actual quartic. -/
noncomputable section

namespace AlpogeSuperZeta

open Asymptotics Complex Filter Set Finset MeasureTheory QuarticModel FieldTarget ArtinPrimitiveRootsConjecture
open scoped ComplexOrder NumberField Topology

/-- The ideal-count asymptotic gives convergence to the right of one.
The coefficient of the unit ideal then makes each real value positive. -/
theorem dedekindZeta_positive_of_one_lt (F : Type*) [Field F] [NumberField F]
    {x : ℝ} (hx : 1 < x) : 0 < NumberField.dedekindZeta F (x:ℂ) := by
  let a (n : ℕ) : ℝ := Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = n}
  have ha₀ (n : ℕ) : 0 ≤ a n := Nat.cast_nonneg _
  have ha₁ : a 1 = 1 := by
    simp [a, Ideal.absNorm_eq_one_iff]
  have hlim : Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, a k) / (n:ℝ)) atTop
      (𝓝 (NumberField.dedekindZeta_residue F)) := by
    refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ F).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
    simp only [Function.comp_apply, Nat.cast_le, a, ← Nat.cast_sum]
    congr
    rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
      show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
      show 1 = Nat.card {I : Ideal (𝓞 F) // Ideal.absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
      Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
      ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
    simp [Set.coe_eq_subtype]
  have hconv : LSeries.abscissaOfAbsConv (fun n => (a n:ℂ)) ≤ (1:ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro s hs
    exact LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using hlim)) ha₀ zero_le_one hs
  have hpos := LSeries.positive (fun n => Complex.zero_le_real.mpr (ha₀ n))
    (show 0 < (a 1:ℂ) by simp [ha₁]) (x := x) (hconv.trans_lt (by exact_mod_cast hx))
  simpa [NumberField.dedekindZeta, a] using hpos

/-- A real zero of the archived Gaussian factor cannot be at or to the
right of one. The exact factorization gives the claim above one, and the
class-number residue gives it at one. -/
theorem gaussian_real_poles_lt_one (ρ : ℂ) (hp : ρ ∈ gaussianPoles) (hi : ρ.im = 0) :
    ρ.re < 1 := by
  by_contra! h
  have hre : (ρ.re:ℂ) = ρ := Complex.ext (by simp) (by simpa using hi.symm)
  rcases eq_or_lt_of_le h with he | hl
  · have hone : ρ = 1 := by rw [← hre, ← he, ofReal_one]
    exact quartic_gaussian_one_ne_zero (hone ▸ hp.2)
  · have hz : archivedQuarticZeta ρ = 0 := by simp [archivedQuarticZeta, hp.2]
    have hD : NumberField.dedekindZeta K (ρ.re:ℂ) = 0 := by
      rw [hre, ← archivedQuarticZeta_isDedekind.2 ρ hl]
      exact hz
    exact (dedekindZeta_positive_of_one_lt K hl).ne' hD

theorem quartic_rh_of_gaussian_ramp_checked_real_poles (hD : DirichletLZerosOnLine)
    (g : ℝ → ℝ) (hMeas : Measurable g)
    (hGrowth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2*u))
    (hLaplace : ∀ w : ℂ, 2 < w.re →
      gaussianPoleFormula w = ∫ u in Set.Ioi (0:ℝ), (g u:ℂ) * exp (-w*u))
    (hWindows : GaussianWindows g) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_gaussian_ramp hD g hMeas hGrowth hLaplace gaussian_real_poles_lt_one hWindows

#print axioms dedekindZeta_positive_of_one_lt
#print axioms gaussian_real_poles_lt_one
#print axioms quartic_rh_of_gaussian_ramp_checked_real_poles
#check quartic_rh_of_gaussian_ramp_checked_real_poles

end AlpogeSuperZeta
end
