import AlpogeAdapters
import GaussianEndpoint
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.poleData

namespace AlpogeSuperZeta

open Complex Set Filter MeasureTheory SuperZeta QuarticModel FieldTarget
open scoped Topology

noncomputable section

def gaussianPoles : Set ℂ := {w | 0 < w.re ∧ archivedGaussianFactor w = 0}

def gaussianPoleFormula (w : ℂ) : ℂ :=
  -(logDeriv archivedGaussianFactor w - w * logDeriv archivedGaussianFactor 1) /
    (w * (w - 1))

/-- The globally entire archived Gaussian factor admits the same local
pole construction as the functions in Alpöge's window proof. -/
theorem gaussian_regularized_transform :
    ∃ Φ : ℂ → ℂ,
      (∀ w, w ≠ 1 → Φ w = gaussianPoleFormula w) ∧
      (∀ ρ, ρ ≠ 0 → archivedGaussianFactor ρ ≠ 0 → AnalyticAt ℂ Φ ρ) ∧
      (∀ ρ, ρ ≠ 0 → ∃ m : ℕ, (m = 0 ↔ archivedGaussianFactor ρ ≠ 0) ∧
        ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧
          ∀ᶠ w in 𝓝[≠] ρ,
            Φ w = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (w - ρ) + h w) ∧
      (∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, archivedGaussianFactor w ≠ 0) := by
  obtain ⟨Φ, hf, ha, hp, hi⟩ := Deduction.poleData_abstract archivedGaussianFactor
    archivedGaussianFactor_entire quartic_gaussian_one_ne_zero 0
  refine ⟨Φ, ?_, ha, hp, hi⟩
  intro w hw
  simpa [gaussianPoleFormula, logDeriv_apply] using hf w hw

/-- Make the analytic inputs to the upstream Landau criterion explicit.
The real-pole premise is needed to fix the sign of the residue. -/
theorem gaussian_pole_data_of_laplace (g : ℝ → ℝ) (hMeas : Measurable g)
    (hGrowth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u))
    (hLaplace : ∀ w : ℂ, 2 < w.re →
      gaussianPoleFormula w = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * exp (-w * u))
    (hReal : ∀ ρ ∈ gaussianPoles, ρ.im = 0 → ρ.re < 1) :
    ∃ Φ : ℂ → ℂ, Deduction.PoleData g Φ gaussianPoles := by
  obtain ⟨Φ, hf, ha, hp, hi⟩ := gaussian_regularized_transform
  refine ⟨Φ, ⟨hMeas, hGrowth, ?_, fun _ h => h.1, ?_, ?_, ?_⟩⟩
  · intro w hw
    refine (hf w ?_).trans (hLaplace w hw)
    intro h
    rw [h, Complex.one_re] at hw
    linarith
  · rintro w ⟨hw, hn⟩
    change 0 < w.re at hw
    have h₀ : w ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hw
      exact (lt_irrefl _ hw)
    exact (ha w h₀ (fun h => hn ⟨hw, h⟩)).differentiableAt.differentiableWithinAt
  · intro z _
    filter_upwards [hi z] with w hw
    exact fun h => hw h.2
  · intro ρ hz
    have h₀ : ρ ≠ 0 := fun h => by simpa [h] using hz.1
    have h₁ : ρ ≠ 1 := fun h => quartic_gaussian_one_ne_zero (h ▸ hz.2)
    obtain ⟨m, hm, a, hA, he⟩ := hp ρ h₀
    have hm₀ : m ≠ 0 := fun h => (hm.mp h) hz.2
    have hc : (m : ℂ) * (-1 / (ρ * (ρ - 1))) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hm₀)
        (div_ne_zero (by norm_num) (mul_ne_zero h₀ (sub_ne_zero.mpr h₁)))
    refine ⟨_, hc, ?_, a, hA, he⟩
    intro hIm
    have hRe := hReal ρ hz hIm
    have hr : (ρ.re : ℂ) = ρ := Complex.ext (by simp) (by simpa using hIm.symm)
    have hpure : (m : ℂ) * (-1 / (ρ * (ρ - 1))) =
      ((m : ℝ) * (-1 / (ρ.re * (ρ.re - 1))) : ℝ) := by
      push_cast
      rw [hr]
    have hmPos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm₀
    have hd : ρ.re * (ρ.re - 1) < 0 := mul_neg_of_pos_of_neg hz.1 (sub_neg.mpr hRe)
    rw [hpure, Complex.ofReal_re, Complex.ofReal_im]
    exact ⟨mul_pos hmPos (div_pos_of_neg_of_neg (by norm_num) hd), rfl⟩

#print axioms Deduction.poleData_abstract
#print axioms gaussian_regularized_transform
#print axioms gaussian_pole_data_of_laplace

end
end AlpogeSuperZeta
