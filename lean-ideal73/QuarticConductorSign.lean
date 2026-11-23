import MurphyOddStep
import ArchivedThetaPoisson

/-! Apply the original odd-prime induction at the three conductor primes,
then supply the positive amplitude to the same archived field continuation. -/

namespace QuarticConductorSign

open QuarticFiniteFourier DBN.Gen

private def AtLevel (n : ℕ) [NeZero n] : Prop :=
  ∀ χ : DirichletCharacter ℂ n, χ.IsPrimitive → (∀ k : ℕ, (χ k).im = 0) →
    χ.rootNumber = 1 ∧ Kprop χ

private theorem base : AtLevel 1 := by
  intro χ _ _
  exact ⟨DirichletCharacter.rootNumber_modOne χ, K_level_one χ⟩

private theorem extend {p m : ℕ} [Fact p.Prime] [NeZero m] (hp : p ≠ 2)
    (hc : p.Coprime m) (prev : AtLevel m) : AtLevel (p*m) := by
  intro χ hprim hreal
  exact sign_step hp hc χ hprim hreal
    (prev _ (comp2_isPrimitive hc χ hprim) (comp_real hc χ hreal).2)

private theorem character_real (n : ℕ) : (quarticCharacter n).im = 0 := by
  change ((jacobiSym ((n : ZMod D).val : ℤ) D : ℂ)).im = 0
  simp

private instance prime41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩
private instance prime457 : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
private instance prime1414835497 : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

theorem root_number : quarticCharacter.rootNumber = 1 := by
  have h₃ := extend (p := 1414835497) (m := 1) (by decide) (by decide) base
  have h₂ := extend (p := 457) (m := 1414835497*1) (by decide) (by decide) h₃
  have h₁ := extend (p := 41) (m := 457*(1414835497*1)) (by decide) (by decide) h₂
  exact (h₁ quarticCharacter quarticCharacter_primitive character_real).1

theorem amplitude : gaussAmplitude = (Real.sqrt D : ℂ) := by
  have he : quarticCharacter.Even := quarticCharacter_at_neg_one
  rw [gaussAmplitude, gaussSum_of_rootNumber root_number, if_pos he, pow_zero, one_mul,
    natCast_cpow_half, ← Real.sqrt_eq_rpow]

#print axioms root_number
#print axioms amplitude

end QuarticConductorSign

namespace QuarticModel

open FieldCoefficientTransfer ArtinPrimitiveRootsConjecture

theorem archivedTheta_reflection : ArchivedThetaReflects :=
  archivedThetaReflects_of_gaussAmplitude QuarticConductorSign.amplitude

theorem archivedMellin_functional_equation (w : ℂ) : archivedMellin (1-w) = archivedMellin w :=
  archivedMellin_reflects archivedTheta_reflection w

theorem archivedGaussianFactor_entire : Differentiable ℂ archivedGaussianFactor :=
  archivedGaussianFactor_differentiable archivedTheta_reflection

noncomputable def archivedQuarticZeta (w : ℂ) : ℂ :=
  riemannZeta w * chi4.LFunction w * archivedGaussianFactor w

theorem archivedQuarticZeta_isDedekind : IsDedekindZeta K archivedQuarticZeta :=
  archivedFieldContinuation archivedTheta_reflection

theorem archivedQuarticZeta_eq_off_one {Z : ℂ → ℂ} (hZ : IsDedekindZeta K Z) {w : ℂ} (hw : w ≠ 1) :
    archivedQuarticZeta w = Z w :=
  FieldTarget.continuation_eq_off_one archivedQuarticZeta_isDedekind hZ hw

theorem archivedGaussianFactor_zero_iff_mellin {w : ℂ} (hw : 0 < w.re) :
    archivedGaussianFactor w = 0 ↔ archivedMellin w = 0 := by
  have hGamma := Complex.Gamma_ne_zero_of_re_pos hw
  have hscale : (archivedThetaScale : ℂ)^w ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'))
  simp [archivedGaussianFactor, hGamma, hscale]

theorem archivedQuarticZeta_zero_iff {w : ℂ} (hw : 0 < w.re) :
    archivedQuarticZeta w = 0 ↔
      riemannZeta w = 0 ∨ chi4.LFunction w = 0 ∨ archivedMellin w = 0 := by
  rw [archivedQuarticZeta, mul_eq_zero, mul_eq_zero, archivedGaussianFactor_zero_iff_mellin hw, or_assoc]

theorem archivedQuarticRH_iff_three_factors :
    DedekindZetaRH K ↔ FieldTarget.StripZerosOnLine riemannZeta ∧
      FieldTarget.StripZerosOnLine chi4.LFunction ∧ FieldTarget.StripZerosOnLine archivedGaussianFactor :=
  FieldTarget.dedekindZetaRH_iff_three_factors archivedQuarticZeta_isDedekind.1 archivedQuarticZeta_isDedekind.2

#print axioms archivedTheta_reflection
#print axioms archivedMellin_functional_equation
#print axioms archivedGaussianFactor_entire
#print axioms archivedQuarticZeta_isDedekind
#print axioms archivedQuarticZeta_eq_off_one
#print axioms archivedQuarticZeta_zero_iff
#print axioms archivedQuarticRH_iff_three_factors

end QuarticModel
