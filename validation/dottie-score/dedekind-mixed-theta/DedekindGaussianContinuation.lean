import DedekindGaussianEulerProduct

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set

/-- The ordinary zeta and beta product is the Gaussian field's meromorphic
continuation, with its regularity and defining Dirichlet-series identity. -/
theorem gaussianQuadratic_zeta_beta_isDedekind :
    IsDedekindZeta GaussianQuadraticField (fun w ↦ riemannZeta w * gaussianQuadraticChar.LFunction w) := by
  refine ⟨?_, fun w hw ↦ (gaussianQuadratic_dedekindZeta_eq_zeta_beta w hw).symm⟩
  intro w hw
  have hne : w ≠ 1 := hw
  exact ((differentiableAt_riemannZeta hne).mul
    (DirichletCharacter.differentiableAt_LFunction gaussianQuadraticChar w (Or.inl hne))).differentiableWithinAt

theorem gaussianQuadratic_mixedThetaContinuation_eq_zeta_beta {w : ℂ} (hw : w ≠ 1) :
    mixedThetaContinuation GaussianQuadraticField w = riemannZeta w * gaussianQuadraticChar.LFunction w :=
  continuation_eq_off_one (mixedThetaContinuation_isDedekind GaussianQuadraticField)
    gaussianQuadratic_zeta_beta_isDedekind hw

/-- Each factor's strip-zero statement is necessary and together they suffice
for the exact Gaussian field statement. -/
theorem gaussianQuadratic_dedekindZetaRH_iff_zeta_beta :
    DedekindZetaRH GaussianQuadraticField ↔
      StripZerosOnLine riemannZeta ∧ StripZerosOnLine gaussianQuadraticChar.LFunction := by
  rw [dedekindZetaRH_iff_strip gaussianQuadratic_zeta_beta_isDedekind]
  constructor
  · intro h
    exact ⟨fun w h0 h1 hz ↦ h w h0 h1 (by simp [hz]),
      fun w h0 h1 hz ↦ h w h0 h1 (by simp [hz])⟩
  · rintro ⟨hζ, hβ⟩ w h0 h1 hz
    exact (mul_eq_zero.mp hz).elim (hζ w h0 h1) (hβ w h0 h1)

#check @gaussianQuadratic_mixedThetaContinuation_eq_zeta_beta
#check @gaussianQuadratic_dedekindZetaRH_iff_zeta_beta
#print axioms gaussianQuadratic_zeta_beta_isDedekind
#print axioms gaussianQuadratic_mixedThetaContinuation_eq_zeta_beta
#print axioms gaussianQuadratic_dedekindZetaRH_iff_zeta_beta

end FieldTarget
