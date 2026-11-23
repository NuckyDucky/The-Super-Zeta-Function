import ArchivedDottieTailPartition
import DottieReferencePhaseEnclosure

/-! Express the archived reference as one real projection of its exact
signed Dirichlet polynomial, with a certified Gamma direction. -/

open Complex
open scoped ComplexConjugate

namespace QuarticModel

open SuperZeta.StirlingCorrection
open private dottieSharpSide from ArchivedDottieTailPartition

noncomputable def dottieReferencePoint : ℂ :=
  1/2 + ((dottieHeight - 1/512 : ℝ) : ℂ)*I

private noncomputable def referenceTerm (n : ℕ) : ℂ :=
  if n = 0 then 0 else (archivedLatticeCoeff n : ℂ) *
    ((archivedThetaScale / (n : ℝ) : ℝ) : ℂ)^dottieReferencePoint

/-- The finite signed polynomial used in the original reference unit. -/
noncomputable def dottieReferencePolynomial : ℂ :=
  ∑ n ∈ Finset.range (276824064+1), referenceTerm n

/-- The archived normalization is the absolute real projection of its signed
polynomial at the same point, with the Gamma direction enclosed in Lean. -/
theorem dottieCircleReference_eq_gamma_phase_projection :
    ∃ phase : ℝ, 4.067324 < phase ∧ phase < 4.067326 ∧
      Gamma dottieReferencePoint / (‖Gamma dottieReferencePoint‖ : ℂ) =
        Complex.exp ((phase : ℂ)*I) ∧
      dottieCircleReference = (2 * ‖Gamma dottieReferencePoint‖ / archivedDottieCompletionScale) *
        |(Complex.exp ((phase : ℂ)*I) * dottieReferencePolynomial).re| := by
  let z := dottieReferencePoint
  let P := dottieReferencePolynomial
  have hpoint : archivedRightCenter dottieHeight - (1/64 : ℂ) = z := by
    apply Complex.ext <;> norm_num [z, dottieReferencePoint, archivedRightCenter, Complex.mul_re,
      Complex.mul_im]
  have hmirror : 1 - conj z = z := by
    apply Complex.ext <;> norm_num [z, dottieReferencePoint, Complex.mul_re, Complex.mul_im]
  have hpos : 0 < z.re := by norm_num [z, dottieReferencePoint, Complex.mul_re]
  obtain ⟨φ, hφ₁, hφ₂, hφ⟩ := dottie_gamma_reference_phase_interval
  change Gamma z / (‖Gamma z‖ : ℂ) = Complex.exp ((φ : ℂ)*I) at hφ
  let A := archivedDottieCompletionScale
  let g := Gamma z / (A : ℂ)
  have hn : ‖Gamma z‖ ≠ 0 := norm_ne_zero_iff.mpr (Gamma_ne_zero_of_re_pos hpos)
  have hg : g = ((‖Gamma z‖ / A : ℝ) : ℂ) * Complex.exp ((φ : ℂ)*I) := by
    have h := (div_eq_iff (Complex.ofReal_ne_zero.mpr hn)).mp hφ
    dsimp only [g]
    conv_lhs => rw [h]
    push_cast
    ring
  have hterm (n : ℕ) : dottieSharpSide z n = g * referenceTerm n := by
    by_cases h : n = 0
    · simp [dottieSharpSide, referenceTerm, h]
    · simp only [dottieSharpSide, referenceTerm, h, if_false, z, g, A]
      ring
  refine ⟨φ, hφ₁, hφ₂, hφ, ?_⟩
  change dottieCircleReference = (2 * ‖Gamma z‖ / A) *
    |(Complex.exp ((φ : ℂ)*I) * P).re|
  rw [dottieCircleReference, hpoint, hmirror]
  simp only [hterm, Finset.sum_add_distrib, ← map_sum, ← Finset.mul_sum]
  change ‖g * P + conj (g * P)‖ = _
  have hro (v : ℂ) : v + conj v = ((2*v.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [two_mul]
  rw [hro, hg, mul_assoc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul]
  have hA : 0 < A := archivedDottieCompletionScale_pos
  rw [abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_nonneg (by positivity : 0 ≤ ‖Gamma z‖ / A)]
  ring

theorem dottieCircleReference_eq_phase_projection :
    ∃ phase : ℝ, 4.067324 < phase ∧ phase < 4.067326 ∧
      dottieCircleReference = (2 * ‖Gamma dottieReferencePoint‖ / archivedDottieCompletionScale) *
        |(Complex.exp ((phase : ℂ)*I) * dottieReferencePolynomial).re| := by
  obtain ⟨phase,hlo,hhi,_,hprojection⟩ := dottieCircleReference_eq_gamma_phase_projection
  exact ⟨phase,hlo,hhi,hprojection⟩

#print axioms dottieCircleReference_eq_gamma_phase_projection
#print axioms dottieCircleReference_eq_phase_projection

end QuarticModel
