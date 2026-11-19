import SuperZeta.DeterminantProduct
import SuperZeta.Multiplicity

/-! The unit-coupling root list and its analytic continuation.
Every entry is chosen from a proved unique solution of its defining equation. -/
namespace SuperZeta.UnitSpectrum

noncomputable section
open Set

/-- The unique real Dottie root between zero and π/2. -/
def dottie : ℝ := Classical.choose Dottie.existsUnique_dottie.exists

theorem dottie_spec : dottie ∈ Ioo 0 (Real.pi/2) ∧ dottie = Real.cos dottie :=
  Classical.choose_spec Dottie.existsUnique_dottie.exists

/-- Index zero refers to the first positive quartet level. -/
def levelHeight (n : ℕ) : ℝ :=
  Classical.choose (QuartetRadius.existsUnique_level (n+1) (Nat.succ_pos n)).exists

theorem levelHeight_spec (n : ℕ) : 0 < levelHeight n ∧
    QuartetRadius.level (levelHeight n) = 2 * Real.pi * (n+1) := by
  simpa only [levelHeight, Nat.cast_add, Nat.cast_one] using
    Classical.choose_spec (QuartetRadius.existsUnique_level (n+1) (Nat.succ_pos n)).exists

/-- One real square and the conjugate pair of squares from each positive quartet. -/
def squaredRoot : Unit ⊕ (ℕ ⊕ ℕ) → ℂ := RootBounds.family dottie levelHeight

/-- The product uses every classified squared root and is normalized at the origin. -/
theorem determinant_product (v : ℂ) :
    Spectrum.coupledDet v = ∏' j, (1 - v / squaredRoot j) :=
  Ray.coupledDet_eq_tprod dottie_spec levelHeight_spec v

/-- The root sum after continuation, analytic away from the doubled zeta pole. -/
def continuation (s : ℂ) : ℂ :=
  Reference.entireCorrection 1 s + Spectrum.riemannFactor s * riemannZeta (2*s)

/-- On the open Mellin strip the series of actual squared roots sums to the
continued function. `HasSum` includes convergence as well as the value. -/
theorem root_hasSum {s : ℂ} (hs : 1/2 < s.re) (hu : s.re < 1) :
    HasSum (fun j => (squaredRoot j)^(-s)) (continuation s) := by
  have hsum := (RootBounds.indexed_stieltjes dottie_spec.1.1 levelHeight_spec hs hu).summable.hasSum
  have h := Ray.root_series_reconstruction dottie_spec levelHeight_spec hs hu
  rw [sub_eq_iff_eq_add] at h
  simpa only [squaredRoot, continuation, h, add_comm] using hsum

theorem continuation_analytic {s : ℂ} (hs : 2*s ≠ 1) :
    AnalyticAt ℂ continuation s := by
  have hJ : AnalyticAt ℂ (Reference.entireCorrection 1) s :=
    (Reference.entireCorrection_differentiable (by norm_num : (0:ℝ) ≤ 1)).analyticAt s
  exact hJ.add ((Multiplicity.analytic_factor s).mul
    ((Multiplicity.analytic_zeta hs).comp (Multiplicity.scale_analytic 2 s)))

/-- On the pulled-back critical strip, the continued root sum meets the
entire correction exactly at a zero of Riemann zeta at twice the input. -/
theorem equality_iff_riemann_zero {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1/2) :
    AnalyticAt ℂ continuation s ∧
    (continuation s = Reference.entireCorrection 1 s ↔ riemannZeta (2*s) = 0) :=
  ⟨continuation_analytic (Multiplicity.doubled_ne_pole h₁),
    Spectrum.equality_iff_riemann_zero h₀ (by simp [continuation])⟩

/-- The difference between the continued root sum and its Mellin correction
has the same vanishing order as Riemann zeta at the doubled coordinate. -/
theorem difference_order {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1/2) :
    ((continuation_analytic (Multiplicity.doubled_ne_pole h₁)).sub
      ((Reference.entireCorrection_differentiable (by norm_num : (0:ℝ) ≤ 1)).analyticAt s)).order =
    (Multiplicity.analytic_zeta (Multiplicity.doubled_ne_pole h₁)).order := by
  have he : (fun t => Spectrum.riemannFactor t * riemannZeta (2*t)) =
      (fun t => continuation t - Reference.entireCorrection 1 t) := by
    funext t
    simp [continuation]
  exact (((Multiplicity.analytic_factor s).mul
    ((Multiplicity.analytic_zeta (Multiplicity.doubled_ne_pole h₁)).comp
      (Multiplicity.scale_analytic 2 s))).order_congr
        (Filter.EventuallyEq.of_eq he)).trans (Multiplicity.reconstruction_order h₀ h₁)

end
end SuperZeta.UnitSpectrum
