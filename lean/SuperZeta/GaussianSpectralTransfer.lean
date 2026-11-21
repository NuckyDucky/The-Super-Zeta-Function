import SuperZeta.UnitSpectrum
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! Transfer from the continued sum over the unit-coupling squared roots to the
three factors of the quartic field. The inputs about field and Gaussian Hecke
functions are explicit: analyticity off 1 and their Euler factorization on Re w > 1.
Continuation, the corrected spectral factor, and the zero-order calculation are proved here. -/

namespace SuperZeta.GaussianSpectralTransfer

open Complex Filter Set
open scoped Topology
noncomputable section

/-- Dirichlet beta, formed with mathlib's quadratic character of the Gaussian field. -/
def beta : ℂ → ℂ := DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))

theorem beta_analytic {w : ℂ} (hw : w ≠ 1) : AnalyticAt ℂ beta w := by
  refine (DifferentiableOn.analyticOnNhd (s := ({1}ᶜ : Set ℂ)) ?_ isOpen_compl_singleton) w hw
  intro z hz
  exact (DirichletCharacter.differentiableAt_LFunction _ z (Or.inl hz)).differentiableWithinAt

/-- This interface takes the arithmetic identity only in its domain of absolute convergence. -/
structure FactorizationData (field gaussian : ℂ → ℂ) : Prop where
  fieldAnalytic : AnalyticOnNhd ℂ field {1}ᶜ
  gaussianAnalytic : AnalyticOnNhd ℂ gaussian {1}ᶜ
  euler : ∀ w : ℂ, 1 < w.re → field w = riemannZeta w * beta w * gaussian w

variable {field gaussian : ℂ → ℂ}

theorem factorization_off_pole (d : FactorizationData field gaussian) :
    EqOn field (fun w => riemannZeta w * beta w * gaussian w) {1}ᶜ := by
  have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
  refine d.fieldAnalytic.eqOn_of_preconnected_of_eventuallyEq ?_ hpre
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num) ?_
  · exact fun z hz => ((Multiplicity.analytic_zeta hz).mul (beta_analytic hz)).mul (d.gaussianAnalytic z hz)
  · have hn : ∀ᶠ w : ℂ in 𝓝 2, 1 < w.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hn] with w hw
    exact d.euler w hw

/-- The corrected root sum, multiplied by beta and the Gaussian function, equals the field
zeta times a nonvanishing elementary factor on the pulled-back strip. -/
theorem spectral_product (d : FactorizationData field gaussian) {s : ℂ} (h₁ : s.re < 1/2) :
    (UnitSpectrum.continuation s - Reference.entireCorrection 1 s) * beta (2*s) * gaussian (2*s) =
      Spectrum.riemannFactor s * field (2*s) := by
  rw [factorization_off_pole d (Multiplicity.doubled_ne_pole h₁)]
  unfold UnitSpectrum.continuation
  ring

/-- At any interior-strip point, including common zeros, all three vanishing orders add.
The spectral term is measured at s, the other three orders at 2s. -/
theorem field_order (d : FactorizationData field gaussian) {s : ℂ}
    (h₀ : 0 < s.re) (h₁ : s.re < 1/2) :
    (d.fieldAnalytic (2*s) (Multiplicity.doubled_ne_pole h₁)).order =
      ((UnitSpectrum.continuation_analytic (Multiplicity.doubled_ne_pole h₁)).sub
        ((Reference.entireCorrection_differentiable (by norm_num : (0:ℝ) ≤ 1)).analyticAt s)).order +
      (beta_analytic (Multiplicity.doubled_ne_pole h₁)).order +
      (d.gaussianAnalytic (2*s) (Multiplicity.doubled_ne_pole h₁)).order := by
  have hp := Multiplicity.doubled_ne_pole h₁
  have hG := d.gaussianAnalytic (2*s) hp
  have hZ := Multiplicity.analytic_zeta hp
  have hB := beta_analytic hp
  have he : (fun w => riemannZeta w * beta w * gaussian w) =ᶠ[𝓝 (2*s)] field := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show 2*s ∈ ({1}ᶜ : Set ℂ) from hp)] with w hw
    exact (factorization_off_pole d hw).symm
  rw [UnitSpectrum.difference_order h₀ h₁]
  exact (((hZ.mul hB).mul hG).order_congr he).trans
    (by rw [AnalyticAt.order_mul, AnalyticAt.order_mul])

/-- The Gaussian order alone remains at any point where the two other readings exclude zero. -/
theorem field_order_of_other_factors_nonzero (d : FactorizationData field gaussian) {s : ℂ}
    (h₀ : 0 < s.re) (h₁ : s.re < 1/2)
    (hS : UnitSpectrum.continuation s ≠ Reference.entireCorrection 1 s) (hB : beta (2*s) ≠ 0) :
    (d.fieldAnalytic (2*s) (Multiplicity.doubled_ne_pole h₁)).order =
      (d.gaussianAnalytic (2*s) (Multiplicity.doubled_ne_pole h₁)).order := by
  have hp := Multiplicity.doubled_ne_pole h₁
  have hZ : riemannZeta (2*s) ≠ 0 :=
    fun hz => hS ((UnitSpectrum.equality_iff_riemann_zero h₀ h₁).2.mpr hz)
  rw [field_order d h₀ h₁, UnitSpectrum.difference_order h₀ h₁,
    (Multiplicity.analytic_zeta hp).order_eq_zero_iff.mpr hZ,
    (beta_analytic hp).order_eq_zero_iff.mpr hB, zero_add, zero_add]

/-- The continued unit-coupling root sum with its entire Mellin correction subtracted. -/
def corrected (s : ℂ) : ℂ := UnitSpectrum.continuation s - Reference.entireCorrection 1 s

private theorem corrected_eq (s : ℂ) :
    corrected s = Spectrum.riemannFactor s * riemannZeta (2*s) := by
  simp [corrected, UnitSpectrum.continuation]

/-- At a zero of the corrected spectral reading, its derivative measures the zeta
derivative in the doubled coordinate, including the Jacobian 2. -/
theorem corrected_deriv_at_zero {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1/2)
    (hz : corrected s = 0) :
    deriv corrected s = 2 * Spectrum.riemannFactor s * deriv riemannZeta (2*s) := by
  have hp := Multiplicity.doubled_ne_pole h₁
  have hζ : riemannZeta (2*s) = 0 := by
    exact (mul_eq_zero.mp ((corrected_eq s).symm.trans hz)).resolve_left
      (Spectrum.riemannFactor_ne_zero h₀)
  have hs : HasDerivAt (fun w : ℂ => 2*w) 2 s := by simpa using (hasDerivAt_id s).const_mul 2
  have hc := (differentiableAt_riemannZeta hp).hasDerivAt.comp s hs
  have hd := ((Multiplicity.analytic_factor s).differentiableAt.hasDerivAt.mul hc).deriv
  change deriv (fun t => Spectrum.riemannFactor t * riemannZeta (2*t)) s = _ at hd
  rw [funext corrected_eq, hd]
  simp only [Function.comp_apply, hζ]
  ring

/-- At a common zero of the field zeta and the corrected spectral reading, the
ordinary quotient is 0/0. A simple corrected zero and nonzero beta allow the
Gaussian factor value to be recovered from the two derivatives. -/
theorem gaussian_value_at_simple_corrected_zero (d : FactorizationData field gaussian)
    {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1/2) (hz : corrected s = 0)
    (hD : deriv corrected s ≠ 0) (hB : beta (2*s) ≠ 0) :
    gaussian (2*s) =
      2 * Spectrum.riemannFactor s * deriv field (2*s) / (deriv corrected s * beta (2*s)) := by
  have hp := Multiplicity.doubled_ne_pole h₁
  have hζ : riemannZeta (2*s) = 0 :=
    (mul_eq_zero.mp ((corrected_eq s).symm.trans hz)).resolve_left
      (Spectrum.riemannFactor_ne_zero h₀)
  have he : field =ᶠ[𝓝 (2*s)] (fun w => riemannZeta w * beta w * gaussian w) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show 2*s ∈ ({1}ᶜ : Set ℂ) from hp)] with w hw
    exact factorization_off_pole d hw
  have hd := (((differentiableAt_riemannZeta hp).hasDerivAt.mul
    (beta_analytic hp).differentiableAt.hasDerivAt).mul
    (d.gaussianAnalytic (2*s) hp).differentiableAt.hasDerivAt).deriv
  change deriv (fun w => riemannZeta w * beta w * gaussian w) (2*s) = _ at hd
  apply (eq_div_iff (mul_ne_zero hD hB)).2
  rw [he.deriv_eq, hd, hζ, corrected_deriv_at_zero h₀ h₁ hz]
  ring

end
end SuperZeta.GaussianSpectralTransfer
