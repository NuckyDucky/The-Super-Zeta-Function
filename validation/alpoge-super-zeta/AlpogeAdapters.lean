import SpectralBridge
import Formalism.GammaFactorNonvanishing.RhOfRight
import Statements
import ArchivedQuarticSpectralAddress

namespace AlpogeSuperZeta

open Complex Filter SuperZeta QuarticModel FieldTarget
open SuperZeta.QuarticOrderedTurns
open scoped Topology

noncomputable section

/-- This reproduces the input to Alpöge's imported reflection argument in
the spectral coordinate and retains the pole exclusion explicitly. -/
def RightSpectralNonvanishing : Prop :=
  ∀ s : ℂ, 1 / 4 < s.re → 2 * s ≠ 1 → corrected s ≠ 0

theorem rh_iff_right_spectral_nonvanishing :
    RiemannHypothesis ↔ RightSpectralNonvanishing := by
  constructor
  · intro hRH s hs hp hc
    have hpos : 0 < s.re := by linarith
    have hz := (mul_eq_zero.mp ((corrected_eq s).symm.trans hc)).resolve_left
      (Spectrum.riemannFactor_ne_zero hpos)
    have hw : 1 / 2 < (2 * s).re := by simp [two_mul]; linarith
    have htriv : ¬∃ n : ℕ, 2 * s = -2 * ((n : ℂ) + 1) := by
      rintro ⟨n, hn⟩
      have hr := congrArg Complex.re hn
      simp [Complex.mul_re, Complex.add_re] at hr
      linarith [Nat.cast_nonneg (α := ℝ) n]
    exact (ne_of_gt hw) (hRH (2 * s) hz htriv hp)
  · intro h
    apply Formalism.VW.rh_of_right
    intro w hw hp hz
    have hs : 1 / 4 < (w / 2).re := by rw [Complex.div_ofNat_re]; linarith
    have he : 2 * (w / 2) = w := by ring
    apply h (w / 2) hs (by rwa [he])
    rw [corrected_eq, he, hz, mul_zero]

/-- The exact published Dirichlet statement supplies both rational cofactors.
Here the modulus-one specialization is ordinary zeta. -/
theorem cofactors_on_line (hD : DirichletLZerosOnLine) :
    StripZerosOnLine riemannZeta ∧
      StripZerosOnLine FieldCoefficientTransfer.chi4.LFunction := by
  constructor
  · have h := hD 1 (1 : DirichletCharacter ℂ 1)
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    exact h
  · exact hD 4 FieldCoefficientTransfer.chi4

/-- At the actual recovered input the ordinary spectral comparison is
separated and the field zero is exactly the painted Gaussian equality. -/
theorem quartic_chart_of_dirichlet (hD : DirichletLZerosOnLine)
    (x : QuarticTurn.Input) (ink : ℂ → ℂ) (hoff : x.val.re ≠ 1 / 2) :
    let q := QuarticTurn.inChart (fun y : QuarticTurn.Input =>
      paintedReading y.val (ink y.val)) (QuarticTurn.chart x)
    QuarticTurn.address x ≠ Reference.entireCorrection 1 (x.val / 2) ∧
      (archivedQuarticZeta x.val = 0 ↔ jk q = kj q) := by
  have hx := x.property
  change (15 / 64 ≤ (x.val / 2).re ∧ (x.val / 2).re ≤ 17 / 64) ∧
    101 ≤ (x.val / 2).im at hx
  have hs₀ : 0 < (x.val / 2).re := by linarith [hx.1.1]
  have hs₁ : (x.val / 2).re < 1 / 2 := by linarith [hx.1.2]
  have he : 2 * (x.val / 2) = x.val := by ring
  have hw₀ : 0 < x.val.re := by rw [Complex.div_ofNat_re] at hs₀; linarith
  have hw₁ : x.val.re < 1 := by rw [Complex.div_ofNat_re] at hs₁; linarith
  obtain ⟨hR, hB⟩ := cofactors_on_line hD
  have hOrdinary : QuarticTurn.address x ≠ Reference.entireCorrection 1 (x.val / 2) := by
    intro hc
    have hz := (UnitSpectrum.equality_iff_riemann_zero hs₀ hs₁).2.mp hc
    rw [he] at hz
    exact hoff (hR x.val hw₀ hw₁ hz)
  have hb : FieldCoefficientTransfer.chi4.LFunction x.val ≠ 0 :=
    fun hz => hoff (hB x.val hw₀ hw₁ hz)
  refine ⟨hOrdinary, ?_⟩
  have h := archivedFieldZero_at_chart x ink
  simpa only [hOrdinary, hb, false_or] using h

/-- Use the ordinary reconstruction as an actual cofactor in the Riemann
coordinate. No rescaling remains in the Gaussian logarithmic derivative. -/
def spectralZetaAt (w : ℂ) : ℂ := normalized (w / 2)

theorem spectralZetaAt_eq {w : ℂ} (hw : 0 < w.re) : spectralZetaAt w = riemannZeta w := by
  have hs : 0 < (w / 2).re := by rw [Complex.div_ofNat_re]; linarith
  rw [spectralZetaAt, normalized_eq hs, show 2 * (w / 2) = w by ring]

theorem quartic_gaussian_logDeriv {w : ℂ} (hw : 0 < w.re) (hp : w ≠ 1)
    (hz : riemannZeta w ≠ 0) (hb : FieldCoefficientTransfer.chi4.LFunction w ≠ 0)
    (hg : archivedGaussianFactor w ≠ 0) :
    logDeriv archivedQuarticZeta w - logDeriv spectralZetaAt w -
      logDeriv FieldCoefficientTransfer.chi4.LFunction w =
      logDeriv archivedGaussianFactor w := by
  have he : spectralZetaAt =ᶠ[𝓝 w] riemannZeta := by
    have hh : ∀ᶠ v : ℂ in 𝓝 w, 0 < v.re :=
      (isOpen_lt continuous_const continuous_re).mem_nhds hw
    filter_upwards [hh] with v hv
    exact spectralZetaAt_eq hv
  have hr := (logDeriv_congr_nhds he).eq_of_nhds
  have hZ := differentiableAt_riemannZeta hp
  have hB := DirichletCharacter.differentiableAt_LFunction FieldCoefficientTransfer.chi4 w
    (Or.inl hp)
  have hG := archivedGaussianFactor_entire w
  change logDeriv (fun v => riemannZeta v *
    FieldCoefficientTransfer.chi4.LFunction v * archivedGaussianFactor v) w -
    logDeriv spectralZetaAt w - logDeriv FieldCoefficientTransfer.chi4.LFunction w = _
  have hprod := logDeriv_mul (f := fun v => riemannZeta v *
    FieldCoefficientTransfer.chi4.LFunction v) (g := archivedGaussianFactor)
    w (mul_ne_zero hz hb) hg (hZ.mul hB) hG
  rw [hr, hprod, logDeriv_mul (f := riemannZeta)
    (g := FieldCoefficientTransfer.chi4.LFunction) w hz hb hZ hB]
  ring

#print axioms Formalism.VW.rh_of_right
#print axioms rh_iff_right_spectral_nonvanishing
#print axioms cofactors_on_line
#print axioms quartic_chart_of_dirichlet
#print axioms quartic_gaussian_logDeriv

end
end AlpogeSuperZeta
