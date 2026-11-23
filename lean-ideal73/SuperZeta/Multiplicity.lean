import SuperZeta.Spectrum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Analytic multiplicities in the doubled Riemann coordinate. -/
namespace SuperZeta.Multiplicity
open Filter Complex
open scoped Topology
noncomputable section

/-- Retain the original proof-indexed notation for Mathlib's analytic order. -/
abbrev _root_.AnalyticAt.order {f : ℂ → ℂ} {z : ℂ} (_ : AnalyticAt ℂ f z) : ENat :=
  analyticOrderAt f z

theorem scale_analytic (c z : ℂ) : AnalyticAt ℂ (fun w : ℂ => c*w) z := by fun_prop

/-- Scaling the local coordinate by a nonzero number preserves its vanishing order. -/
theorem scale_order {f : ℂ → ℂ} {c z : ℂ} (hc : c ≠ 0) (hf : AnalyticAt ℂ f (c*z)) :
    (hf.comp (scale_analytic c z)).order = hf.order := by
  exact analyticOrderAt_comp_of_deriv_ne_zero (scale_analytic c z) (by rwa [deriv_const_mul_id])

theorem analytic_factor (s : ℂ) : AnalyticAt ℂ Spectrum.riemannFactor s := by
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  unfold Spectrum.riemannFactor
  simp only [Complex.cpow_def_of_ne_zero hp, Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0)]
  fun_prop

theorem analytic_zeta {w : ℂ} (hw : w ≠ 1) : AnalyticAt ℂ riemannZeta w := by
  have h : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  exact h.analyticAt (isOpen_compl_singleton.mem_nhds hw)

theorem doubled_ne_pole {s : ℂ} (h : s.re<1/2) : 2*s ≠ 1 := by
  intro eq
  have k := congrArg Complex.re eq
  simp [two_mul] at k
  linarith

/-- At every point of the pulled-back open strip the reconstructed product has
the exact same order as ordinary Riemann zeta at twice its input. -/
theorem reconstruction_order {s : ℂ} (h₀ : 0<s.re) (h₁ : s.re<1/2) :
    ((analytic_factor s).mul ((analytic_zeta (doubled_ne_pole h₁)).comp (scale_analytic 2 s))).order =
      (analytic_zeta (doubled_ne_pole h₁)).order := by
  have hz := analytic_zeta (doubled_ne_pole h₁)
  change analyticOrderAt (Spectrum.riemannFactor * (riemannZeta ∘ fun w : ℂ => 2*w)) s = _
  rw [analyticOrderAt_mul (analytic_factor s) (hz.comp (scale_analytic 2 s)),
    (analytic_factor s).analyticOrderAt_eq_zero.mpr (Spectrum.riemannFactor_ne_zero h₀), zero_add]
  exact scale_order (by norm_num) hz

end
end SuperZeta.Multiplicity
