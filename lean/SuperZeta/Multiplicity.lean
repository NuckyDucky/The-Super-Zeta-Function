import SuperZeta.Spectrum
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Analytic multiplicities in the doubled Riemann coordinate. -/
namespace SuperZeta.Multiplicity
open Filter Complex
open scoped Topology
noncomputable section

theorem scale_analytic (c z : ℂ) : AnalyticAt ℂ (fun w : ℂ => c*w) z := by fun_prop

/-- Scaling the local coordinate by a nonzero number preserves its vanishing order. -/
theorem scale_order {f : ℂ → ℂ} {c z : ℂ} (hc : c ≠ 0) (hf : AnalyticAt ℂ f (c*z)) :
    (hf.comp (scale_analytic c z)).order = hf.order := by
  have ht := (scale_analytic c z).continuousAt.tendsto
  by_cases htop : hf.order = ⊤
  · rw [htop, AnalyticAt.order_eq_top_iff]
    exact ht.eventually (hf.order_eq_top_iff.mp htop)
  · let n := hf.order.toNat
    have hn : (n:ENat)=hf.order := ENat.coe_toNat_eq_self.mpr htop
    obtain ⟨g,hg,hg₀,he⟩ := hf.order_eq_nat_iff.mp hn.symm
    rw [←hn, AnalyticAt.order_eq_nat_iff]
    refine ⟨fun w => c^n*g (c*w), analyticAt_const.mul (hg.comp (scale_analytic c z)),
      mul_ne_zero (pow_ne_zero _ hc) hg₀, ?_⟩
    filter_upwards [ht.eventually he] with w hw
    change f (c*w) = (w-z)^n • (c^n*g (c*w))
    rw [hw, show c*w-c*z=c*(w-z) by ring, mul_pow, smul_eq_mul, smul_eq_mul]
    ring

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
  rw [AnalyticAt.order_mul, (analytic_factor s).order_eq_zero_iff.mpr
    (Spectrum.riemannFactor_ne_zero h₀), zero_add, scale_order (by norm_num)]

end
end SuperZeta.Multiplicity
