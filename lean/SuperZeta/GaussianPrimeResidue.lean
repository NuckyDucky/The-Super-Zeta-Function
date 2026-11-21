import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Local residue of the equal-sign prime detector. Its arithmetic identity on the
convergence half-plane is a separate Euler calculation. The local input here is
the continued identity 2S = H' - g'/g on a punctured neighborhood. -/

namespace SuperZeta.GaussianPrimeResidue

open Complex Filter Set
open scoped Topology

private theorem logDeriv_factorization {ρ : ℂ} {m : ℕ} {g u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u ρ) (hu₀ : u ρ ≠ 0)
    (hg : g =ᶠ[𝓝 ρ] fun z => (z - ρ)^m * u z) :
    logDeriv g =ᶠ[𝓝[≠] ρ] fun z => (m : ℂ)/(z-ρ) + logDeriv u z := by
  have hlocal : ∀ᶠ z in 𝓝 ρ,
      g z = (z-ρ)^m * u z ∧ deriv g z = deriv (fun w => (w-ρ)^m * u w) z ∧
        u z ≠ 0 ∧ AnalyticAt ℂ u z :=
    hg.and (hg.deriv.and ((hu.continuousAt.eventually_ne hu₀).and hu.eventually_analyticAt))
  filter_upwards [hlocal.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z h hz
  have hne : z-ρ ≠ 0 := sub_ne_zero.mpr hz
  have hs : HasDerivAt (fun w : ℂ => w-ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  calc
    logDeriv g z = logDeriv (fun w => (w-ρ)^m * u w) z := by
      simp only [logDeriv_apply, h.1, h.2.1]
    _ = logDeriv (fun w => (w-ρ)^m) z + logDeriv u z :=
      logDeriv_mul z (pow_ne_zero _ hne) h.2.2.1 (hs.pow m).differentiableAt h.2.2.2.differentiableAt
    _ = _ := by rw [logDeriv_fun_pow hs.differentiableAt m, logDeriv_apply, hs.deriv]; ring

/-- The regular part after removing -m/(2(z-ρ)) is analytic, including when m=0. -/
theorem detector_principal_part {ρ : ℂ} {m : ℕ} {H g S : ℂ → ℂ}
    (hH : AnalyticAt ℂ H ρ) (hg : AnalyticAt ℂ g ρ) (hm : hg.order = (m : ℕ∞))
    (hS : S =ᶠ[𝓝[≠] ρ] fun z => (deriv H z - logDeriv g z)/2) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R ρ ∧
      S =ᶠ[𝓝[≠] ρ] fun z => R z - (m : ℂ)/(2*(z-ρ)) := by
  obtain ⟨u, hu, hu₀, he⟩ := hg.order_eq_nat_iff.mp hm
  have hgerm : g =ᶠ[𝓝 ρ] fun z => (z-ρ)^m * u z := by simpa [smul_eq_mul] using he
  refine ⟨fun z => (deriv H z - deriv u z / u z)/2, ?_, ?_⟩
  · exact (hH.deriv.sub (hu.deriv.div hu hu₀)).div analyticAt_const (by norm_num)
  · filter_upwards [hS, logDeriv_factorization hu hu₀ hgerm] with z hSz hgz
    rw [hSz, hgz, logDeriv_apply, div_mul_eq_div_div]
    ring

/-- The scaled detector tends to -m/2 at a zero of finite order m. -/
theorem detector_residue {ρ : ℂ} {m : ℕ} {H g S : ℂ → ℂ}
    (hH : AnalyticAt ℂ H ρ) (hg : AnalyticAt ℂ g ρ) (hm : hg.order = (m : ℕ∞))
    (hS : S =ᶠ[𝓝[≠] ρ] fun z => (deriv H z - logDeriv g z)/2) :
    Tendsto (fun z => (z-ρ)*S z) (𝓝[≠] ρ) (𝓝 (-(m : ℂ)/2)) := by
  obtain ⟨R,hR,hE⟩ := detector_principal_part hH hg hm hS
  have hc : ContinuousAt (fun z : ℂ => (z-ρ)*R z - (m : ℂ)/2) ρ :=
    ((continuousAt_id.sub continuousAt_const).mul hR.continuousAt).sub continuousAt_const
  have ht : Tendsto (fun z : ℂ => (z-ρ)*R z - (m : ℂ)/2) (𝓝[≠] ρ) (𝓝 (-(m : ℂ)/2)) := by
    simpa [neg_div] using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  apply ht.congr'
  filter_upwards [hE, self_mem_nhdsWithin] with z h hz
  rw [h]
  field_simp [sub_ne_zero.mpr (show z ≠ ρ from hz)]
  ring

/-- Consequently a holomorphic continuation of that detector at ρ forces ordinary
order zero there whenever the Gaussian germ has finite order. -/
theorem order_zero_of_detector_analytic {ρ : ℂ} {m : ℕ} {H g S : ℂ → ℂ}
    (hH : AnalyticAt ℂ H ρ) (hg : AnalyticAt ℂ g ρ) (hm : hg.order = (m : ℕ∞))
    (hS : S =ᶠ[𝓝[≠] ρ] fun z => (deriv H z - logDeriv g z)/2)
    (hreg : AnalyticAt ℂ S ρ) : m = 0 := by
  have hc : ContinuousAt (fun z : ℂ => (z-ρ)*S z) ρ :=
    (continuousAt_id.sub continuousAt_const).mul hreg.continuousAt
  have ht : Tendsto (fun z : ℂ => (z-ρ)*S z) (𝓝[≠] ρ) (𝓝 0) := by
    simpa using hc.tendsto.mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have h := tendsto_nhds_unique (detector_residue hH hg hm hS) ht
  simpa using h

/-- A holomorphic candidate S on a connected open set needs to agree with the
prime detector only near one ordinary point. Continuing the denominator-cleared
identity first allows the residue argument to test every point, including a
hypothetical zero of g. No zero-free neighborhood of that point is assumed. -/
theorem zero_free_of_detector_continuation {U : Set ℂ} {H g S : ℂ → ℂ} {a : ℂ}
    (ho : IsOpen U) (hc : IsPreconnected U) (ha : a ∈ U) (hga : g a ≠ 0)
    (hH : AnalyticOnNhd ℂ H U) (hg : AnalyticOnNhd ℂ g U) (hS : AnalyticOnNhd ℂ S U)
    (hseed : S =ᶠ[𝓝 a] fun z => (deriv H z - logDeriv g z)/2) :
    ∀ ρ ∈ U, g ρ ≠ 0 := by
  have hcleared : EqOn (fun z => 2*S z*g z) (fun z => deriv H z*g z - deriv g z) U := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) ?_ ?_ hc ha ?_
    · exact fun z hz => (analyticAt_const.mul (hS z hz)).mul (hg z hz)
    · exact fun z hz => (((hH z hz).deriv).mul (hg z hz)).sub (hg z hz).deriv
    · filter_upwards [hseed, (hg a ha).continuousAt.eventually_ne hga] with z h hz
      rw [h, logDeriv_apply]
      field_simp [hz]
      ring
  intro ρ hρ
  have hnontrivial : ¬ (∀ᶠ z in 𝓝 ρ, g z = 0) := fun h =>
    hga (hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hρ h ha)
  have hfinite := mt (hg ρ hρ).order_eq_top_iff.mp hnontrivial
  have hm := (ENat.coe_toNat_eq_self.mpr hfinite).symm
  have hn := (hg ρ hρ).eventually_eq_zero_or_eventually_ne_zero.resolve_left hnontrivial
  have he : S =ᶠ[𝓝[≠] ρ] fun z => (deriv H z - logDeriv g z)/2 := by
    have hloc : U ∈ 𝓝[≠] ρ := mem_nhdsWithin_of_mem_nhds (ho.mem_nhds hρ)
    filter_upwards [hn, hloc] with z hz hU
    rw [logDeriv_apply]
    apply (eq_div_iff (by norm_num : (2:ℂ) ≠ 0)).2
    field_simp [hz]
    linear_combination hcleared hU
  have hzero := order_zero_of_detector_analytic (hH ρ hρ) (hg ρ hρ) hm he (hS ρ hρ)
  exact (hg ρ hρ).order_eq_zero_iff.mp (by simpa [hzero] using hm)

end SuperZeta.GaussianPrimeResidue
