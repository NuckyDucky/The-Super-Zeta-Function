import GaussianVaughanMellinSeries
import Mathlib.Analysis.Meromorphic.NormalForm

/-! Complete the removable values of the actual Mellin transform. A zero
is a pole precisely when the original multiplier survives there. -/

namespace AlpogeSuperZeta

open Complex Filter Set QuarticModel
open scoped Topology

noncomputable section

def archivedGaussianVaughanDetectedPoles : Set ℂ :=
  {z | archivedGaussianFactor z = 0 ∧ archivedGaussianVaughanMultiplier z ≠ 0}

def archivedGaussianVaughanMellinNormal : ℂ → ℂ :=
  toMeromorphicNFOn archivedGaussianVaughanMellin Set.univ

private theorem vaughanMellin_meromorphic :
    MeromorphicOn archivedGaussianVaughanMellin Set.univ := by
  intro z _
  have hG := archivedGaussianFactor_entire.analyticAt z
  have hM := archivedGaussianVaughanMultiplier_entire.analyticAt z
  have hL : MeromorphicAt (logDeriv archivedGaussianFactor) z :=
    hG.deriv.meromorphicAt.div hG.meromorphicAt
  exact hM.meromorphicAt.mul hL.neg

private theorem vaughanMellinNormal_eventuallyEq (z : ℂ) :
    archivedGaussianVaughanMellinNormal =ᶠ[𝓝[≠] z] archivedGaussianVaughanMellin :=
  vaughanMellin_meromorphic.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)

theorem archivedGaussianVaughanMellinNormal_eq {z : ℂ}
    (hz : archivedGaussianFactor z ≠ 0) :
    archivedGaussianVaughanMellinNormal z = archivedGaussianVaughanMellin z := by
  rw [archivedGaussianVaughanMellinNormal,
    toMeromorphicNFOn_eq_toMeromorphicNFAt vaughanMellin_meromorphic (mem_univ z)]
  exact congrFun (toMeromorphicNFAt_eq_self.mpr
    (archivedGaussianVaughanMellin_analytic hz).meromorphicNFAt) z

private theorem vaughanMellin_local_at_zero {ρ : ℂ} (hρ : archivedGaussianFactor ρ = 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ b : ℂ → ℂ, AnalyticAt ℂ b ρ ∧
      ∀ᶠ z in 𝓝[≠] ρ, archivedGaussianVaughanMellin z =
        (-(n : ℂ) * archivedGaussianVaughanMultiplier ρ) / (z - ρ) + b z := by
  have hG := archivedGaussianFactor_entire.analyticAt ρ
  have hfinite : analyticOrderAt archivedGaussianFactor ρ ≠ ⊤ := by
    intro htop
    have hzero : archivedGaussianFactor =ᶠ[𝓝 ρ] fun _ => 0 := analyticOrderAt_eq_top.mp htop
    have hall := AnalyticOnNhd.eq_of_eventuallyEq
      (fun z _ => archivedGaussianFactor_entire.analyticAt z) analyticOnNhd_const hzero
    exact quartic_gaussian_one_ne_zero (congrFun hall 1)
  let n := analyticOrderNatAt archivedGaussianFactor ρ
  have hn : analyticOrderAt archivedGaussianFactor ρ = n :=
    (Nat.cast_analyticOrderNatAt hfinite).symm
  have hn₀ : n ≠ 0 := by
    intro h
    exact (hG.analyticOrderAt_ne_zero.mpr hρ) (by simpa [h] using hn)
  obtain ⟨b, hb, hnear⟩ := gaussianNegLogDeriv_local hG hn
  let M := archivedGaussianVaughanMultiplier
  have hM := archivedGaussianVaughanMultiplier_entire.analyticAt ρ
  refine ⟨n, Nat.pos_of_ne_zero hn₀, fun z => dslope M ρ z * (-(n : ℂ)) + M z * b z,
    ((Deduction.poleData_dslope hM).mul analyticAt_const).add (hM.mul hb), ?_⟩
  filter_upwards [hnear, self_mem_nhdsWithin] with z hz hne
  change z ≠ ρ at hne
  rw [archivedGaussianVaughanMellin, hz, dslope_of_ne _ hne, slope_def_field]
  change M z * (-(n : ℂ) / (z - ρ) + b z) =
    (-(n : ℂ) * M ρ) / (z - ρ) + ((M z - M ρ) / (z - ρ) * -(n : ℂ) + M z * b z)
  ring

theorem archivedGaussianVaughanMellinNormal_analytic {z : ℂ}
    (hz : z ∉ archivedGaussianVaughanDetectedPoles) :
    AnalyticAt ℂ archivedGaussianVaughanMellinNormal z := by
  have hNormal := meromorphicNFOn_toMeromorphicNFOn archivedGaussianVaughanMellin
    Set.univ (mem_univ z)
  have hEq := vaughanMellinNormal_eventuallyEq z
  by_cases hG : archivedGaussianFactor z = 0
  · have hM : archivedGaussianVaughanMultiplier z = 0 := by
      by_contra hm
      exact hz ⟨hG, hm⟩
    obtain ⟨n, _, b, hb, hnear⟩ := vaughanMellin_local_at_zero hG
    simp only [hM, mul_zero, zero_div, zero_add] at hnear
    have h := (hNormal.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hb.meromorphicNFAt).mp
      (hEq.trans hnear)
    exact hb.congr h.symm
  · have ha := archivedGaussianVaughanMellin_analytic hG
    have h := (hNormal.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds ha.meromorphicNFAt).mp hEq
    exact ha.congr h.symm

theorem archivedGaussianVaughanMellinNormal_pole {z : ℂ}
    (hz : z ∈ archivedGaussianVaughanDetectedPoles) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ b : ℂ → ℂ, AnalyticAt ℂ b z ∧
      ∀ᶠ w in 𝓝[≠] z, archivedGaussianVaughanMellinNormal w = c / (w - z) + b w := by
  obtain ⟨n, hn, b, hb, hnear⟩ := vaughanMellin_local_at_zero hz.1
  exact ⟨_, mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hn.ne')) hz.2, b, hb,
    (vaughanMellinNormal_eventuallyEq z).trans hnear⟩

#print axioms archivedGaussianVaughanMellinNormal_eq
#print axioms archivedGaussianVaughanMellinNormal_analytic
#print axioms archivedGaussianVaughanMellinNormal_pole

end
end AlpogeSuperZeta
