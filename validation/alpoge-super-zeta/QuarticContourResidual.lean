import QuarticContourError
import GaussianEndpoint
import AlpogeAdapters
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LogDerivLocal
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Perfect

/-! Certify the boundary and the weighted count from one relative bound. -/
noncomputable section

namespace SuperZeta.WeightedContour

open Complex Metric Set Filter
open scoped Topology

private theorem sphere_accumulates {c z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ sphere c r) : NeBot (𝓝[sphere c r \ {z}] z) := by
  have hdim : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  have hTwo : (sphere c r).Nontrivial := by
    refine ⟨c+(r:ℂ), ?_, c-(r:ℂ), ?_, ?_⟩
    · simp [mem_sphere_iff_norm, norm_real, abs_of_pos hr]
    · rw [mem_sphere_iff_norm, show c-(r:ℂ)-c = -(r:ℂ) by ring, norm_neg, norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
    · intro he
      have h := congrArg Complex.re he
      simp only [add_re, sub_re, ofReal_re] at h
      linarith
  have hAcc := ((isPreconnected_sphere hdim c r).preperfect_of_nontrivial hTwo) z hz
  exact accPt_principal_iff_nhdsWithin.mp hAcc

/-- A zero makes the logarithmic derivative unbounded as the circle approaches
it. A finite relative residual bound therefore certifies boundary nonvanishing. -/
theorem sphere_nonzero_of_relative_residual {G B : ℂ → ℂ} {c x : ℂ} {r M : ℝ}
    (hr : 0 < r) (hG : Differentiable ℂ G) (hx : G x ≠ 0)
    (hB : ContinuousOn B (sphere c r))
    (bound : ∀ z ∈ sphere c r, ‖deriv G z - B z * G z‖ ≤ M * ‖G z‖) :
    ∀ z ∈ sphere c r, G z ≠ 0 := by
  intro ρ hρ hzero
  have ha : AnalyticAt ℂ G ρ := hG.analyticAt ρ
  have hn : ¬ ∀ᶠ z in 𝓝 ρ, G z = 0 := by
    intro h
    have hA : AnalyticOnNhd ℂ G univ := fun z _ => hG.analyticAt z
    exact hx ((hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ ρ) h) (mem_univ x))
  obtain ⟨m, hm, _, R, hR, hPole⟩ := Deduction.logDeriv_local ha hn
  have hm₀ : (m : ℂ) ≠ 0 := by
    exact_mod_cast (fun h : m = 0 => (hm.mp h) hzero)
  let p := 𝓝[sphere c r \ {ρ}] ρ
  have : NeBot p := sphere_accumulates hr hρ
  have hp₁ : p ≤ 𝓝[sphere c r] ρ := nhdsWithin_mono _ sdiff_subset
  have hp₂ : p ≤ 𝓝[≠] ρ := nhdsWithin_mono _ (fun _ hz => hz.2)
  have hSphere : ∀ᶠ z in p, z ∈ sphere c r := hp₁ eventually_mem_nhdsWithin
  have hAway : ∀ᶠ z in p, G z ≠ 0 := by
    rcases ha.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact (hn h).elim
    · exact hp₂ h
  have hnρ : ∀ᶠ z in p, z ≠ ρ := hp₂ self_mem_nhdsWithin
  have hP : ∀ᶠ z in p, deriv G z / G z = (m:ℂ)/(z-ρ) + R z := hp₂ hPole
  have hId : Tendsto (fun z : ℂ => z) p (𝓝 ρ) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hSub : Tendsto (fun z : ℂ => z-ρ) p (𝓝 (0:ℂ)) := by
    have hc : Tendsto (fun _ : ℂ => ρ) p (𝓝 ρ) := tendsto_const_nhds
    simpa only [sub_self] using hId.sub hc
  have hDiff : Tendsto (fun z => R z-B z) p (𝓝 (R ρ-B ρ)) :=
    (hR.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).sub
      ((hB ρ hρ).tendsto.mono_left hp₁)
  have hlim : Tendsto (fun z => ‖(m:ℂ)+(z-ρ)*(R z-B z)‖) p (𝓝 ‖(m:ℂ)‖) := by
    simpa only [zero_mul, add_zero] using (tendsto_const_nhds.add (hSub.mul hDiff)).norm
  have hlim₀ : Tendsto (fun z => M * ‖z-ρ‖) p (𝓝 (0:ℝ)) := by
    simpa only [norm_zero, mul_zero] using tendsto_const_nhds.mul hSub.norm
  have hEventually : ∀ᶠ z in p, ‖(m:ℂ)+(z-ρ)*(R z-B z)‖ ≤ M * ‖z-ρ‖ := by
    filter_upwards [hSphere,hAway,hnρ,hP] with z hz hgz hzρ hPoleEq
    have hq : ‖deriv G z / G z - B z‖ ≤ M := by
      apply (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hgz)).mp
      rw [← norm_mul, sub_mul, div_mul_cancel₀ _ hgz]
      exact bound z hz
    have he : (m:ℂ)+(z-ρ)*(R z-B z) = (z-ρ)*(deriv G z / G z-B z) := by
      rw [hPoleEq]
      field_simp [sub_ne_zero.mpr hzρ]
      ring
    rw [he, norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left hq (norm_nonneg _)
  exact hm₀ (norm_le_zero_iff.mp (le_of_tendsto_of_tendsto hlim hlim₀ hEventually))

#print axioms sphere_nonzero_of_relative_residual

end SuperZeta.WeightedContour

namespace QuarticModel

open Complex Metric Set SuperZeta.WeightedContour AlpogeSuperZeta
open scoped ComplexConjugate Topology

/-- One division-free bound for the archived Gaussian factor certifies both
disks. The holomorphic comparison is the derivative of an Euler remainder
minus twice the holomorphic model for the signed detector. -/
theorem archivedRightDisk_exclusion_of_relative_residual {T e : ℝ} {H P : ℂ → ℂ}
    (hh : DifferentiableOn ℂ H {w : ℂ | 1/2 < w.re}) (hp : Differentiable ℂ P)
    (bound : ∀ z ∈ sphere (archivedRightCenter T) (31/2048),
      ‖deriv archivedGaussianFactor z - (deriv H z - 2*P z)*archivedGaussianFactor z‖
        ≤ 2*e * ‖archivedGaussianFactor z‖)
    (small : e < 1024/31)
    {w : ℂ} (hw : w ∈ closedBall (archivedRightCenter T) (31/2048)) :
    archivedGaussianFactor w ≠ 0 ∧ archivedGaussianFactor (1-conj w) ≠ 0 := by
  have hO : IsOpen {z : ℂ | 1/2 < z.re} := isOpen_lt continuous_const continuous_re
  have hB : ContinuousOn (fun z => deriv H z - 2*P z) (sphere (archivedRightCenter T) (31/2048)) := by
    intro z hz
    have hright : (1/2:ℝ) < z.re := by linarith [archivedRightDisk_horizontal_gap (sphere_subset_closedBall hz)]
    have hloc : {q : ℂ | 1/2 < q.re} ∈ 𝓝 z := hO.mem_nhds hright
    exact (((hh.deriv hO).continuousOn.continuousAt hloc).sub
      (continuousAt_const.mul hp.continuous.continuousAt)).continuousWithinAt
  have hn := sphere_nonzero_of_relative_residual (by norm_num)
    (archivedGaussianFactor_differentiable archivedTheta_reflection) quartic_gaussian_one_ne_zero hB bound
  let S (z : ℂ) := (deriv H z - logDeriv archivedGaussianFactor z)/2
  have hid (z : ℂ) (hz : z ∈ sphere (archivedRightCenter T) (31/2048)) :
      2*S z*archivedGaussianFactor z = deriv H z*archivedGaussianFactor z - deriv archivedGaussianFactor z := by
    simp only [S, logDeriv_apply]
    field_simp [hn z hz]
  have he (z : ℂ) (hz : z ∈ sphere (archivedRightCenter T) (31/2048)) : ‖S z-P z‖ ≤ e := by
    have hpos : 0 < 2 * ‖archivedGaussianFactor z‖ := mul_pos (by norm_num) (norm_pos_iff.mpr (hn z hz))
    apply (mul_le_mul_iff_left₀ hpos).mp
    have hscale : ‖2*(S z-P z)*archivedGaussianFactor z‖ = ‖S z-P z‖ * (2*‖archivedGaussianFactor z‖) := by
      rw [norm_mul, norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
      ring
    rw [← hscale]
    have hneg : 2*(S z-P z)*archivedGaussianFactor z =
        -(deriv archivedGaussianFactor z - (deriv H z-2*P z)*archivedGaussianFactor z) := by
      linear_combination hid z hz
    rw [hneg, norm_neg]
    exact (bound z hz).trans_eq (by ring)
  exact archivedRightDisk_exclusion_of_detector_error hh hp hn hid he small hw

/-- With the rational cofactor theorem supplied, the same residual bound
excludes zeros of the actual Dedekind continuation at the two inputs. -/
theorem archivedQuartic_disk_exclusion_of_relative_residual (hD : DirichletLZerosOnLine)
    {T e : ℝ} {H P : ℂ → ℂ}
    (hh : DifferentiableOn ℂ H {w : ℂ | 1/2 < w.re}) (hp : Differentiable ℂ P)
    (bound : ∀ z ∈ sphere (archivedRightCenter T) (31/2048),
      ‖deriv archivedGaussianFactor z - (deriv H z - 2*P z)*archivedGaussianFactor z‖
        ≤ 2*e * ‖archivedGaussianFactor z‖)
    (small : e < 1024/31)
    {w : ℂ} (hw : w ∈ closedBall (archivedRightCenter T) (31/2048)) :
    archivedQuarticZeta w ≠ 0 ∧ archivedQuarticZeta (1-conj w) ≠ 0 := by
  obtain ⟨hGaussian,hMirror⟩ := archivedRightDisk_exclusion_of_relative_residual hh hp bound small hw
  obtain ⟨hR,hB⟩ := cofactors_on_line hD
  have hright : (1/2:ℝ) < w.re := by linarith [archivedRightDisk_horizontal_gap hw]
  have hnorm : ‖w-archivedRightCenter T‖ ≤ (31/2048:ℝ) := by
    simpa only [mem_closedBall, dist_eq_norm] using hw
  have htop := (abs_le.mp ((abs_re_le_norm _).trans hnorm)).2
  change w.re - 33/64 ≤ 31/2048 at htop
  have hupper : w.re < 1 := by linarith
  have applyAt (z : ℂ) (hz₀ : 0 < z.re) (hz₁ : z.re < 1) (hoff : z.re ≠ 1/2)
      (hg : archivedGaussianFactor z ≠ 0) : archivedQuarticZeta z ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (fun he => hoff (hR z hz₀ hz₁ he))
      (fun he => hoff (hB z hz₀ hz₁ he))) hg
  have hmir : (1-conj w).re = 1-w.re := by simp
  exact ⟨applyAt w (by linarith) hupper hright.ne' hGaussian,
    applyAt (1-conj w) (by rw [hmir]; linarith) (by rw [hmir]; linarith)
      (by rw [hmir]; linarith) hMirror⟩

#print axioms archivedRightDisk_exclusion_of_relative_residual
#print axioms archivedQuartic_disk_exclusion_of_relative_residual

end QuarticModel
end
