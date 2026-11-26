import AlpogeAdapters
import GaussianEndpoint
import Mathlib.Analysis.Meromorphic.Order

/-! Seventh-power dilation sends every positive-real-part Gaussian zero
to a pole of the exponentially weighted seventh-power-free ideal reading. -/

namespace AlpogeSuperZeta

open Complex QuarticModel FieldTarget ArtinPrimitiveRootsConjecture

noncomputable section

/-- A rational boundary strictly above the external number-field bound. -/
def archivedGaussianKnownBoundary : ℝ := 873333 / 1000000

/-- Mellin expression for the exponentially weighted seventh-power-free ideal sum. -/
def archivedGaussianSeventhFreeMellin (s : ℂ) : ℂ :=
  Gamma s * (archivedGaussianFactor s / archivedGaussianFactor (7 * s))

/-- The signed theta weight after writing the cutoff as the seventh
power of a variable measured on the ideal-norm scale. -/
def archivedGaussianSeventhFreeKernel (v : ℝ) : ℝ :=
  archivedTheta (v ^ 7 / archivedThetaScale)

theorem archivedGaussianSeventhFreeKernel_reflect {v : ℝ} (hv : 0 < v) :
    archivedGaussianSeventhFreeKernel v =
      (v ^ 7)⁻¹ * archivedGaussianSeventhFreeKernel v⁻¹ := by
  simpa only [archivedGaussianSeventhFreeKernel, inv_pow] using
    archivedTheta_reflection (v ^ 7) (pow_pos hv _)

theorem archivedGaussianSeventhFreeKernel_upperTail {v : ℝ}
    (hv : 2 ≤ v ^ 7 / archivedThetaScale) :
    |archivedGaussianSeventhFreeKernel v| ≤ 2 * Real.exp (-(v ^ 7 / archivedThetaScale)) :=
  archivedTheta_exp_bound hv

theorem archivedGaussianSeventhFreeKernel_lowerTail {v : ℝ} (hv : 0 < v)
    (h : 2 ≤ (v ^ 7)⁻¹ / archivedThetaScale) :
    |archivedGaussianSeventhFreeKernel v| ≤
      (v ^ 7)⁻¹ * (2 * Real.exp (-((v ^ 7)⁻¹ / archivedThetaScale))) := by
  have hpos : 0 < (v ^ 7)⁻¹ := inv_pos.mpr (pow_pos hv _)
  rw [archivedGaussianSeventhFreeKernel_reflect hv, abs_mul, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [archivedGaussianSeventhFreeKernel, inv_pow] using archivedTheta_exp_bound h)
    hpos.le

private theorem archivedGaussian_zero_reflect {w : ℂ} (hw : 0 < w.re) (hw₁ : w.re < 1)
    (hz : archivedGaussianFactor w = 0) : archivedGaussianFactor (1 - w) = 0 := by
  have hr : 0 < (1 - w).re := by simpa [sub_re] using sub_pos.mpr hw₁
  rw [archivedGaussianFactor_zero_iff_mellin hr, archivedMellin_functional_equation]
  exact (archivedGaussianFactor_zero_iff_mellin hw).mp hz

/-- Reflection into the known zero-free half-plane protects the numerator. -/
theorem archivedGaussian_seventhFree_numerator_ne_zero
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : archivedGaussianFactor ρ = 0) :
    archivedGaussianFactor (ρ / 7) ≠ 0 := by
  have hle : ρ.re ≤ archivedGaussianKnownBoundary := le_of_not_gt fun h => hFree ρ h hz
  have hs : 0 < (ρ / 7).re := by rw [div_ofNat_re]; positivity
  have hs' : (ρ / 7).re < 1 := by
    rw [div_ofNat_re]
    norm_num [archivedGaussianKnownBoundary] at hle
    linarith
  intro hzero
  apply hFree (1 - ρ / 7) ?_ (archivedGaussian_zero_reflect hs hs' hzero)
  rw [sub_re, one_re, div_ofNat_re]
  norm_num [archivedGaussianKnownBoundary] at hle ⊢
  linarith

private theorem gamma_analyticAt_of_re_pos {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gamma s := by
  have hΓ := differentiable_one_div_Gamma.analyticAt s
  have h := hΓ.inv (inv_ne_zero (Gamma_ne_zero_of_re_pos hs))
  change AnalyticAt ℂ (fun w => ((Gamma w)⁻¹)⁻¹) s at h
  simpa only [inv_inv] using h

/-- The pole has exactly the multiplicity of the original Gaussian zero. -/
theorem archivedGaussian_seventhFree_order
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hz : archivedGaussianFactor ρ = 0) :
    ∃ n : ℕ, 0 < n ∧ meromorphicOrderAt archivedGaussianFactor ρ = (n : ℤ) ∧
      meromorphicOrderAt archivedGaussianSeventhFreeMellin (ρ / 7) = (-(n : ℤ) : ℤ) := by
  let s := ρ / 7
  let scale : ℂ → ℂ := fun w => 7 * w
  have hs : 0 < s.re := by dsimp [s]; rw [div_ofNat_re]; positivity
  have hscale : scale s = ρ := by dsimp [scale, s]; ring
  have hscale₁ : AnalyticAt ℂ scale s := analyticAt_const.mul analyticAt_id
  have hscale₂ : deriv scale s ≠ 0 := by simp [scale]
  have hG : ∀ w, AnalyticAt ℂ archivedGaussianFactor w := archivedGaussianFactor_entire.analyticAt
  have hDen := (hG (scale s)).comp hscale₁
  have hcomp : meromorphicOrderAt (archivedGaussianFactor ∘ scale) s =
      meromorphicOrderAt archivedGaussianFactor ρ :=
    (meromorphicOrderAt_comp_of_deriv_ne_zero hscale₁ hscale₂).trans (by rw [hscale])
  have hNum : meromorphicOrderAt archivedGaussianFactor s = 0 := by
    rw [(hG s).meromorphicOrderAt_eq,
      (hG s).analyticOrderAt_eq_zero.mpr (archivedGaussian_seventhFree_numerator_ne_zero hFree hρ hz)]
    rfl
  have hord :
      meromorphicOrderAt archivedGaussianSeventhFreeMellin s =
        0 - meromorphicOrderAt archivedGaussianFactor ρ := by
    change meromorphicOrderAt (Gamma * (archivedGaussianFactor /
      (archivedGaussianFactor ∘ scale))) s = _
    rw [meromorphicOrderAt_mul_of_ne_zero (gamma_analyticAt_of_re_pos hs)
      (Gamma_ne_zero_of_re_pos hs), meromorphicOrderAt_div (hG s).meromorphicAt hDen.meromorphicAt,
      hNum, hcomp]
  have hOn : AnalyticOnNhd ℂ archivedGaussianFactor Set.univ := fun w _ => hG w
  have hfinite : analyticOrderAt archivedGaussianFactor ρ ≠ ⊤ :=
    hOn.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ 1) (Set.mem_univ ρ) (fun h => by
        apply quartic_gaussian_one_ne_zero
        exact (show (1 : ℂ) ∈ {z | archivedGaussianFactor z = 0} from
          mem_of_mem_nhds (analyticOrderAt_eq_top.mp h)))
  have hzero := (hG ρ).analyticOrderAt_ne_zero.mpr hz
  lift analyticOrderAt archivedGaussianFactor ρ to ℕ using hfinite with n hn
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by exact_mod_cast hzero)
  have hm : meromorphicOrderAt archivedGaussianFactor ρ = (n : ℤ) := by
    rw [(hG ρ).meromorphicOrderAt_eq, ← hn, ENat.map_natCast]
  refine ⟨n, hn0, hm, ?_⟩
  rw [hord, hm, ← WithTop.coe_zero, ← WithTop.LinearOrderedAddCommGroup.coe_sub, zero_sub]

/-- For the actual quartic the exponential transform excludes every
positive-real-part off-line Gaussian zero if it is analytic to the
right of one fourteenth. The converse uses the same zero-free input. -/
theorem archivedQuarticRH_iff_seventhFree_analytic (hD : DirichletLZerosOnLine)
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0) :
    DedekindZetaRH QuarticModel.K ↔
      ∀ s : ℂ, 1 / 14 < s.re → AnalyticAt ℂ archivedGaussianSeventhFreeMellin s := by
  have hG : ∀ w, AnalyticAt ℂ archivedGaussianFactor w := archivedGaussianFactor_entire.analyticAt
  constructor
  · intro hRH s hs
    have hpos : 0 < s.re := by linarith
    have hw : 1 / 2 < (7 * s).re := by simp [mul_re]; linarith
    have hden : archivedGaussianFactor (7 * s) ≠ 0 := by
      by_cases h : (7 * s).re < 1
      · intro hz
        have hline := (archivedQuarticRH_iff_three_factors.mp hRH).2.2 _ (by linarith) h hz
        linarith
      · exact hFree _ ((show archivedGaussianKnownBoundary < 1 by
          norm_num [archivedGaussianKnownBoundary]).trans_le (le_of_not_gt h))
    exact (gamma_analyticAt_of_re_pos hpos).mul
      ((hG s).div ((hG (7 * s)).comp (analyticAt_const.mul analyticAt_id)) hden)
  · intro ha
    have hr (w : ℂ) (hw : 1 / 2 < w.re) : archivedGaussianFactor w ≠ 0 := by
      intro hz
      have hs : 1 / 14 < (w / 7).re := by rw [div_ofNat_re]; linarith
      obtain ⟨n, hn, _, hp⟩ :=
        archivedGaussian_seventhFree_order hFree (by linarith) hz
      have hA := (ha _ hs).meromorphicOrderAt_nonneg
      rw [hp] at hA
      norm_cast at hA
      exact (not_le_of_gt hn) (by omega)
    obtain ⟨hR, hB⟩ := cofactors_on_line hD
    refine archivedQuarticRH_iff_three_factors.mpr ⟨hR, hB, fun w h0 h1 hz => ?_⟩
    apply le_antisymm
    · exact le_of_not_gt fun h => hr w h hz
    · apply le_of_not_gt
      intro hl
      exact hr (1 - w) (by simp only [sub_re, one_re]; linarith)
        (archivedGaussian_zero_reflect h0 h1 hz)

#print axioms archivedGaussianSeventhFreeKernel_reflect
#print axioms archivedGaussianSeventhFreeKernel_upperTail
#print axioms archivedGaussianSeventhFreeKernel_lowerTail
#print axioms archivedGaussian_seventhFree_numerator_ne_zero
#print axioms archivedGaussian_seventhFree_order
#check archivedQuarticRH_iff_seventhFree_analytic
#print axioms archivedQuarticRH_iff_seventhFree_analytic

end
end AlpogeSuperZeta
