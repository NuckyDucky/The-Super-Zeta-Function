import GaussianVaughanWindowCriterion

/-! At a Gaussian zero hidden by the seventh-scale multiplier,
reflection gives another zero closer to the real fixed point 7/8. -/

namespace AlpogeSuperZeta

open Complex Filter QuarticModel
open scoped Topology

noncomputable section

private theorem gaussianVaughan_reflect_of_multiplier_zero {w : ℂ}
    (hleft : 1 / 2 < w.re) (hright : w.re < 1)
    (hM : archivedGaussianVaughanMultiplier w = 0) :
    1 / 2 < (1 - w / 7).re ∧ (1 - w / 7).re < 1 ∧
      archivedGaussianFactor (1 - w / 7) = 0 := by
  have hRe : (1 - w / 7).re = 1 - w.re / 7 := by
    rw [sub_re, one_re, div_ofNat_re]
  have hleft' : 1 / 2 < (1 - w / 7).re := by rw [hRe]; linarith
  have hright' : (1 - w / 7).re < 1 := by rw [hRe]; linarith
  refine ⟨hleft', hright', (archivedGaussianFactor_zero_iff_mellin (by linarith)).mpr ?_⟩
  rw [archivedMellin_functional_equation]
  unfold archivedGaussianVaughanMultiplier at hM
  have h := (mul_eq_zero.mp hM).resolve_left (gaussianHalfScale_zero_ne_zero hleft).2
  exact (div_eq_zero_iff.mp h).resolve_right (by norm_num)

/-- The same multiplier detects at least one upper-right zero if any
upper-right Gaussian zero exists. Only the value at the real fixed
point is needed for the reflection descent. -/
theorem archivedGaussianVaughan_detects_some_zero
    (hFixed : archivedMellin (7 / 8 : ℂ) ≠ 0)
    {w : ℂ} (hleft : 1 / 2 < w.re) (hright : w.re < 1)
    (hw : archivedGaussianFactor w = 0) :
    ∃ z : ℂ, 1 / 2 < z.re ∧ z.re < 1 ∧ archivedGaussianFactor z = 0 ∧
      archivedGaussianVaughanMultiplier z ≠ 0 := by
  by_contra h
  have hHidden (z : ℂ) (hl : 1 / 2 < z.re) (hr : z.re < 1)
      (hz : archivedGaussianFactor z = 0) : archivedGaussianVaughanMultiplier z = 0 := by
    by_contra hn
    exact h ⟨z, hl, hr, hz, hn⟩
  let c : ℂ := 7 / 8
  let r : ℂ := -(1 / 7)
  let z (n : ℕ) := c + r ^ n * (w - c)
  have hz0 : z 0 = w := by simp [z]
  have hzstep (n : ℕ) : z (n + 1) = 1 - z n / 7 := by
    dsimp [z, c, r]
    rw [pow_succ]
    ring
  have hZeros (n : ℕ) : 1 / 2 < (z n).re ∧ (z n).re < 1 ∧ archivedGaussianFactor (z n) = 0 := by
    induction n with
    | zero => simpa only [hz0] using And.intro hleft (And.intro hright hw)
    | succ n ih =>
      rw [hzstep n]
      exact gaussianVaughan_reflect_of_multiplier_zero ih.1 ih.2.1 (hHidden _ ih.1 ih.2.1 ih.2.2)
  have hrNorm : ‖r‖ < 1 := by
    dsimp [r]
    rw [norm_neg, norm_div, norm_one, show (7 : ℂ) = ((7 : ℕ) : ℂ) by norm_num,
      Complex.norm_natCast]
    norm_num
  have hPow : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hrNorm
  have hLim : Tendsto z atTop (𝓝 c) := by
    have hC : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    simpa only [z, zero_mul, add_zero] using hC.add (hPow.mul_const (w - c))
  have hCont : ContinuousAt archivedMellin c :=
    (archivedMellin_differentiable archivedTheta_reflection).continuous.continuousAt
  have hLimit : Tendsto (fun n => archivedMellin (z n)) atTop (𝓝 (archivedMellin c)) :=
    hCont.tendsto.comp hLim
  have hzM (n : ℕ) : archivedMellin (z n) = 0 :=
    (archivedGaussianFactor_zero_iff_mellin (by linarith [(hZeros n).1])).mp (hZeros n).2.2
  have hzero : Tendsto (fun n => archivedMellin (z n)) atTop (𝓝 0) := by
    simp only [hzM, tendsto_const_nhds]
  exact hFixed (tendsto_nhds_unique hLimit hzero)

theorem archivedGaussianVaughan_detects_some_zero_of_real_pos
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    {w : ℂ} (hleft : 1 / 2 < w.re) (hright : w.re < 1)
    (hw : archivedGaussianFactor w = 0) :
    ∃ z : ℂ, 1 / 2 < z.re ∧ z.re < 1 ∧ archivedGaussianFactor z = 0 ∧
      archivedGaussianVaughanMultiplier z ≠ 0 := by
  apply archivedGaussianVaughan_detects_some_zero _ hleft hright hw
  have hp : 0 < (archivedMellin (((7 / 8 : ℝ) : ℂ))).re := by
    rw [archivedMellin_eq_quartic_real_formula]
    exact hpos (7 / 8)
  rw [show (((7 / 8 : ℝ)) : ℂ) = (7 / 8 : ℂ) by norm_num] at hp
  intro h
  simp [h] at hp

#check archivedGaussianVaughan_detects_some_zero_of_real_pos
#print axioms archivedGaussianVaughan_detects_some_zero
#print axioms archivedGaussianVaughan_detects_some_zero_of_real_pos

end
end AlpogeSuperZeta
