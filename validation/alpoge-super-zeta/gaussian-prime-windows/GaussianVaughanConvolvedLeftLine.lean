import GaussianVaughanLeftLineGamma
import GaussianVaughanGaussianStrip

/-! Reflect the actual convolved Mellin transform and bound it on
each of the integer-spaced negative contours. -/

namespace AlpogeSuperZeta

open Complex MeasureTheory QuarticModel

noncomputable section

def archivedGaussianVaughanConvolvedMellin (z : ℂ) : ℂ :=
  archivedGaussianVaughanMultiplier z * archivedGaussianFactor z

theorem archivedGaussianVaughanConvolvedMellin_entire :
    Differentiable ℂ archivedGaussianVaughanConvolvedMellin :=
  archivedGaussianVaughanMultiplier_entire.mul archivedGaussianFactor_entire

theorem archivedGaussianFactor_norm_on_right {a : ℝ} (ha : 1 < a) :
    ∃ B ≥ 0, ∀ z : ℂ, a ≤ z.re → ‖archivedGaussianFactor z‖ ≤ B := by
  let b := fun n : ℕ => ‖LSeries.term signedIdealCoefficients (a : ℂ) n‖
  have hb : Summable b := (archivedGaussianFactor_hasSum (w := (a : ℂ))
    (by simpa using ha)).LSeriesSummable.norm
  refine ⟨∑' n, b n, tsum_nonneg (fun _ => norm_nonneg _), fun z hz => ?_⟩
  have hnorm : ∀ n, ‖LSeries.term signedIdealCoefficients z n‖ ≤ b n :=
    fun n => LSeries.norm_term_le_of_re_le_re _ (s := (a : ℂ)) (by simpa using hz) n
  have h := hb.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
  rw [← (archivedGaussianFactor_hasSum (ha.trans_le hz)).LSeries_eq]
  exact (norm_tsum_le_tsum_norm h).trans (h.tsum_le_tsum hnorm hb)

/-- Reflect both actual readings and keep the Gamma quotient grouped for
the integer-line estimate. -/
theorem archivedGaussianVaughanConvolvedMellin_reflect {z : ℂ} (hz : z.re < 0) :
    archivedGaussianVaughanConvolvedMellin z =
      gaussianScaleDifference (1 / 2) z *
        archivedGaussianFactor (1 - z / 7) * archivedGaussianFactor (1 - z) *
        (archivedThetaScale : ℂ) ^ (2 - 15 * z / 7) *
        ((Gamma (1 - z) / Gamma z) * Gamma (1 - z / 7)) / 7 := by
  let c : ℂ := archivedThetaScale
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have hpow : c ^ (1 - z) * (c ^ z)⁻¹ = c ^ (1 - 2 * z) := by
    rw [← cpow_neg, ← cpow_add _ _ hc]
    congr 1
    ring
  have hg : archivedGaussianFactor z = c ^ (1 - 2 * z) *
      (Gamma (1 - z) / Gamma z) * archivedGaussianFactor (1 - z) := by
    conv_lhs =>
      rw [archivedGaussianFactor, ← archivedMellin_functional_equation z,
        archivedMellin_eq_gaussian_completion (by simp [sub_re]; linarith : 0 < (1 - z).re)]
    rw [← hpow]
    ring
  have hRight : 0 < (1 - z / 7).re := by
    simp only [sub_re, one_re, div_ofNat_re]
    linarith
  rw [archivedGaussianVaughanConvolvedMellin, archivedGaussianVaughanMultiplier, hg,
    ← archivedMellin_functional_equation (z / 7), archivedMellin_eq_gaussian_completion hRight]
  have hBoth : c ^ (1 - z / 7) * c ^ (1 - 2 * z) = c ^ (2 - 15 * z / 7) := by
    rw [← cpow_add _ _ hc]
    congr 1
    ring
  rw [← hBoth]
  ring

theorem gaussianScaleDifference_norm_on_right {a σ : ℝ} {z : ℂ} (h : σ ≤ z.re) :
    ‖gaussianScaleDifference a z‖ ≤ 1 + Real.exp ((a - σ) * Real.log 2) := by
  unfold gaussianScaleDifference
  refine (norm_sub_le _ _).trans ?_
  rw [norm_one, norm_exp, mul_re, ofReal_re, ofReal_im, sub_re, ofReal_re, mul_zero, sub_zero]
  exact add_le_add_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right (sub_le_sub_left h a)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))) _

def gaussianVaughanLeftPoint (N : ℕ) (t : ℝ) : ℂ :=
  ((-((7 * N : ℕ) : ℝ) : ℝ) : ℂ) + (t : ℂ) * I

@[simp] theorem gaussianVaughanLeftPoint_re (N : ℕ) (t : ℝ) :
    (gaussianVaughanLeftPoint N t).re = -((7 * N : ℕ) : ℝ) := by
  simp [gaussianVaughanLeftPoint, mul_re]

@[simp] theorem gaussianVaughanLeftPoint_im (N : ℕ) (t : ℝ) :
    (gaussianVaughanLeftPoint N t).im = t := by
  simp [gaussianVaughanLeftPoint, mul_im]

private theorem gaussianScaleDifference_on_leftPoint (N : ℕ) (t : ℝ) :
    ‖gaussianScaleDifference (1 / 2) (gaussianVaughanLeftPoint N t)‖ ≤
      ((2 : ℝ) ^ (7 : ℕ)) ^ (N + 1) := by
  refine (gaussianScaleDifference_norm_on_right
    (σ := -((7 * N : ℕ) : ℝ)) (by simp)).trans ?_
  have hd : (1 / 2 : ℝ) - (-((7 * N : ℕ) : ℝ)) ≤ ((7 * N + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hExp : Real.exp (((7 * N + 1 : ℕ) : ℝ) * Real.log 2) = (2 : ℝ) ^ (7 * N + 1) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  calc
    _ ≤ 1 + (2 : ℝ) ^ (7 * N + 1) := by
      rw [← hExp]
      exact add_le_add_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hd
        (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)))) _
    _ ≤ (2 : ℝ) ^ ((7 * N + 1) + 1) := by
      rw [pow_succ (2 : ℝ) (7 * N + 1)]
      linarith [one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := 7 * N + 1)]
    _ ≤ _ := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)

private theorem archivedThetaScale_on_leftPoint (N : ℕ) (t : ℝ) :
    ‖(archivedThetaScale : ℂ) ^ (2 - 15 * gaussianVaughanLeftPoint N t / 7)‖ ≤
      ((max 1 archivedThetaScale) ^ (15 : ℕ)) ^ (N + 1) := by
  have hre : (2 - 15 * gaussianVaughanLeftPoint N t / 7).re =
      ((2 + 15 * N : ℕ) : ℝ) := by
    simp only [sub_re, div_ofNat_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero,
      gaussianVaughanLeftPoint_re]
    push_cast
    ring
  rw [norm_cpow_eq_rpow_re_of_pos archivedThetaScale_pos, hre, Real.rpow_natCast, ← pow_mul]
  calc
    _ ≤ (max 1 archivedThetaScale) ^ (2 + 15 * N) :=
      pow_le_pow_left₀ archivedThetaScale_pos.le (le_max_right _ _) _
    _ ≤ _ := pow_le_pow_right₀ (le_max_left _ _) (by omega)

theorem archivedGaussianVaughanConvolvedMellin_left_pointwise :
    ∃ B ≥ 1, ∀ N ≥ 1, ∀ t : ℝ,
      ‖archivedGaussianVaughanConvolvedMellin (gaussianVaughanLeftPoint N t)‖ ≤
        B ^ (N + 1) * ((7 * N : ℕ) + 1 + |t| : ℝ) ^ (15 * N + 6) *
          Real.exp (-(Real.pi * |t| / 14)) := by
  obtain ⟨B, hB, hb⟩ := archivedGaussianFactor_norm_on_right (a := 2) (by norm_num)
  let P := (max 1 archivedThetaScale) ^ (15 : ℕ)
  let Q := max 1 (96 * B * B / 7)
  let R := (2 : ℝ) ^ (7 : ℕ)
  have hP : 1 ≤ P := one_le_pow₀ (le_max_left _ _)
  have hQ : 1 ≤ Q := le_max_left _ _
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  refine ⟨Q * R * P, ?_, fun N hN t => ?_⟩
  · calc
      (1 : ℝ) = (1 * 1) * 1 := by norm_num
      _ ≤ _ := by gcongr
  let z := gaussianVaughanLeftPoint N t
  have hz : z.re = -(7 * (N : ℝ)) := by simp [z, Nat.cast_mul]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hz₁ : 2 ≤ (1 - z).re := by simp only [sub_re, one_re, hz]; linarith
  have hz₂ : 2 ≤ (1 - z / 7).re := by simp only [sub_re, one_re, div_ofNat_re, hz]; linarith
  have hγ :
      ‖Gamma (1 - z) / Gamma z‖ * ‖Gamma (1 - z / 7)‖ ≤
        96 * ((7 * N : ℕ) + 1 + |t| : ℝ) ^ (15 * N + 6) *
          Real.exp (-(Real.pi * |t| / 14)) := by
    have hzΓ : z = -((7 * N : ℕ) : ℂ) + (t : ℂ) * I := by simp [z, gaussianVaughanLeftPoint]
    have h₁ : 1 - z = 1 + ((7 * N : ℕ) : ℂ) - (t : ℂ) * I := by rw [hzΓ]; ring
    have h₂ : 1 - z / 7 = 1 + (N : ℂ) - ((t / 7 : ℝ) : ℂ) * I := by
      rw [hzΓ]
      push_cast
      ring
    rw [h₁, h₂, hzΓ]
    exact gaussianGamma_leftLine_product_bound N t
  have hQP : 96 * B * B / 7 ≤ Q ^ (N + 1) :=
    (le_max_right _ _).trans (le_self_pow₀ hQ (by omega))
  change ‖archivedGaussianVaughanConvolvedMellin z‖ ≤ _
  rw [archivedGaussianVaughanConvolvedMellin_reflect (by linarith : z.re < 0),
    norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_ofNat]
  calc
    _ ≤ R ^ (N + 1) * B * B * P ^ (N + 1) *
        (96 * ((7 * N : ℕ) + 1 + |t| : ℝ) ^ (15 * N + 6) *
          Real.exp (-(Real.pi * |t| / 14))) / 7 := by
      have hD := gaussianScaleDifference_on_leftPoint N t
      have hS := archivedThetaScale_on_leftPoint N t
      have h₁ := hb _ hz₁
      have h₂ := hb _ hz₂
      gcongr
    _ = (96 * B * B / 7) * R ^ (N + 1) * P ^ (N + 1) *
        ((7 * N : ℕ) + 1 + |t| : ℝ) ^ (15 * N + 6) *
          Real.exp (-(Real.pi * |t| / 14)) := by ring
    _ ≤ _ := by rw [mul_pow, mul_pow]; gcongr

#print axioms archivedGaussianVaughanConvolvedMellin_reflect
#print axioms archivedGaussianVaughanConvolvedMellin_left_pointwise

end
end AlpogeSuperZeta
