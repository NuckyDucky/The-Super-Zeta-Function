import GaussianVaughanConvolvedLeftLine
import GaussianVaughanGammaRatioStrip

/-! Decay on the entire strip from the inversion line to each of the
selected negative contours, for the exact convolved transform. -/

namespace AlpogeSuperZeta

open Complex QuarticModel

noncomputable section

private theorem thetaScale_power_le {z : ℂ} {a b : ℝ} (ha : a ≤ z.re) (hb : z.re ≤ b) :
    ‖(archivedThetaScale : ℂ) ^ z‖ ≤
      max (archivedThetaScale ^ a) (archivedThetaScale ^ b) := by
  rw [norm_cpow_eq_rpow_re_of_pos archivedThetaScale_pos]
  by_cases h : 1 ≤ archivedThetaScale
  · exact (Real.rpow_le_rpow_of_exponent_le h hb).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_exponent_ge archivedThetaScale_pos (le_of_not_ge h) ha).trans
      (le_max_left _ _)

private theorem gaussianFactor_reflected {z : ℂ} (hz : z.re < 1) :
    archivedGaussianFactor z =
      (archivedThetaScale : ℂ) ^ (1 - 2 * z) * (Gamma (1 - z) / Gamma z) *
        archivedGaussianFactor (1 - z) := by
  let c : ℂ := archivedThetaScale
  have hc : c ≠ 0 := ofReal_ne_zero.mpr archivedThetaScale_pos.ne'
  have hpow : c ^ (1 - z) * (c ^ z)⁻¹ = c ^ (1 - 2 * z) := by
    rw [← cpow_neg, ← cpow_add _ _ hc]
    congr 1
    ring
  conv_lhs =>
    rw [archivedGaussianFactor, ← archivedMellin_functional_equation z,
      archivedMellin_eq_gaussian_completion (by simp [sub_re]; linarith : 0 < (1 - z).re)]
  rw [← hpow]
  ring

theorem archivedGaussianFactor_norm_to_right_of_integer (n : ℕ) :
    ∃ B ≥ 0, ∀ z : ℂ, -(n : ℝ) ≤ z.re →
      ‖archivedGaussianFactor z‖ ≤ B * (1 + |z.im|) ^ (2 * (n + 5)) := by
  obtain ⟨C, hC, hSmall⟩ := archivedGaussianFactor_polynomial_on_strip
  obtain ⟨D, hD, hRight⟩ := archivedGaussianFactor_norm_on_right (a := 2) (by norm_num)
  obtain ⟨J, hJ, hRatio⟩ := gaussianGamma_ratio_norm_on_negative_strip n
  let P := max (archivedThetaScale ^ (3 : ℝ)) (archivedThetaScale ^ (1 + 2 * (n : ℝ)))
  have hP : 0 ≤ P := (Real.rpow_nonneg archivedThetaScale_pos.le _).trans (le_max_left _ _)
  let B := 64 * C + D + P * J * D
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, fun z hz => ?_⟩
  let T := 1 + |z.im|
  have hT : 1 ≤ T := le_add_of_nonneg_right (abs_nonneg _)
  by_cases h₁ : z.re ≤ -1
  · have hρ : 2 ≤ (1 - z).re := by rw [sub_re, one_re]; linarith
    have hScale : ‖(archivedThetaScale : ℂ) ^ (1 - 2 * z)‖ ≤ P := by
      apply thetaScale_power_le
      · norm_num [sub_re, mul_re]; linarith
      · norm_num [sub_re, mul_re]; linarith
    have hR := hRatio z hz h₁
    have hD' := hRight _ hρ
    rw [gaussianFactor_reflected (by linarith : z.re < 1), norm_mul, norm_mul]
    calc
      _ ≤ P * (J * T ^ (2 * (n + 5))) * D := by gcongr
      _ = (P * J * D) * T ^ (2 * (n + 5)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left (by positivity : 0 ≤ 64 * C + D)) (by positivity)
  by_cases h₂ : z.re ≤ 2
  · have hGeom : ‖z + 2‖ ≤ 4 * T := by
      refine (Complex.norm_le_abs_re_add_abs_im (z + 2)).trans ?_
      rw [add_re, re_ofNat, add_im, im_ofNat, add_zero,
        abs_of_nonneg (by linarith : 0 ≤ z.re + 2)]
      dsimp only [T]
      linarith [abs_nonneg z.im]
    refine (hSmall z (le_of_not_ge h₁) h₂).trans ?_
    calc
      _ ≤ C * (4 * T) ^ (3 : ℕ) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hGeom _) hC
      _ = (64 * C) * T ^ (3 : ℕ) := by ring
      _ ≤ _ := by
        have hCB : 64 * C ≤ B := by
          dsimp [B]
          linarith [mul_nonneg (mul_nonneg hP hJ) hD]
        exact mul_le_mul hCB (pow_le_pow_right₀ hT (by omega)) (by positivity) hB
  have hDB : D ≤ B := by
    dsimp [B]
    linarith [mul_nonneg (mul_nonneg hP hJ) hD]
  exact (hRight z (le_of_not_ge h₂)).trans
    (hDB.trans (le_mul_of_one_le_right hB (one_le_pow₀ hT)))

theorem archivedGaussianVaughanConvolvedMellin_exponential_on_strip (N : ℕ) :
    ∃ B ≥ 0, ∀ z : ℂ, -((7 * N : ℕ) : ℝ) ≤ z.re → z.re ≤ 3 / 2 →
      ‖archivedGaussianVaughanConvolvedMellin z‖ ≤
        B * (1 + |z.im|) ^ (4 * (7 * N + 5) + (N + 5)) *
          Real.exp (-(Real.pi * |z.im| / 14)) := by
  obtain ⟨B, hB, hG⟩ := archivedGaussianFactor_norm_to_right_of_integer (7 * N)
  obtain ⟨D, hD, hΓ⟩ := gaussianGamma_fixed_positive_strip N
  let P := max (archivedThetaScale ^ (0 : ℝ)) (archivedThetaScale ^ (1 + (N : ℝ)))
  have hP : 0 ≤ P := (Real.rpow_nonneg archivedThetaScale_pos.le _).trans (le_max_left _ _)
  let R : ℝ := 1 + Real.exp ((1 / 2 - (-((7 * N : ℕ) : ℝ))) * Real.log 2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨R * B * P * D * B / 7, by positivity, fun z hl hr => ?_⟩
  let u := 1 - z / 7
  have hu : u.re = 1 - z.re / 7 := by
    change (1 - z / 7).re = _
    rw [sub_re, one_re, div_ofNat_re]
  have hu₁ : 1 / 2 ≤ u.re := by rw [hu]; linarith
  have hu₂ : u.re ≤ 1 + (N : ℝ) := by
    rw [hu]
    push_cast at hl
    linarith
  have him : |u.im| = |z.im| / 7 := by
    change |(1 - z / 7).im| = _
    rw [sub_im, one_im, zero_sub, abs_neg, div_ofNat_im, abs_div]
    norm_num
  let T := 1 + |z.im|
  have hc : 1 + |u.im| ≤ T := by rw [him]; dsimp [T]; linarith [abs_nonneg z.im]
  have hS : ‖(archivedThetaScale : ℂ) ^ u‖ ≤ P :=
    thetaScale_power_le (by linarith) hu₂
  let d := 2 * (7 * N + 5)
  have hGz : ‖archivedGaussianFactor z‖ ≤ B * T ^ d := hG z hl
  have hGu : ‖archivedGaussianFactor u‖ ≤ B * T ^ d :=
    (hG u ((neg_nonpos.mpr (by positivity)).trans (by linarith : 0 ≤ u.re))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc _) hB)
  have hGamma : ‖Gamma u‖ ≤ D * T ^ (N + 5) * Real.exp (-(Real.pi * |z.im| / 14)) := by
    refine (hΓ u hu₁ (by linarith)).trans ?_
    have he : Real.pi / 2 * |u.im| = Real.pi * |z.im| / 14 := by rw [him]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc _) hD) (Real.exp_pos _).le
  have hDiff : ‖gaussianScaleDifference (1 / 2) z‖ ≤ R := gaussianScaleDifference_norm_on_right hl
  change ‖(gaussianScaleDifference (1 / 2) z * (archivedMellin (z / 7) / 7)) *
    archivedGaussianFactor z‖ ≤ _
  rw [← archivedMellin_functional_equation (z / 7)]
  change ‖(gaussianScaleDifference (1 / 2) z * (archivedMellin u / 7)) *
    archivedGaussianFactor z‖ ≤ _
  rw [archivedMellin_eq_gaussian_completion (by linarith : 0 < u.re)]
  simp only [norm_mul, norm_div, norm_ofNat]
  calc
    _ ≤ (R * (((B * T ^ d) * P * (D * T ^ (N + 5) *
        Real.exp (-(Real.pi * |z.im| / 14)))) / 7)) * (B * T ^ d) := by gcongr
    _ = _ := by
      change _ = (R * B * P * D * B / 7) * T ^ (4 * (7 * N + 5) + (N + 5)) * _
      rw [show 4 * (7 * N + 5) + (N + 5) = d + (N + 5) + d by dsimp [d]; omega,
        pow_add T (d + (N + 5)), pow_add T d (N + 5)]
      ring

private theorem height_power_exp_le (k : ℕ) :
    ∃ C ≥ 0, ∀ t : ℝ, (1 + |t|) ^ k * Real.exp (-(Real.pi * |t| / 14)) ≤ C := by
  refine ⟨(k.factorial : ℝ) * (5 : ℝ) ^ k * Real.exp (1 / 5), by positivity, fun t => ?_⟩
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hp : (0 : ℝ) < (5 : ℝ) ^ k := by positivity
  have hx := Real.pow_div_factorial_le_exp (x := (1 + |t|) / 5) (by positivity) k
  rw [div_le_iff₀ hf, div_pow, div_le_iff₀ hp] at hx
  have hπ : (1 / 5 : ℝ) ≤ Real.pi / 14 := by linarith [Real.pi_gt_three]
  have hE : -(Real.pi * |t| / 14) ≤ -|t| / 5 := by
    linarith [mul_le_mul_of_nonneg_right hπ (abs_nonneg t)]
  calc
    _ ≤ (1 + |t|) ^ k * Real.exp (-|t| / 5) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hE) (by positivity)
    _ ≤ (Real.exp ((1 + |t|) / 5) * (k.factorial : ℝ) * 5 ^ k) * Real.exp (-|t| / 5) :=
      mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
    _ = ((k.factorial : ℝ) * 5 ^ k) *
        (Real.exp ((1 + |t|) / 5) * Real.exp (-|t| / 5)) := by ring
    _ = _ := by rw [← Real.exp_add, show (1 + |t|) / 5 + -|t| / 5 = 1 / 5 by ring]

theorem archivedGaussianVaughanConvolvedMellin_square_decay (N : ℕ) :
    ∃ C ≥ 0, ∀ z : ℂ, -((7 * N : ℕ) : ℝ) ≤ z.re → z.re ≤ 3 / 2 →
      ‖archivedGaussianVaughanConvolvedMellin z‖ ≤ C / ((1 + |z.im|) ^ (2 : ℕ)) := by
  obtain ⟨B, hB, h⟩ := archivedGaussianVaughanConvolvedMellin_exponential_on_strip N
  let d := 4 * (7 * N + 5) + (N + 5)
  obtain ⟨M, hM, hPow⟩ := height_power_exp_le (d + 2)
  refine ⟨B * M, mul_nonneg hB hM, fun z hl hr => ?_⟩
  let T := 1 + |z.im|
  apply (le_div_iff₀ (by positivity : 0 < T ^ (2 : ℕ))).mpr
  calc
    _ ≤ (B * T ^ d * Real.exp (-(Real.pi * |z.im| / 14))) * T ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right (h z hl hr) (by positivity)
    _ = B * (T ^ (d + 2) * Real.exp (-(Real.pi * |z.im| / 14))) := by rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hPow z.im) hB

#print axioms archivedGaussianFactor_norm_to_right_of_integer
#print axioms archivedGaussianVaughanConvolvedMellin_exponential_on_strip
#print axioms archivedGaussianVaughanConvolvedMellin_square_decay

end
end AlpogeSuperZeta
