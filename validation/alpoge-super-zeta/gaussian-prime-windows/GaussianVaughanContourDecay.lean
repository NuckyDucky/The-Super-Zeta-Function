import GaussianVaughanFilteredGrowth
import GaussianVaughanGaussianStrip

/-! Rapid vertical decay of the completed-prime Mellin transform on the
whole closed strip between its inversion line and the shifted contour. -/

namespace AlpogeSuperZeta

open Complex Metric QuarticModel

noncomputable section

private theorem gaussianFactor_norm_at_height :
    ∃ B ≥ 0, ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 →
      ‖archivedGaussianFactor z‖ ≤ B * (1 + |z.im|) ^ 3 := by
  obtain ⟨C, hC, hg⟩ := archivedGaussianFactor_polynomial_on_strip
  refine ⟨64 * C, by positivity, fun z h₁ h₂ => ?_⟩
  have hgeom : ‖z + 2‖ ≤ 4 * (1 + |z.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hp : 0 ≤ (z + 2).re := by simp [add_re]; linarith
    rw [abs_of_nonneg hp]
    norm_num [add_re, add_im]
    linarith [abs_nonneg z.im]
  refine (hg z h₁ h₂).trans ?_
  calc
    _ ≤ C * (4 * (1 + |z.im|)) ^ 3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hgeom _) hC
    _ = _ := by ring

private theorem gaussianFactor_deriv_at_height :
    ∃ B ≥ 0, ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 13 / 8 →
      ‖deriv archivedGaussianFactor z‖ ≤ B * (1 + |z.im|) ^ 3 := by
  obtain ⟨C, hC, hg⟩ := gaussianFactor_norm_at_height
  refine ⟨64 * C, by positivity, fun z hz₁ hz₂ => ?_⟩
  have hSphere (v : ℂ) (hv : v ∈ sphere z (1 / 8)) :
      ‖archivedGaussianFactor v‖ ≤ 8 * C * (1 + |z.im|) ^ 3 := by
    have hd : ‖v - z‖ = 1 / 8 := by simpa only [mem_sphere, dist_eq_norm] using hv
    have hre := Complex.abs_re_le_norm (v - z)
    rw [sub_re, hd, abs_le] at hre
    have him := Complex.abs_im_le_norm (v - z)
    rw [sub_im, hd] at him
    have hAbs : |v.im| ≤ 1 / 8 + |z.im| := by
      have hadd := abs_add_le (v.im - z.im) z.im
      rw [sub_add_cancel] at hadd
      linarith
    have hcmp : 1 + |v.im| ≤ 2 * (1 + |z.im|) := by linarith [abs_nonneg z.im]
    calc
      _ ≤ C * (1 + |v.im|) ^ 3 := hg v (by linarith [hre.1]) (by linarith [hre.2])
      _ ≤ C * (2 * (1 + |z.im|)) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hcmp _) hC
      _ = _ := by ring
  have hD := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0 : ℝ) < 1 / 8) archivedGaussianFactor_entire.diffContOnCl hSphere
  exact hD.trans (by ring_nf; exact le_rfl)

private theorem norm_scale_pow_le {z : ℂ} (hz₁ : 0 ≤ z.re) (hz₂ : z.re ≤ 1) :
    ‖(archivedThetaScale : ℂ) ^ z‖ ≤ max 1 archivedThetaScale := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos archivedThetaScale_pos]
  by_cases hs : 1 ≤ archivedThetaScale
  · exact (Real.rpow_le_rpow_of_exponent_le hs hz₂).trans
      (by rw [Real.rpow_one]; exact le_max_right _ _)
  · exact (Real.rpow_le_one archivedThetaScale_pos.le (le_of_not_ge hs) hz₁).trans
      (le_max_left _ _)

/-- The seventh-scale theta Mellin factor decays more rapidly than every
inverse power of the height, uniformly on the contour strip. -/
theorem archivedGaussianThetaMellin_rapid_decay (k : ℕ) :
    ∃ C ≥ 0, ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 13 / 8 →
      (1 + |z.im|) ^ k * ‖archivedMellin (z / 7) / 7‖ ≤ C := by
  obtain ⟨A, hA, hg⟩ := gaussianFactor_norm_at_height
  obtain ⟨B, hB, hΓ⟩ := gamma_rapid_decay_on_positive_strip
    (a := 3 / 56) (b := 13 / 56) (by norm_num) (by norm_num) (k + 3)
  let P := max 1 archivedThetaScale
  have hP : 0 ≤ P := zero_le_one.trans (le_max_left _ _)
  refine ⟨7 ^ k * A * P * B / 7, by positivity, fun z hz₁ hz₂ => ?_⟩
  let w : ℂ := z / 7
  have hwre : w.re = z.re / 7 := by simp [w, div_ofNat_re]
  have hwim : w.im = z.im / 7 := by simp [w, div_ofNat_im]
  have hw₁ : 3 / 56 ≤ w.re := by rw [hwre]; linarith
  have hw₂ : w.re ≤ 13 / 56 := by rw [hwre]; linarith
  have hn : (1 + |z.im|) ^ k ≤ (7 * (1 + |w.im|)) ^ k := by
    apply pow_le_pow_left₀ (by positivity)
    rw [hwim, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 7)]
    linarith
  have hC : ‖(archivedThetaScale : ℂ) ^ w‖ ≤ P :=
    norm_scale_pow_le (by linarith) (by linarith)
  have hL : ‖archivedGaussianFactor w‖ ≤ A * (1 + |w.im|) ^ 3 :=
    hg w (by linarith) (by linarith)
  change (1 + |z.im|) ^ k * ‖archivedMellin w / 7‖ ≤ _
  rw [archivedMellin_eq_gaussian_completion (by linarith : 0 < w.re), norm_div,
    norm_ofNat, norm_mul, norm_mul]
  calc
    _ ≤ (7 * (1 + |w.im|)) ^ k *
        ((A * (1 + |w.im|) ^ 3) * P * ‖Complex.Gamma w‖ / 7) := by gcongr
    _ = (7 ^ k * A * P / 7) *
        ((1 + |w.im|) ^ (k + 3) * ‖Complex.Gamma w‖) := by rw [pow_add, mul_pow]; ring
    _ ≤ (7 ^ k * A * P / 7) * B := mul_le_mul_of_nonneg_left (hΓ w hw₁ hw₂) (by positivity)
    _ = _ := by ring

/-- The continued transform for the archived Gaussian prime kernel has
arbitrarily many powers of vertical decay on the contour strip. -/
theorem archivedGaussianVaughanCompletedPrime_rapid_decay (hDir : DirichletLZerosOnLine)
    (k : ℕ) :
    ∃ C ≥ 0, ∀ z : ℂ, 3 / 8 ≤ z.re → z.re ≤ 13 / 8 →
      (1 + |z.im|) ^ k *
        ‖archivedGaussianVaughanPrimeContinuation archivedGaussianVaughanHigherMellin z‖ ≤ C := by
  obtain ⟨P, hP, he⟩ := archivedGaussianVaughanCompletedPrime_strip_envelope hDir
  obtain ⟨A, hA, hg⟩ := gaussianFactor_norm_at_height
  obtain ⟨B, hB, hd⟩ := gaussianFactor_deriv_at_height
  obtain ⟨M, hM, hm⟩ := archivedGaussianThetaMellin_rapid_decay (k + 4)
  refine ⟨(3 * B + 2 * P * A) * M, by positivity, fun z hz₁ hz₂ => ?_⟩
  let t := 1 + |z.im|
  have ht : 1 ≤ t := by dsimp [t]; linarith [abs_nonneg z.im]
  have hlog₀ : 0 ≤ 1 + Real.log (1 + 2 * |z.im|) := by
    have := Real.log_nonneg (show 1 ≤ 1 + 2 * |z.im| by linarith [abs_nonneg z.im])
    linarith
  have hlog : 1 + Real.log (1 + 2 * |z.im|) ≤ 2 * t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + 2 * |z.im| by positivity)
    dsimp [t]
    linarith
  have hB' : ‖deriv archivedGaussianFactor z‖ ≤ B * t ^ 4 := by
    refine (hd z hz₁ hz₂).trans ?_
    change B * t ^ 3 ≤ B * t ^ 4
    calc
      _ ≤ B * t ^ 3 * t := le_mul_of_one_le_right (by positivity) ht
      _ = _ := by ring
  have hA' : ‖archivedGaussianFactor z‖ ≤ A * t ^ 3 := hg z (by linarith) (by linarith)
  have hBound : ‖archivedGaussianVaughanPrimeContinuation archivedGaussianVaughanHigherMellin z‖ ≤
      ‖archivedMellin (z / 7) / 7‖ * ((3 * B + 2 * P * A) * t ^ 4) := by
    apply (he z hz₁ hz₂).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      _ ≤ 3 * (B * t ^ 4) + P * (2 * t) * (A * t ^ 3) := by gcongr
      _ = _ := by ring
  change t ^ k * _ ≤ _
  calc
    _ ≤ t ^ k * (‖archivedMellin (z / 7) / 7‖ * ((3 * B + 2 * P * A) * t ^ 4)) :=
      mul_le_mul_of_nonneg_left hBound (by positivity)
    _ = (3 * B + 2 * P * A) * (t ^ (k + 4) * ‖archivedMellin (z / 7) / 7‖) := by
      rw [pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hm z hz₁ hz₂) (by positivity)

#check archivedGaussianVaughanCompletedPrime_rapid_decay
#print axioms archivedGaussianThetaMellin_rapid_decay
#print axioms archivedGaussianVaughanCompletedPrime_rapid_decay

end
end AlpogeSuperZeta
