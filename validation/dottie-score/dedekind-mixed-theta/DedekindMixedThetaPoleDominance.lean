import DedekindMixedThetaSampleCompleteness

namespace FieldTarget

open Complex MeasureTheory Set SuperZeta.StirlingCorrection
open DedekindZetaZeroFree.AbelianQuotient
open scoped ComplexConjugate

/-- Both reciprocal poles have a positive real part on the open strip. -/
theorem dottie_reciprocal_pole_re_lower {w : ℂ} {H : ℝ}
    (hH : 0 ≤ H) (hlo : 0 < w.re) (hhi : w.re < 1) (ht : |w.im| ≤ H) :
    1 / (1 + H^2) ≤ ((w * (1-w))⁻¹).re := by
  have hterm (z : ℂ) (hz₀ : 0 < z.re) (hz₁ : z.re ≤ 1) (hz : |z.im| ≤ H) :
      z.re / (1 + H^2) ≤ (z⁻¹).re := by
    have hsq : z.re * z.re ≤ 1 := calc
      _ ≤ z.re * 1 := mul_le_mul_of_nonneg_left hz₁ hz₀.le
      _ ≤ 1 := by simpa only [mul_one] using hz₁
    have ht2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg hH] using hz : |z.im| ≤ |H|)
    rw [Complex.inv_re, Complex.normSq_apply]
    exact div_le_div_of_nonneg_left hz₀.le
      (add_pos_of_pos_of_nonneg (mul_pos hz₀ hz₀) (mul_self_nonneg z.im))
      (add_le_add hsq (by simpa only [pow_two] using ht2))
  have hw₀ : w ≠ 0 := by rintro rfl; norm_num at hlo
  have hw₁ : 1 - w ≠ 0 := by
    intro he
    have hw : w = 1 := (sub_eq_zero.mp he).symm
    rw [hw, Complex.one_re] at hhi
    exact (lt_irrefl 1) hhi
  have heq : (w*(1-w))⁻¹ = w⁻¹ + (1-w)⁻¹ := by
    field_simp [hw₀, hw₁]
    ring
  have hsub₀ : 0 < (1-w).re := by simpa only [sub_re, one_re] using sub_pos.mpr hhi
  have hsub₁ : (1-w).re ≤ 1 := by rw [sub_re, one_re]; linarith
  have hsubt : |(1-w).im| ≤ H := by simpa only [sub_im, one_im, zero_sub, abs_neg] using ht
  rw [heq, add_re]
  calc
    1 / (1 + H^2) = w.re / (1 + H^2) + (1-w).re / (1 + H^2) := by
      rw [← add_div, sub_re, one_re]
      ring
    _ ≤ _ := add_le_add (hterm w hlo hhi.le ht) (hterm (1-w) hsub₀ hsub₁ hsubt)

/-- One absolute theta-mass inequality gives a strict sign over a whole height band. -/
theorem mixedThetaCompletedReading_signed_of_mass (K : Type) [Field K] [NumberField K]
    {H : ℝ} (hH : 0 ≤ H)
    (hmass : 2 * ∫ t : ℝ in Ioi 1, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖
      < ‖(Theta.mixedThetaPair K).f₀‖ / (1 + H^2)) :
    ∃ axis : ℂ, ∃ margin : ℝ, 0 < margin ∧
      ∀ w : ℂ, 0 < w.re → w.re < 1 → |w.im| ≤ H →
        (axis * mixedThetaCompletedReading K w).im ≤ -margin := by
  let P := Theta.mixedThetaPair K
  let C := P.f₀
  let M := 2 * ∫ t : ℝ in Ioi 1, ‖P.f t - C‖
  let margin := ‖C‖ * (‖C‖ / (1+H^2) - M)
  change M < ‖C‖/(1+H^2) at hmass
  have hM : 0 ≤ M := mul_nonneg (by norm_num) (integral_nonneg fun _ => norm_nonneg _)
  have hC : 0 < ‖C‖ := by
    by_contra! h
    have he := le_antisymm h (norm_nonneg C)
    rw [he, zero_div] at hmass
    exact (not_lt_of_ge hM) hmass
  refine ⟨I * conj C, margin, mul_pos hC (sub_pos.mpr hmass), ?_⟩
  intro w hlo hhi ht
  have hsize : ‖P.Λ₀ w‖ ≤ M := by
    have h := mixedTheta_mellin_tail_le K 1 le_rfl w hlo.le hhi.le
    simpa only [mixedThetaTruncation, intervalIntegral.integral_same, sub_zero] using h
  have hreg : (conj C * P.Λ₀ w).re ≤ ‖C‖ * M := by
    calc
      _ ≤ ‖conj C * P.Λ₀ w‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ ≤ _ := by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left hsize hC.le
  have hpole : (conj C * (C / (w*(1-w)))).re = ‖C‖^2 * ((w*(1-w))⁻¹).re := by
    rw [div_eq_mul_inv, ← mul_assoc, Complex.conj_mul']
    simp [← Complex.ofReal_pow, Complex.mul_re]
  have hpole_lower := mul_le_mul_of_nonneg_left
    (dottie_reciprocal_pole_re_lower hH hlo hhi ht) (sq_nonneg ‖C‖)
  rw [mul_assoc, Complex.I_mul_im, mixedThetaCompletedReading_eq_mellin K w hlo hhi]
  change (conj C * (P.Λ₀ w - C / (w*(1-w)))).re ≤ -margin
  rw [mul_sub, sub_re, hpole]
  calc
    _ ≤ ‖C‖ * M - ‖C‖^2 * (1 / (1+H^2)) := sub_le_sub hreg hpole_lower
    _ = -margin := by dsimp only [margin]; ring

/-- The same mass test supplies finite samples on every measuring disk within the band. -/
theorem dottie_completed_samples_of_mass (K : Type) [Field K] [NumberField K]
    {H T : ℝ} {n : ℕ} (hH : 0 ≤ H) (hT : |T - 1/512| + dottieScaledRadius n ≤ H)
    (hmass : 2 * ∫ t : ℝ in Ioi 1, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖
      < ‖(Theta.mixedThetaPair K).f₀‖ / (1 + H^2)) :
    HasDottieCompletedSamples K T n := by
  apply (dottie_completed_samples_iff_boundary_sign K T n).mpr
  obtain ⟨axis, margin, hmargin, hsign⟩ := mixedThetaCompletedReading_signed_of_mass K hH hmass
  refine ⟨axis, margin, hmargin, ?_⟩
  intro w hw
  let c := dottieScaledRightCenter T n
  have hd : ‖w-c‖ = dottieScaledRadius n := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
  have hi : w.im = (w-c).im + (T - 1/512) := by
    rw [sub_im, show c.im = T - 1/512 from rfl]
    ring
  have hIm : |w.im| ≤ H := by
    rw [hi]
    calc
      _ ≤ |(w-c).im| + |T - 1/512| := abs_add_le _ _
      _ ≤ dottieScaledRadius n + |T - 1/512| :=
        add_le_add (hd ▸ Complex.abs_im_le_norm (w-c)) le_rfl
      _ ≤ H := by simpa only [add_comm (dottieScaledRadius n) |T - 1/512|] using hT
  have hs := dottieScaledRightDisk_strip (Metric.sphere_subset_closedBall hw)
  exact hsign w ((by norm_num : (0 : ℝ) < 1/2).trans hs.1) hs.2 hIm

/-- The same scalar estimate supplies the entire symmetric band certificate.
The extra height allowance is the largest Dottie disk radius. -/
theorem finite_dottie_boundary_of_mellin_mass (K : Type) [Field K] [NumberField K]
    {L : ℝ} (hL : 0 ≤ L)
    (hmass : 2 * ∫ t : ℝ in Ioi 1, ‖(Theta.mixedThetaPair K).f t - (Theta.mixedThetaPair K).f₀‖
      < ‖(Theta.mixedThetaPair K).f₀‖ / (1 + (L + 31/128)^2)) :
    HasFiniteDottieBoundaryCertificate (mixedThetaContinuation K) (mixedThetaCompletedReading K)
      (-L) L := by
  apply (finite_dottie_boundary_iff_completed_sample_cover K (-L) L).mpr
  obtain ⟨ε, hε, disks, hclear, hcover⟩ :=
    exists_finite_dedekind_band_cover (mixedThetaContinuation_isDedekind K) (-L) L
  refine ⟨ε, hε, disks, hclear, hcover, fun a _ => ?_⟩
  have hcenter : |a.val.1 - 1/512| ≤ L := abs_le.mpr a.property
  have hpow : (1/2 : ℝ)^a.val.2 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr : dottieScaledRadius a.val.2 ≤ 31 / 128 := by
    calc
      _ = (31/128) * (1/2 : ℝ)^a.val.2 := by
        unfold dottieScaledRadius dottieRingScale
        ring
      _ ≤ _ := mul_le_of_le_one_right (by norm_num) hpow
  exact dottie_completed_samples_of_mass K (by linarith) (add_le_add hcenter hr) hmass

#check @dottie_completed_samples_of_mass
#check @finite_dottie_boundary_of_mellin_mass
#print axioms dottie_reciprocal_pole_re_lower
#print axioms mixedThetaCompletedReading_signed_of_mass
#print axioms dottie_completed_samples_of_mass
#print axioms finite_dottie_boundary_of_mellin_mass

end FieldTarget
