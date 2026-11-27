import DedekindMixedThetaRightEdge

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set NumberField SuperZeta.StirlingCorrection
open scoped ComplexConjugate
open private gamma_factor_differentiableAt from DedekindMixedThetaSignedRings

private theorem completedReading_eq_gamma_mul (K : Type*) [Field K] [NumberField K]
    {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaCompletedReading K w = dedekindGammaFactor K w * mixedThetaContinuation K w := by
  have h0 : w ≠ 0 := by rintro rfl; norm_num at hlo
  have h1 : w ≠ 1 := by rintro rfl; norm_num at hhi
  rw [mixedThetaCompletedReading, mixedThetaSignedReading,
    mul_div_cancel_left₀ _ (mul_ne_zero h0 (sub_ne_zero.mpr h1.symm))]

/-- The entire relative factor with the ratio of the two completion factors. -/
noncomputable def completedRelativeReading (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] (g : ℂ → ℂ) (w : ℂ) : ℂ :=
  dedekindGammaFactor L w / dedekindGammaFactor K w * g w

private theorem gamma_differentiableOn_strip (F : Type*) [Field F] [NumberField F] :
    DifferentiableOn ℂ (dedekindGammaFactor F) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := fun _ hw ↦
  (gamma_factor_differentiableAt F hw.1).differentiableWithinAt

theorem completedRelativeReading_differentiableOn (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    DifferentiableOn ℂ (completedRelativeReading K L g) (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
  exact ((gamma_differentiableOn_strip L).div (gamma_differentiableOn_strip K)
    (fun w hw ↦ dedekindGammaFactor_ne_zero K hw.1)).mul hg.differentiableOn

theorem completedRelativeReading_mul (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] {g : ℂ → ℂ}
    (hprod : ∀ w : ℂ, w ≠ 1 → mixedThetaContinuation L w = g w * mixedThetaContinuation K w)
    {w : ℂ} (hlo : 0 < w.re) (hhi : w.re < 1) :
    mixedThetaCompletedReading L w = completedRelativeReading K L g w * mixedThetaCompletedReading K w := by
  have h1 : w ≠ 1 := by rintro rfl; norm_num at hhi
  rw [completedReading_eq_gamma_mul L hlo hhi, completedReading_eq_gamma_mul K hlo hhi,
    completedRelativeReading, hprod w h1]
  field_simp [dedekindGammaFactor_ne_zero K hlo]

/-- A negative bound for the cross product becomes a negative bound for the
relative reading using only an upper bound on the lower reading's norm. -/
theorem relative_im_le_of_cross_product {axis A B H : ℂ} {M margin : ℝ}
    (hprod : A = H * B) (hM : 0 < M) (hm : 0 < margin) (hB : ‖B‖ ≤ M)
    (hbound : (axis * (A * conj B)).im ≤ -margin) :
    (axis * H).im ≤ -margin / M ^ 2 := by
  have hscale : (axis * (A * conj B)).im = (axis * H).im * ‖B‖ ^ 2 := by
    rw [hprod]
    calc
      _ = ((axis * H) * (B * conj B)).im := by ring_nf
      _ = ((axis * H) * (↑(‖B‖ ^ 2) : ℂ)).im := by rw [Complex.mul_conj', Complex.ofReal_pow]
      _ = _ := by rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [hscale] at hbound
  have hneg : (axis * H).im ≤ 0 := by
    by_contra! h
    linarith only [mul_nonneg h.le (sq_nonneg ‖B‖), hbound, hm]
  have hsq : ‖B‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg B) hB 2
  exact (le_div_iff₀ (pow_pos hM 2)).mpr ((mul_le_mul_of_nonpos_left hsq hneg).trans hbound)

theorem completedRelativeReading_boundary_of_cross_product (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] {g : ℂ → ℂ}
    (hprod : ∀ w : ℂ, w ≠ 1 → mixedThetaContinuation L w = g w * mixedThetaContinuation K w)
    {T M margin : ℝ} {n : ℕ} {axis : ℂ} (hM : 0 < M) (hm : 0 < margin)
    (hbound : ∀ w ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      ‖mixedThetaCompletedReading K w‖ ≤ M ∧
      (axis * (mixedThetaCompletedReading L w * conj (mixedThetaCompletedReading K w))).im ≤ -margin) :
    ∀ w ∈ Metric.sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (axis * completedRelativeReading K L g w).im ≤ -margin / M ^ 2 := by
  intro w hw
  have hs := dottieScaledRightDisk_strip (Metric.sphere_subset_closedBall hw)
  have hp := completedRelativeReading_mul K L hprod ((by norm_num : (0 : ℝ) < 1 / 2).trans hs.1) hs.2
  obtain ⟨hMass, hSign⟩ := hbound w hw
  exact relative_im_le_of_cross_product hp hM hm hMass hSign

/-- After the lower field's critical-line result, use cofinal Dottie bands for
the completed relative reading. The field reflection and right edge use the
upper continuation at the original input. -/
theorem dedekindZetaRH_of_relative_dottie_bands (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hprod : ∀ w : ℂ, w ≠ 1 → mixedThetaContinuation L w = g w * mixedThetaContinuation K w)
    (hK : DedekindZetaRH K)
    (hbands : ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
      HasFiniteDottieBoundaryCertificate g (completedRelativeReading K L g) 0 (M : ℝ)) :
    DedekindZetaRH L := by
  have hforce (w : ℂ) (hre : 1/2 < w.re) (hhi : w.re < 1)
      (hz : mixedThetaContinuation L w = 0) : g w = 0 := by
    have hw1 : w ≠ 1 := by rintro rfl; norm_num at hhi
    have hp := (mul_eq_zero.mp ((hprod w hw1).symm.trans hz))
    exact hp.resolve_right fun hbase ↦ hre.ne'
      (hK (mixedThetaContinuation K) (mixedThetaContinuation_isDedekind K) w (by linarith) hhi hbase)
  have hnonneg (w : ℂ) (hre : 1/2 < w.re) (hhi : w.re < 1) (him : 0 ≤ w.im) :
      mixedThetaContinuation L w ≠ 0 := by
    by_cases hbound : w.re ≤ 31/32
    · obtain ⟨N, hN⟩ := exists_nat_gt w.im
      obtain ⟨M, hM, hcert⟩ := hbands N
      have hnM : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hg0 := dottie_band_nonzero_of_certificate (completedRelativeReading_differentiableOn K L hg)
        (fun z _ _ hz ↦ by simp [completedRelativeReading, hz]) hcert ⟨him, hN.le.trans hnM⟩ hre hbound
      exact fun hz ↦ hg0 (hforce w hre hhi hz)
    · have hw1 : w ≠ 1 := by rintro rfl; norm_num at hhi
      exact mixedThetaContinuation_ne_zero_above_31_32 L (lt_of_not_ge hbound) hw1
  have hright (w : ℂ) (hre : 1/2 < w.re) (hhi : w.re < 1) :
      mixedThetaContinuation L w ≠ 0 := by
    by_cases him : 0 ≤ w.im
    · exact hnonneg w hre hhi him
    · have hw1 : w ≠ 1 := by rintro rfl; norm_num at hhi
      intro hz
      have hconj : mixedThetaContinuation L (conj w) = 0 := by
        rw [continuation_conj_argument (mixedThetaContinuation_isDedekind L) hw1, hz, map_zero]
      apply hnonneg (conj w) (by simpa only [conj_re] using hre)
        (by simpa only [conj_re] using hhi) _ hconj
      simpa only [conj_im, neg_nonneg] using (le_of_not_ge him)
  apply (dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind L)).mpr
  intro w hlo hhi hz
  rcases lt_trichotomy w.re (1/2 : ℝ) with hleft | heq | hre
  · exfalso
    apply hright (1-conj w) _ _ (mixedThetaContinuation_reflects L w hlo hhi hz)
    · simp only [sub_re, one_re, conj_re]
      linarith
    · simp only [sub_re, one_re, conj_re]
      linarith
  · exact heq
  · exact (hright w hre hhi hz).elim

#check @completedRelativeReading_boundary_of_cross_product
#check @dedekindZetaRH_of_relative_dottie_bands
#print axioms completedRelativeReading_differentiableOn
#print axioms completedRelativeReading_mul
#print axioms relative_im_le_of_cross_product
#print axioms completedRelativeReading_boundary_of_cross_product
#print axioms dedekindZetaRH_of_relative_dottie_bands

end FieldTarget
