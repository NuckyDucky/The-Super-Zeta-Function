import DedekindMixedThetaCompletedRings
import DedekindCuretonThorner

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex Set
open scoped ComplexConjugate

theorem mixedThetaContinuation_ne_zero_above_31_32
    (K : Type*) [Field K] [NumberField K] {w : ℂ}
    (hw : 31/32 < w.re) (hw1 : w ≠ 1) : mixedThetaContinuation K w ≠ 0 := by
  rw [continuation_eq_off_one (mixedThetaContinuation_isDedekind K)
    (dedekindContinuation_isDedekindZeta K) hw1]
  exact (Classical.choose_spec (exists_dedekind_continuation_with_zero_control K)).2.2 w hw hw1

private theorem dedekindZetaRH_of_mixedTheta_height_cover_of_reading
    (K : Type*) [Field K] [NumberField K] {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hzero : ∀ w : ℂ, 0 < w.re → w.re < 1 → mixedThetaContinuation K w = 0 → F w = 0)
    (hbands : ∀ t : ℝ, 0 ≤ t → ∃ l u : ℝ, t ∈ Icc l u ∧
      HasFiniteDottieBoundaryCertificate (mixedThetaContinuation K) F l u) :
    DedekindZetaRH K := by
  have hnonneg (w : ℂ) (hre : 1/2 < w.re) (hhi : w.re < 1) (him : 0 ≤ w.im) :
      mixedThetaContinuation K w ≠ 0 := by
    by_cases hbound : w.re ≤ 31/32
    · obtain ⟨l, u, hheight, hcert⟩ := hbands w.im him
      exact dottie_band_nonzero_of_certificate hF hzero hcert hheight hre hbound
    · have hw1 : w ≠ 1 := by rintro rfl; norm_num at hhi
      exact mixedThetaContinuation_ne_zero_above_31_32 K (lt_of_not_ge hbound) hw1
  have hright (w : ℂ) (hre : 1/2 < w.re) (hhi : w.re < 1) :
      mixedThetaContinuation K w ≠ 0 := by
    by_cases him : 0 ≤ w.im
    · exact hnonneg w hre hhi him
    · have hw1 : w ≠ 1 := by rintro rfl; norm_num at hhi
      intro hz
      have hconj : mixedThetaContinuation K (conj w) = 0 := by
        rw [continuation_conj_argument (mixedThetaContinuation_isDedekind K) hw1, hz, map_zero]
      apply hnonneg (conj w) (by simpa only [conj_re] using hre)
        (by simpa only [conj_re] using hhi) _ hconj
      simpa only [conj_im, neg_nonneg] using (le_of_not_ge him)
  apply (dedekindZetaRH_iff_strip (mixedThetaContinuation_isDedekind K)).mpr
  intro w hlo hhi hz
  rcases lt_trichotomy w.re (1/2 : ℝ) with hleft | heq | hr
  · exfalso
    apply hright (1-conj w) _ _ (mixedThetaContinuation_reflects K w hlo hhi hz)
    · simp only [sub_re, one_re, conj_re]
      linarith
    · simp only [sub_re, one_re, conj_re]
      linarith
  · exact heq
  · exact (hright w hr hhi hz).elim

/-- Signed bands need only cover nonnegative heights. Conjugation reduces
negative heights to those bands, and the functional equation reflects the strip. -/
theorem dedekindZetaRH_of_mixedTheta_signed_height_cover
    (K : Type*) [Field K] [NumberField K]
    (hbands : ∀ t : ℝ, 0 ≤ t → ∃ l u : ℝ, t ∈ Icc l u ∧
      HasFiniteDottieBoundaryCertificate
        (mixedThetaContinuation K) (mixedThetaSignedReading K) l u) :
    DedekindZetaRH K :=
  dedekindZetaRH_of_mixedTheta_height_cover_of_reading K
    (mixedThetaSignedReading_differentiableOn K)
    (fun w hlo hhi => (mixedThetaSignedReading_zero_iff K w hlo hhi).mpr) hbands

/-- The same implication takes the completed reading used by the finite
quadrature samples and the field factorization criterion. -/
theorem dedekindZetaRH_of_completed_mixedTheta_signed_height_cover
    (K : Type*) [Field K] [NumberField K]
    (hbands : ∀ t : ℝ, 0 ≤ t → ∃ l u : ℝ, t ∈ Icc l u ∧
      HasFiniteDottieBoundaryCertificate
        (mixedThetaContinuation K) (mixedThetaCompletedReading K) l u) :
    DedekindZetaRH K :=
  dedekindZetaRH_of_mixedTheta_height_cover_of_reading K
    (mixedThetaCompletedReading_differentiableOn K)
    (fun w hlo hhi => (mixedThetaCompletedReading_zero_iff K w hlo hhi).mpr) hbands

theorem dedekindZetaRH_of_cofinal_mixedTheta_signed_rings
    (K : Type*) [Field K] [NumberField K]
    (hbands : ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ HasFiniteDottieBoundaryCertificate
      (mixedThetaContinuation K) (mixedThetaSignedReading K) (-(M : ℝ)) (M : ℝ)) :
    DedekindZetaRH K := by
  apply dedekindZetaRH_of_mixedTheta_signed_height_cover K
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_gt t
  obtain ⟨M, hNM, hcert⟩ := hbands N
  have hheight : t ≤ (M : ℝ) := hN.le.trans (by exact_mod_cast hNM)
  exact ⟨-(M : ℝ), M, ⟨(neg_nonpos.mpr (ht.trans hheight)).trans ht, hheight⟩, hcert⟩

theorem dedekindZetaRH_of_cofinal_mixedTheta_nonneg_rings
    (K : Type*) [Field K] [NumberField K]
    (hbands : ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ HasFiniteDottieBoundaryCertificate
      (mixedThetaContinuation K) (mixedThetaSignedReading K) 0 (M : ℝ)) :
    DedekindZetaRH K := by
  apply dedekindZetaRH_of_mixedTheta_signed_height_cover K
  intro t ht
  obtain ⟨N, hN⟩ := exists_nat_gt t
  obtain ⟨M, hNM, hcert⟩ := hbands N
  exact ⟨0, M, ⟨ht, hN.le.trans (by exact_mod_cast hNM)⟩, hcert⟩

#check @dedekindZetaRH_of_mixedTheta_signed_height_cover
#check @dedekindZetaRH_of_completed_mixedTheta_signed_height_cover
#check @dedekindZetaRH_of_cofinal_mixedTheta_signed_rings
#check @dedekindZetaRH_of_cofinal_mixedTheta_nonneg_rings
#print axioms mixedThetaContinuation_ne_zero_above_31_32
#print axioms dedekindZetaRH_of_mixedTheta_signed_height_cover
#print axioms dedekindZetaRH_of_completed_mixedTheta_signed_height_cover
#print axioms dedekindZetaRH_of_cofinal_mixedTheta_signed_rings
#print axioms dedekindZetaRH_of_cofinal_mixedTheta_nonneg_rings

end FieldTarget
