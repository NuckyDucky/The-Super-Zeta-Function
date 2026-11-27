import DedekindHighRightAfterCount
import MellinFixedPolynomialDisk

/-! Polynomial disk certificates for the next Dedekind count band. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture
open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

/-- Each hypothetical right-hand zero in the new band is covered at its
own input by a disk certified for the actual completed reading. -/
def HasDedekindPolynomialBandCertificate (K : Type) [Field K] [NumberField K]
    (T U : ℝ) : Prop :=
  ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 31 / 32 → T < |w.im| → |w.im| ≤ U →
    mixedThetaContinuation K w = 0 →
      ∃ (center : ℂ) (p q : ℕ), ‖w - center‖ ≤ (p : ℝ) / (q : ℝ) ∧
        Nonempty (PolynomialDiskCertificate (mixedThetaCompletedReading K) center p q)

theorem dedekind_stripCounts_equal_of_polynomial_band (K : Type) [Field K] [NumberField K]
    {T U : ℝ}
    (hcount : (mixedThetaCountingFunction K).stripZeroCount T (fun _ ↦ True) =
      (mixedThetaCountingFunction K).stripZeroCount T (fun w ↦ w.re = 1 / 2))
    (hcover : HasDedekindPolynomialBandCertificate K T U) :
    (mixedThetaCountingFunction K).stripZeroCount U (fun _ ↦ True) =
      (mixedThetaCountingFunction K).stripZeroCount U (fun w ↦ w.re = 1 / 2) := by
  apply dedekind_stripCounts_equal_of_high_right_band K hcount
  intro w hre hle ht hu hz
  obtain ⟨center, p, q, hw, ⟨cert⟩⟩ := hcover w hre hle ht hu hz
  exact cert.nonzero hw
    ((mixedThetaCompletedReading_zero_iff K w (by linarith only [hre])
      (by linarith only [hle])).mpr hz)

theorem dedekindZetaRH_of_cofinal_polynomial_bands (K : Type) [Field K] [NumberField K]
    {T : ℝ}
    (hcount : (mixedThetaCountingFunction K).stripZeroCount T (fun _ ↦ True) =
      (mixedThetaCountingFunction K).stripZeroCount T (fun w ↦ w.re = 1 / 2))
    (hcover : ∀ H : ℝ, ∃ U : ℝ, H ≤ U ∧ HasDedekindPolynomialBandCertificate K T U) :
    DedekindZetaRH K := by
  apply (dedekindZetaRH_iff_cofinal_mixedTheta_counts K).mpr
  intro H
  obtain ⟨U, hU, hcert⟩ := hcover H
  exact ⟨U, hU, dedekind_stripCounts_equal_of_polynomial_band K hcount hcert⟩

#check @dedekind_stripCounts_equal_of_polynomial_band
#check @dedekindZetaRH_of_cofinal_polynomial_bands
#print axioms dedekind_stripCounts_equal_of_polynomial_band
#print axioms dedekindZetaRH_of_cofinal_polynomial_bands

end

end FieldTarget
