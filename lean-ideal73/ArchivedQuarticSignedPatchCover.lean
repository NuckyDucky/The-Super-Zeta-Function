import ArchivedQuarticCertificates

/-! A finite cover of each right box by signed projections of the exact
completed Gaussian factor. -/

open Complex
open scoped ComplexConjugate

namespace StripCover

/-- An input disk with a positive lower bound for its signed projection. -/
structure SignedPatch where
  center : ℂ
  radius : ℝ
  margin : ℝ
  margin_pos : 0 < margin

/-- Points where this patch must certify a bound in box `n`. -/
def SignedPatch.points (patch : SignedPatch) (n : ℕ) : Set ℂ :=
  rightBox n ∩ Metric.closedBall patch.center patch.radius

/-- Each patch has one unit direction, shared by all its points in the box.
The projection along that direction is bounded below by the patch margin. -/
def HasSignedPatchBounds (F : ℂ → ℂ) : Prop :=
  ∀ n : ℕ, ∃ (k : ℕ) (patches : Fin k → SignedPatch),
    (∀ w ∈ rightBox n, ∃ i, w ∈ (patches i).points n) ∧
    ∀ i, ∃ d : ℂ, ‖d‖ = 1 ∧
      ∀ w ∈ (patches i).points n, (patches i).margin ≤ (conj d * F w).re

/-- A unit projection is bounded by the norm. The smallest patch margin
therefore gives a positive norm bound for the whole box. -/
theorem boxMargins_of_signedPatchBounds {F : ℂ → ℂ}
    (certificate : HasSignedPatchBounds F) : BoxMargins F := by
  intro n
  obtain ⟨k, patches, cover, bounds⟩ := certificate n
  by_cases hne : (Finset.univ : Finset (Fin k)).Nonempty
  · obtain ⟨j, _, hj⟩ :=
      Finset.exists_min_image Finset.univ (fun i => (patches i).margin) hne
    refine ⟨(patches j).margin, (patches j).margin_pos, ?_⟩
    intro w hw
    obtain ⟨i, hi⟩ := cover w hw
    obtain ⟨d, hd, hbound⟩ := bounds i
    calc
      (patches j).margin ≤ (patches i).margin := hj i (Finset.mem_univ i)
      _ ≤ (conj d * F w).re := hbound w hi
      _ ≤ ‖conj d * F w‖ := Complex.re_le_norm _
      _ = ‖F w‖ := by rw [norm_mul, Complex.norm_conj, hd, one_mul]
  · refine ⟨1, zero_lt_one, ?_⟩
    intro w hw
    obtain ⟨i, _⟩ := cover w hw
    exact (hne ⟨i, Finset.mem_univ i⟩).elim

/-- A uniform signed bound on either coordinate of each patch suffices.
The coordinate and its sign can vary between patches. -/
theorem hasSignedPatchBounds_of_axisBounds {F : ℂ → ℂ}
    (certificate : ∀ n : ℕ, ∃ (k : ℕ) (patches : Fin k → SignedPatch),
      (∀ w ∈ rightBox n, ∃ i, w ∈ (patches i).points n) ∧
      ∀ i, let patch := patches i
        (∀ w ∈ patch.points n, patch.margin ≤ (F w).re) ∨
        (∀ w ∈ patch.points n, (F w).re ≤ -patch.margin) ∨
        (∀ w ∈ patch.points n, patch.margin ≤ (F w).im) ∨
        (∀ w ∈ patch.points n, (F w).im ≤ -patch.margin)) :
    HasSignedPatchBounds F := by
  intro n
  obtain ⟨k, patches, cover, bounds⟩ := certificate n
  refine ⟨k, patches, cover, fun i => ?_⟩
  rcases bounds i with h | h | h | h
  · exact ⟨1, norm_one, by simpa using h⟩
  · refine ⟨-1, by simp, fun w hw => ?_⟩
    have haxis := h w hw
    simp
    linarith
  · exact ⟨I, norm_I, by simpa [mul_re] using h⟩
  · refine ⟨-I, by simp, fun w hw => ?_⟩
    have haxis := h w hw
    simp [mul_re]
    linarith

#print axioms boxMargins_of_signedPatchBounds
#print axioms hasSignedPatchBounds_of_axisBounds

end StripCover

namespace QuarticModel

open ArtinPrimitiveRootsConjecture FieldCoefficientTransfer

/-- Signed patch covers of the exact completion localize every Gaussian strip zero. -/
theorem archivedGaussian_strip_of_signedPatchBounds
    (certificate : StripCover.HasSignedPatchBounds archivedMellin) :
    FieldTarget.StripZerosOnLine archivedGaussianFactor :=
  archivedGaussian_strip_iff_boxMargins.mpr (StripCover.boxMargins_of_signedPatchBounds certificate)

/-- With the rational zeta and beta inputs, signed patch covers of the exact
Gaussian completion imply the fixed quartic field's Dedekind zeta RH. -/
theorem archivedQuarticRH_of_signedPatchBounds
    (hzeta : FieldTarget.StripZerosOnLine riemannZeta)
    (hbeta : FieldTarget.StripZerosOnLine chi4.LFunction)
    (certificate : StripCover.HasSignedPatchBounds archivedMellin) :
    DedekindZetaRH K :=
  archivedQuarticRH_iff_boxMargins.mpr
    ⟨hzeta, hbeta, StripCover.boxMargins_of_signedPatchBounds certificate⟩

#print axioms archivedGaussian_strip_of_signedPatchBounds
#print axioms archivedQuarticRH_of_signedPatchBounds

end QuarticModel
