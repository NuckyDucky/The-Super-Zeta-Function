import DedekindMixedTheta
import DedekindZetaZeroFree.Main

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex
open scoped ComplexConjugate

/-- One continuation satisfies the exact field identification, the horizontal
reflection of its zeros, and the published zero-free bound. -/
theorem exists_dedekind_continuation_with_zero_control
    (K : Type*) [Field K] [NumberField K] :
    ∃ Z : ℂ → ℂ, IsDedekindZeta K Z ∧
      (∀ w : ℂ, 0 < w.re → w.re < 1 → Z w = 0 → Z (1 - conj w) = 0) ∧
      (∀ w : ℂ, 31 / 32 < w.re → w ≠ 1 → Z w ≠ 0) := by
  apply exists_dedekind_continuation_of_small_fields
  intro F _ _
  obtain ⟨Z, hZ, hFE⟩ := exists_dedekind_continuation_with_functionalEquation F
  obtain ⟨W, hWdiff, hWseries, hWfree⟩ := DedekindZetaZeroFree.dedekindZeta_ne_zero F
  exact ⟨Z, hZ, continuation_reflects_zeros_of_functionalEquation hZ hFE,
    fun _ hw hw1 => continuation_ne_zero_above hZ ⟨hWdiff, hWseries⟩ hWfree hw hw1⟩

noncomputable def dedekindContinuation (K : Type*) [Field K] [NumberField K] : ℂ → ℂ :=
  Classical.choose (exists_dedekind_continuation_with_zero_control K)

theorem dedekindContinuation_isDedekindZeta (K : Type*) [Field K] [NumberField K] :
    IsDedekindZeta K (dedekindContinuation K) :=
  (Classical.choose_spec (exists_dedekind_continuation_with_zero_control K)).1

/-- The field-dependent inputs are now the same-point equality, location in
the remaining half-strip, and the signed estimates. -/
theorem dedekindZetaRH_of_signed_gap_with31_32
    {K : Type*} [Field K] [NumberField K] {Orbit : Type*} {U V : ℂ → ℂ}
    (region : Orbit → Set ℂ) (axis : Orbit → ℂ)
    (retained : Orbit → ℂ → ℂ) (main tail : Orbit → ℂ → ℝ)
    (hzero : ∀ w : ℂ, 0 < w.re → w.re < 1 →
      dedekindContinuation K w = 0 → U w = V w)
    (hlocate : ∀ w : ℂ, 1 / 2 < w.re → w.re ≤ 31 / 32 →
      dedekindContinuation K w = 0 → ∃ a : Orbit, w ∈ region a)
    (hgap : ∀ a w, w ∈ region a → tail a w < main a w)
    (hmodel : ∀ a w, w ∈ region a → (retained a w).im ≤ -main a w)
    (htail : ∀ a w, w ∈ region a → (axis a * (U w - V w) - retained a w).im ≤ tail a w) :
    DedekindZetaRH K := by
  have h := Classical.choose_spec (exists_dedekind_continuation_with_zero_control K)
  exact dedekindZetaRH_of_same_input_signed_gap_below h.1
    ⟨dedekindContinuation K, h.1, h.2.2⟩ region axis retained main tail
    hzero h.2.1 (fun w hr _ hb hz => hlocate w hr hb hz) hgap hmodel htail

#check @dedekindZetaRH_of_signed_gap_with31_32
#print axioms exists_dedekind_continuation_with_zero_control
#print axioms dedekindContinuation_isDedekindZeta
#print axioms dedekindZetaRH_of_signed_gap_with31_32

end FieldTarget
