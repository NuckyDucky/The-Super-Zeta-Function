import FieldTarget

/-! Connect the existing field target to signed estimates at a family of
measuring regions. The Dottie region proof supplies `hlocate`. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex
open scoped ComplexConjugate

/-- This is the existing Dedekind-zeta strip target with a family of
measuring regions at marked returns. `hzero` is the field identity, `hlocate`
is dynamical coverage and `hmodel`/`htail` are the two signed estimates. -/
theorem dedekindZetaRH_of_same_input_signed_regions
    {K : Type*} [Field K] [NumberField K] {Orbit : Type*}
    {Z U V : ℂ → ℂ} (hZ : IsDedekindZeta K Z)
    (region : Orbit → Set ℂ) (axis : Orbit → ℂ)
    (retained : Orbit → ℂ → ℂ) (margin : Orbit → ℂ → ℝ)
    (hzero : ∀ w : ℂ, 0 < w.re → w.re < 1 → Z w = 0 → U w = V w)
    (hreflect : ∀ w : ℂ, 0 < w.re → w.re < 1 → Z w = 0 → Z (1-conj w) = 0)
    (hlocate : ∀ w : ℂ, 1/2 < w.re → w.re < 1 → Z w = 0 →
      ∃ a : Orbit, w ∈ region a)
    (hmargin : ∀ a w, w ∈ region a → 0 < margin a w)
    (hmodel : ∀ a w, w ∈ region a → (retained a w).im ≤ -(2*margin a w))
    (htail : ∀ a w, w ∈ region a → (axis a*(U w-V w)-retained a w).im ≤ margin a w) :
    DedekindZetaRH K := by
  apply (dedekindZetaRH_iff_strip hZ).2
  have excludeRight (w : ℂ) (hr : 1/2 < w.re) (h₁ : w.re < 1) (hz : Z w = 0) : False := by
    obtain ⟨a, ha⟩ := hlocate w hr h₁ hz
    have he := hzero w (by linarith) h₁ hz
    have ht := htail a w ha
    have hm := hmodel a w ha
    have hp := hmargin a w ha
    rw [he, sub_self] at ht
    simp only [mul_zero, zero_sub, neg_im] at ht
    linarith
  intro w hw₀ hw₁ hz
  rcases lt_trichotomy w.re (1/2) with hleft | hline | hright
  · exfalso
    have he : (1-conj w).re = 1-w.re := by simp
    exact excludeRight (1-conj w) (by rw [he]; linarith)
      (by rw [he]; linarith) (hreflect w hw₀ hw₁ hz)
  · exact hline
  · exact False.elim (excludeRight w hright hw₁ hz)

#check @dedekindZetaRH_of_same_input_signed_regions
#print axioms dedekindZetaRH_of_same_input_signed_regions

end FieldTarget
