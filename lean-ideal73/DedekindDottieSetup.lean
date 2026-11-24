import FieldTarget

/-! Connect the existing field target to signed estimates at a family of
measuring regions. The Dottie region proof supplies `hlocate`. -/

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex
open scoped ComplexConjugate

/-- The retained bound and the tail allowance can be arbitrarily close.
The contradiction uses their strict gap at the original input. -/
theorem readings_ne_of_signed_gap {U V axis retained : ℂ} {main tail : ℝ}
    (hgap : tail < main) (hmodel : retained.im ≤ -main)
    (htail : (axis*(U-V)-retained).im ≤ tail) : U ≠ V := by
  intro he
  rw [he, sub_self] at htail
  simp only [mul_zero, zero_sub, neg_im] at htail
  linarith

/-- Transport the same-input contradiction through the reflecting strip.
The paired bounds may depend on the field, region, and recovered point. -/
theorem dedekindZetaRH_of_same_input_signed_gap
    {K : Type*} [Field K] [NumberField K] {Orbit : Type*}
    {Z U V : ℂ → ℂ} (hZ : IsDedekindZeta K Z)
    (region : Orbit → Set ℂ) (axis : Orbit → ℂ)
    (retained : Orbit → ℂ → ℂ) (main tail : Orbit → ℂ → ℝ)
    (hzero : ∀ w : ℂ, 0 < w.re → w.re < 1 → Z w = 0 → U w = V w)
    (hreflect : ∀ w : ℂ, 0 < w.re → w.re < 1 → Z w = 0 → Z (1-conj w) = 0)
    (hlocate : ∀ w : ℂ, 1/2 < w.re → w.re < 1 → Z w = 0 →
      ∃ a : Orbit, w ∈ region a)
    (hgap : ∀ a w, w ∈ region a → tail a w < main a w)
    (hmodel : ∀ a w, w ∈ region a → (retained a w).im ≤ -(main a w))
    (htail : ∀ a w, w ∈ region a → (axis a*(U w-V w)-retained a w).im ≤ tail a w) :
    DedekindZetaRH K := by
  apply (dedekindZetaRH_iff_strip hZ).2
  have excludeRight (w : ℂ) (hr : 1/2 < w.re) (h₁ : w.re < 1) (hz : Z w = 0) : False := by
    obtain ⟨a, ha⟩ := hlocate w hr h₁ hz
    exact readings_ne_of_signed_gap (hgap a w ha) (hmodel a w ha) (htail a w ha)
      (hzero w (by linarith) h₁ hz)
  intro w hw₀ hw₁ hz
  rcases lt_trichotomy w.re (1/2) with hleft | hline | hright
  · exfalso
    have he : (1-conj w).re = 1-w.re := by simp
    exact excludeRight (1-conj w) (by rw [he]; linarith)
      (by rw [he]; linarith) (hreflect w hw₀ hw₁ hz)
  · exact hline
  · exact False.elim (excludeRight w hright hw₁ hz)

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
  apply dedekindZetaRH_of_same_input_signed_gap hZ region axis retained
    (fun a w => 2 * margin a w) margin hzero hreflect hlocate _ hmodel htail
  intro a w hw
  linarith [hmargin a w hw]

#check @dedekindZetaRH_of_same_input_signed_regions
#print axioms readings_ne_of_signed_gap
#print axioms dedekindZetaRH_of_same_input_signed_gap
#print axioms dedekindZetaRH_of_same_input_signed_regions

end FieldTarget
