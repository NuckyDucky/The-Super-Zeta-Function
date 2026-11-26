import DedekindDottieSetup
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

namespace FieldTarget

open ArtinPrimitiveRootsConjecture Complex
open scoped ComplexConjugate

variable {K : Type*} [Field K] [NumberField K]

/-- The ideal-counting coefficients are real. -/
theorem dedekindZeta_conj_argument (K : Type*) [Field K] [NumberField K] (w : ℂ) :
    NumberField.dedekindZeta K (conj w) = conj (NumberField.dedekindZeta K w) := by
  simp only [NumberField.dedekindZeta, LSeries, RCLike.conj_tsum]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  simp only [LSeries.term_of_ne_zero hn, map_div₀, map_natCast]
  have hArg : (n : ℂ).arg ≠ Real.pi := by
    rw [Complex.natCast_arg]
    exact Real.pi_ne_zero.symm
  rw [Complex.cpow_conj _ _ hArg, map_natCast]

/-- The identity theorem gives conjugation for every continuation of the series. -/
theorem continuation_conj_argument {Z : ℂ → ℂ}
    (hZ : IsDedekindZeta K Z) {w : ℂ} (hw : w ≠ 1) :
    Z (conj w) = conj (Z w) := by
  let W := fun z : ℂ => conj (Z (conj z))
  have hW : IsDedekindZeta K W := by
    refine ⟨?_, ?_⟩
    · intro z hz
      have hcz : conj z ≠ 1 := by
        intro h
        apply hz
        exact Set.mem_singleton_iff.mpr
          (by simpa only [conj_conj, map_one] using congrArg (conj : ℂ → ℂ) h)
      have hd : DifferentiableAt ℂ Z (conj z) :=
        hZ.1.differentiableAt (isOpen_compl_singleton.mem_nhds hcz)
      have hWr : DifferentiableAt ℂ (conj ∘ Z ∘ conj) z :=
        differentiableAt_conj_conj_iff.mpr hd
      exact hWr.differentiableWithinAt
    · intro z hz
      have hcz : 1 < (conj z).re := by simpa using hz
      change conj (Z (conj z)) = _
      rw [hZ.2 _ hcz, dedekindZeta_conj_argument, conj_conj]
  have ht := continuation_eq_off_one hW hZ hw
  simpa [W, conj_conj] using congrArg (conj : ℂ → ℂ) ht

/-- A completed functional equation induces the reflecting zero map used by
the signed-gap proof as soon as its multiplier is nonzero in the strip. -/
theorem continuation_reflects_zeros_of_completion {Z A Λ : ℂ → ℂ}
    (hZ : IsDedekindZeta K Z)
    (hcomplete : ∀ w : ℂ, 0 < w.re → w.re < 1 → Λ w = A w * Z w)
    (hscale : ∀ w : ℂ, 0 < w.re → w.re < 1 → A w ≠ 0)
    (hfe : ∀ w : ℂ, 0 < w.re → w.re < 1 → Λ (1 - w) = Λ w)
    (w : ℂ) (hw₀ : 0 < w.re) (hw₁ : w.re < 1) (hz : Z w = 0) :
    Z (1 - conj w) = 0 := by
  have hw : w ≠ 1 := by rintro rfl; norm_num at hw₁
  have hc₀ : 0 < (conj w).re := by simpa using hw₀
  have hc₁ : (conj w).re < 1 := by simpa using hw₁
  have hc : Z (conj w) = 0 := by rw [continuation_conj_argument hZ hw, hz, map_zero]
  have hR : (1 - conj w).re = 1 - w.re := by simp
  have hr₀ : 0 < (1 - conj w).re := by rw [hR]; linarith
  have hr₁ : (1 - conj w).re < 1 := by rw [hR]; linarith
  have he := hfe (conj w) hc₀ hc₁
  rw [hcomplete _ hr₀ hr₁, hcomplete _ hc₀ hc₁, hc, mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (hscale _ hr₀ hr₁)

/-- The normalization in the mixed-theta continuation, including both kinds
of infinite place. -/
noncomputable def dedekindGammaFactor (K : Type*) [Field K] [NumberField K] (w : ℂ) : ℂ :=
  (((|NumberField.discr K| : ℤ) : ℂ) ^ (w / 2)) *
    Complex.Gammaℝ w ^ NumberField.InfinitePlace.nrRealPlaces K *
    Complex.Gammaℂ w ^ NumberField.InfinitePlace.nrComplexPlaces K

theorem dedekindGammaFactor_ne_zero (K : Type*) [Field K] [NumberField K]
    {w : ℂ} (hw : 0 < w.re) : dedekindGammaFactor K w ≠ 0 := by
  have hD : ((|NumberField.discr K| : ℤ) : ℂ) ≠ 0 := by
    simp [NumberField.discr_ne_zero K]
  have hBase : (2 : ℂ) * Real.pi ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hC : Complex.Gammaℂ w ≠ 0 := by
    rw [Complex.Gammaℂ_def]
    exact mul_ne_zero
      (mul_ne_zero two_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hBase)))
      (Complex.Gamma_ne_zero_of_re_pos hw)
  exact mul_ne_zero
    (mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hD))
      (pow_ne_zero _ (Complex.Gammaℝ_ne_zero_of_re_pos hw)))
    (pow_ne_zero _ hC)

theorem continuation_reflects_zeros_of_functionalEquation {Z : ℂ → ℂ}
    (hZ : IsDedekindZeta K Z)
    (hfe : ∀ w : ℂ, 0 < w.re → w.re < 1 →
      dedekindGammaFactor K (1 - w) * Z (1 - w) = dedekindGammaFactor K w * Z w)
    (w : ℂ) (hw₀ : 0 < w.re) (hw₁ : w.re < 1) (hz : Z w = 0) :
    Z (1 - conj w) = 0 :=
  continuation_reflects_zeros_of_completion hZ (fun _ _ _ => rfl)
    (fun _ hw _ => dedekindGammaFactor_ne_zero K hw) hfe w hw₀ hw₁ hz

/-- An external zero-free estimate for one continuation applies to every
continuation compared away from the pole. -/
theorem continuation_ne_zero_above {Z W : ℂ → ℂ} {b : ℝ}
    (hZ : IsDedekindZeta K Z) (hW : IsDedekindZeta K W)
    (hfree : ∀ w : ℂ, b < w.re → w ≠ 1 → W w ≠ 0)
    {w : ℂ} (hwb : b < w.re) (hw : w ≠ 1) : Z w ≠ 0 := by
  rw [continuation_eq_off_one hZ hW hw]
  exact hfree w hwb hw

/-- Restrict the locating premise to the part of the strip left by an
external zero-free bound. The proof uses the original signed-gap theorem. -/
theorem dedekindZetaRH_of_same_input_signed_gap_below
    {Orbit : Type*} {Z U V : ℂ → ℂ} {b : ℝ}
    (hZ : IsDedekindZeta K Z)
    (hfree : ∃ W : ℂ → ℂ, IsDedekindZeta K W ∧
      ∀ w : ℂ, b < w.re → w ≠ 1 → W w ≠ 0)
    (region : Orbit → Set ℂ) (axis : Orbit → ℂ)
    (retained : Orbit → ℂ → ℂ) (main tail : Orbit → ℂ → ℝ)
    (hzero : ∀ w : ℂ, 0 < w.re → w.re < 1 → Z w = 0 → U w = V w)
    (hreflect : ∀ w : ℂ, 0 < w.re → w.re < 1 → Z w = 0 → Z (1 - conj w) = 0)
    (hlocate : ∀ w : ℂ, 1 / 2 < w.re → w.re < 1 → w.re ≤ b →
      Z w = 0 → ∃ a : Orbit, w ∈ region a)
    (hgap : ∀ a w, w ∈ region a → tail a w < main a w)
    (hmodel : ∀ a w, w ∈ region a → (retained a w).im ≤ -main a w)
    (htail : ∀ a w, w ∈ region a → (axis a * (U w - V w) - retained a w).im ≤ tail a w) :
    DedekindZetaRH K := by
  obtain ⟨W, hW, hBounds⟩ := hfree
  refine dedekindZetaRH_of_same_input_signed_gap hZ region axis retained main tail
    hzero hreflect ?_ hgap hmodel htail
  intro w hr h₁ hz
  have hw : w ≠ 1 := by rintro rfl; norm_num at h₁
  have hb : w.re ≤ b :=
    le_of_not_gt (fun h => (continuation_ne_zero_above hZ hW hBounds h hw) hz)
  exact hlocate w hr h₁ hb hz

#check continuation_reflects_zeros_of_completion
#check continuation_reflects_zeros_of_functionalEquation
#check dedekindZetaRH_of_same_input_signed_gap_below
#print axioms dedekindZeta_conj_argument
#print axioms continuation_conj_argument
#print axioms continuation_reflects_zeros_of_completion
#print axioms dedekindGammaFactor_ne_zero
#print axioms continuation_reflects_zeros_of_functionalEquation
#print axioms continuation_ne_zero_above
#print axioms dedekindZetaRH_of_same_input_signed_gap_below

end FieldTarget
