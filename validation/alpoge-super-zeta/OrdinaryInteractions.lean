import AlpogeAdapters
import Mathlib.NumberTheory.LSeries.ZetaZeros

namespace AlpogeSuperZeta

open Complex Set SuperZeta
open ArithmeticFunction
open scoped ArithmeticFunction

noncomputable section

theorem coincidence_iff_mod_two {s : ℂ} (hp : 2 * s ≠ 1) :
    UnitSpectrum.continuation s = Reference.entireCorrection 1 s ↔
      DirichletCharacter.LFunctionTrivChar 2 (2 * s) = 0 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hπp : (Real.pi : ℂ) ^ (-(2 * s)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  have h₂p : (2 : ℂ) ^ (2 * s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  rw [← sub_eq_zero, ← corrected, corrected_eq_triv_char_two hp]
  exact mul_eq_zero.trans (or_iff_right (mul_ne_zero (mul_ne_zero two_ne_zero hπp) h₂p))

/-- The local factor can vanish on the boundary. Ordinary zeta there
is nonzero, by reflection to the line Re w = 1 and the value at zero. -/
theorem zeta_at_imaginary_address_ne_zero {s : ℂ} (hs : s.re = 0) :
    riemannZeta (2 * s) ≠ 0 := by
  rcases eq_or_ne s 0 with rfl | hn
  · simp [riemannZeta_zero]
  let v := (1 : ℂ) - 2 * s
  have hv : v.re = 1 := by simp [v, sub_re, two_mul, hs]
  have h₁ : v ≠ 1 := by
    intro h
    have h₂ : 2 * s = 0 := by linear_combination -h
    exact (mul_ne_zero two_ne_zero hn) h₂
  have hnat (n : ℕ) : v ≠ -(n : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    rw [hv, neg_re, natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hcos : cos ((Real.pi : ℂ) * v / 2) ≠ 0 := by
    rw [Ne, cos_eq_zero_iff]
    rintro ⟨k, hk⟩
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have he : (v - (2 * (k : ℂ) + 1)) * (Real.pi : ℂ) = 0 := by
      linear_combination 2 * hk
    have hvr := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hπ)
    have hi : v.im = 0 := by
      have hz := congrArg Complex.im hvr
      simpa [add_im, mul_im] using hz
    exact h₁ (Complex.ext (by simpa using hv) (by simpa using hi))
  have hpow : (2 * (Real.pi : ℂ)) ^ (-v) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero two_ne_zero
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))
  have hz := riemannZeta_one_sub hnat h₁
  rw [← show 1 - v = 2 * s by dsimp [v]; ring, hz]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpow)
    (Complex.Gamma_ne_zero_of_re_pos (by rw [hv]; norm_num))) hcos)
    (riemannZeta_ne_zero_of_one_le_re hv.ge)

theorem boundary_coincidence_iff {s : ℂ} (hs : s.re = 0) :
    UnitSpectrum.continuation s = Reference.entireCorrection 1 s ↔
      ∃ k : ℤ, Complex.log 2 * (2 * s) = (k : ℂ) * (2 * Real.pi * I) := by
  rw [← sub_eq_zero, ← corrected, corrected_zero_cases (Multiplicity.doubled_ne_pole
    (by rw [hs]; norm_num))]
  exact or_iff_left (zeta_at_imaginary_address_ne_zero hs)

/-- In the half-plane of absolute convergence the normalized difference
recovers the actual prime-power L-series in Alpöge's unhalved variable. -/
theorem spectral_prime_powers {s : ℂ} (hs : 1 < (2 * s).re) :
    (logDeriv Spectrum.riemannFactor s - logDeriv corrected s) / 2 =
      LSeries (fun n : ℕ => (Λ n : ℂ)) (2 * s) := by
  have hs₀ : 0 < s.re := by simp [two_mul] at hs; linarith
  have hp : 2 * s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact (lt_irrefl _ hs)
  have hh := corrected_logDeriv hs₀ hp (riemannZeta_ne_zero_of_one_le_re hs.le)
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    neg_div, ← logDeriv_apply]
  linear_combination -hh / 2

/-- The ordinary correspondence gives a bijective address map on any
chosen region of the open strip. Its compact intersections are finite. -/
theorem compact_coincidences_finite {A : Set ℂ} (hA : IsCompact A)
    (hstrip : ∀ s ∈ A, 0 < s.re ∧ s.re < 1 / 2) :
    {s ∈ A | UnitSpectrum.continuation s = Reference.entireCorrection 1 s}.Finite := by
  let f : ℂ → ℂ := fun s => 2 * s
  have hf : Function.Injective f := fun _ _ h =>
    mul_left_cancel₀ two_ne_zero h
  have hc : IsCompact (f '' A) := hA.image (continuous_const.mul continuous_id)
  apply Set.Finite.of_finite_image (f := f) _ hf.injOn
  refine hc.inter_riemannZetaZeros_finite.subset ?_
  rintro _ ⟨s, ⟨hs, hz⟩, rfl⟩
  exact ⟨mem_image_of_mem _ hs,
    (UnitSpectrum.equality_iff_riemann_zero (hstrip s hs).1 (hstrip s hs).2).2.mp hz⟩

#print axioms coincidence_iff_mod_two
#print axioms zeta_at_imaginary_address_ne_zero
#print axioms boundary_coincidence_iff
#print axioms spectral_prime_powers
#print axioms compact_coincidences_finite

end
end AlpogeSuperZeta
