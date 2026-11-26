import SuperZeta.UnitSpectrum
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace AlpogeSuperZeta

open Complex Filter Set
open scoped Topology
open SuperZeta

noncomputable section

def corrected (s : ℂ) : ℂ :=
  UnitSpectrum.continuation s - Reference.entireCorrection 1 s

theorem corrected_eq (s : ℂ) :
    corrected s = Spectrum.riemannFactor s * riemannZeta (2 * s) := by
  simp [corrected, UnitSpectrum.continuation]

def normalized (s : ℂ) : ℂ := corrected s / Spectrum.riemannFactor s

theorem normalized_eq {s : ℂ} (hs : 0 < s.re) :
    normalized s = riemannZeta (2 * s) := by
  rw [normalized, corrected_eq, mul_div_cancel_left₀ _ (Spectrum.riemannFactor_ne_zero hs)]

/-- The full continued root sum has the residue already computed for the
reference expression. The entire correction agrees with that expression locally. -/
theorem continuation_residue_half :
    Tendsto (fun s : ℂ => (s - 1 / 2) * UnitSpectrum.continuation s)
      (𝓝[≠] (1 / 2)) (𝓝 ((Real.pi : ℂ)⁻¹)) := by
  refine (Reference.residue_half (q := 1) (by norm_num)).congr' ?_
  have hs : ∀ᶠ s : ℂ in 𝓝 (1 / 2 : ℂ), s.re < 1 :=
    (isOpen_lt continuous_re continuous_const).mem_nhds (by norm_num)
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds] with s h
  simp only [Reference.continuedExpression, UnitSpectrum.continuation,
    Reference.entireCorrection_eq (by norm_num : (0 : ℝ) ≤ 1) h]
  ring

theorem corrected_residue_half :
    Tendsto (fun s : ℂ => (s - 1 / 2) * corrected s)
      (𝓝[≠] (1 / 2)) (𝓝 ((Real.pi : ℂ)⁻¹)) := by
  have hJ := ((Reference.entireCorrection_differentiable (by norm_num : (0 : ℝ) ≤ 1))
    (1 / 2)).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds (s := {(1 / 2 : ℂ)}ᶜ))
  have hid : Tendsto (fun s : ℂ => s - 1 / 2) (𝓝[≠] (1 / 2)) (𝓝 0) := by
    have hi : Tendsto (fun s : ℂ => s) (𝓝[≠] (1 / 2 : ℂ)) (𝓝 (1 / 2 : ℂ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [sub_self] using hi.sub_const (1 / 2 : ℂ)
  have h := continuation_residue_half.sub (hid.mul hJ)
  simpa only [zero_mul, sub_zero, ← mul_sub, corrected] using h

theorem prefactor_zero_iff (s : ℂ) :
    Spectrum.riemannFactor s = 0 ↔ ∃ k : ℤ,
      Complex.log 2 * (2 * s) = (k : ℂ) * (2 * Real.pi * I) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hpow : (Real.pi : ℂ) ^ (-(2 * s)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)
  simp only [Spectrum.riemannFactor, mul_eq_zero, two_ne_zero, hpow, false_or, sub_eq_zero]
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0), Complex.exp_eq_one_iff]

theorem corrected_zero_cases {s : ℂ} (_hp : 2 * s ≠ 1) :
    corrected s = 0 ↔ (∃ k : ℤ,
      Complex.log 2 * (2 * s) = (k : ℂ) * (2 * Real.pi * I)) ∨ riemannZeta (2 * s) = 0 := by
  rw [corrected_eq, mul_eq_zero, prefactor_zero_iff]

/-- The prefactor is the local Euler-factor removal at 2, times a nonzero
elementary factor. This is the same operation used in level change. -/
theorem corrected_eq_triv_char_two {s : ℂ} (hp : 2 * s ≠ 1) :
    corrected s = 2 * (Real.pi : ℂ) ^ (-(2 * s)) * (2 : ℂ) ^ (2 * s) *
      DirichletCharacter.LFunctionTrivChar 2 (2 * s) := by
  rw [corrected_eq, DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := 2) hp]
  rw [Nat.prime_two.primeFactors, Finset.prod_singleton, Nat.cast_ofNat]
  have h₂ : (2 : ℂ) ^ (2 * s) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have heuler : (2 : ℂ) ^ (2 * s) * (1 - (2 : ℂ) ^ (-(2 * s))) =
      (2 : ℂ) ^ (2 * s) - 1 := by
    rw [Complex.cpow_neg, mul_sub, mul_one, mul_inv_cancel₀ h₂]
  rw [Spectrum.riemannFactor, ← heuler]
  ring

theorem normalized_reflect {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2) :
    normalized (1 / 2 - s) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(2 * s)) * Gamma (2 * s) *
        cos ((Real.pi : ℂ) * (2 * s) / 2) * normalized s := by
  have hm : 0 < (1 / 2 - s).re := by simp [sub_re]; linarith
  have hnat (n : ℕ) : 2 * s ≠ -(n : ℂ) := by
    intro h
    have hh := congrArg Complex.re h
    simp [two_mul] at hh
    linarith [Nat.cast_nonneg (α := ℝ) n]
  rw [normalized_eq hm, normalized_eq h₀, show 2 * (1 / 2 - s) = 1 - 2 * s by ring]
  exact riemannZeta_one_sub hnat (Multiplicity.doubled_ne_pole h₁)

theorem normalized_reflect_zero_iff {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2) :
    normalized (1 / 2 - s) = 0 ↔ normalized s = 0 := by
  have hm₀ : 0 < (1 / 2 - s).re := by simp [sub_re]; linarith
  have hm₁ : (1 / 2 - s).re < 1 / 2 := by simp [sub_re]; linarith
  constructor
  · intro h
    have hh := normalized_reflect hm₀ hm₁
    rw [show (1 / 2 : ℂ) - (1 / 2 - s) = s by ring, h, mul_zero] at hh
    exact hh
  · intro h
    rw [normalized_reflect h₀ h₁, h, mul_zero]

open scoped ComplexConjugate in
theorem normalized_conj {s : ℂ} (h₀ : 0 < s.re) :
    normalized (conj s) = conj (normalized s) := by
  rw [normalized_eq (by simpa using h₀), normalized_eq h₀,
    show 2 * conj s = conj (2 * s) by simp only [map_mul, map_ofNat], riemannZeta_conj]

open scoped ComplexConjugate in
theorem normalized_mirror_zero_iff {s : ℂ} (h₀ : 0 < s.re) (h₁ : s.re < 1 / 2) :
    normalized (1 / 2 - conj s) = 0 ↔ normalized s = 0 := by
  have ha : 0 < (conj s).re := by simpa using h₀
  have hb : (conj s).re < 1 / 2 := by simpa using h₁
  rw [normalized_reflect_zero_iff ha hb, normalized_conj h₀]
  simp

/-- This exposes the analytic input to prime-power arguments. Multiplying
the normalized logarithmic derivative by 1/2 returns the ordinary one. -/
theorem corrected_logDeriv {s : ℂ} (h₀ : 0 < s.re) (hp : 2 * s ≠ 1)
    (hz : riemannZeta (2 * s) ≠ 0) :
    logDeriv corrected s - logDeriv Spectrum.riemannFactor s =
      2 * logDeriv riemannZeta (2 * s) := by
  have hh : HasDerivAt (fun t : ℂ => 2 * t) 2 s := by
    simpa using (hasDerivAt_id s).const_mul 2
  have hd := (differentiableAt_riemannZeta hp).hasDerivAt.comp s hh
  change HasDerivAt (fun t : ℂ => riemannZeta (2 * t)) (deriv riemannZeta (2 * s) * 2) s at hd
  rw [funext corrected_eq, logDeriv_mul (g := fun t => riemannZeta (2 * t)) s
    (Spectrum.riemannFactor_ne_zero h₀) hz
    (Multiplicity.analytic_factor s).differentiableAt hd.differentiableAt, add_sub_cancel_left]
  change deriv (fun t : ℂ => riemannZeta (2 * t)) s / riemannZeta (2 * s) = _
  rw [hd.deriv, logDeriv_apply]
  ring

#print axioms normalized_eq
#print axioms continuation_residue_half
#print axioms corrected_residue_half
#print axioms corrected_zero_cases
#print axioms corrected_eq_triv_char_two
#print axioms normalized_reflect_zero_iff
#print axioms normalized_mirror_zero_iff
#print axioms corrected_logDeriv

end
end AlpogeSuperZeta
