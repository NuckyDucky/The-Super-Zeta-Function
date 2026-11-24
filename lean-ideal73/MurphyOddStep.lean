/- Adapted from DrMurphyIsIn/real-dirichlet-dbn-lean v1.0.0, Apache-2.0.
   See murphy-gauss/LICENSE and murphy-gauss/UPSTREAM-NOTICE.md.
   The version-specific changes specialize the dependency chain to the odd conductor. -/

import QuarticPrimitive
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import GaussCRT

/-! Gauss's sign theorem, stage S3c: **every real primitive Dirichlet character has root number 1.**

Strong induction on the level `N`, peeling one odd prime `p ∥ N` at a time
(`χ = χ_p · χ'` by CRT, `χ_p` the Legendre character), carrying the invariant

`K(χ)`:  `χ(ℓ) = (D/ℓ)` for every odd prime `ℓ ∤ N`,  `D = χ(−1)·N`,

so that the twist `χ_p(N/p) χ'(p) = (χ'(−1)/p)` is computed without further reciprocity
(quadratic reciprocity enters only in proving `K` for the Legendre factor).  Base: levels
`1, 4, 8` (`1`, `χ₋₄`, `χ₈`, `χ₋₈`); levels `2` and `2^e`, `e ≥ 4`, and odd `p² ∣ N` admit no real
primitive character.  conjecture1_proved = False. -/

open Real Complex ZMod

namespace DBN.Gen

open scoped Classical in
/-- The sign `χ(−1) = ±1` as an integer. -/
noncomputable def sgnD {N : ℕ} (χ : DirichletCharacter ℂ N) : ℤ := if χ.Even then 1 else -1

/-- The Kronecker invariant `K(χ)`: `χ(ℓ) = (χ(−1)N / ℓ)` for odd primes `ℓ ∤ N`. -/
def Kprop {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ 2 → ¬ ℓ ∣ N → χ ℓ = ((legendreSym ℓ (sgnD χ * N) : ℤ) : ℂ)

theorem neg_one_sq {N : ℕ} (χ : DirichletCharacter ℂ N) : χ (-1) = 1 ∨ χ (-1) = -1 := by
  have h : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
  have : (χ (-1) - 1) * (χ (-1) + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linear_combination h1
  · right; linear_combination h1

theorem sgnD_cast {N : ℕ} (χ : DirichletCharacter ℂ N) : ((sgnD χ : ℤ) : ℂ) = χ (-1) := by
  unfold sgnD
  split_ifs with h
  · rw [h]; simp
  · rcases neg_one_sq χ with h1 | h1
    · exact absurd h1 h
    · rw [h1]; simp

open scoped Classical in
/-- `rootNumber χ = 1 ↔ τ(χ) = i^k √N`. -/
theorem gaussSum_of_rootNumber {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (h : DirichletCharacter.rootNumber χ = 1) :
    gaussSum χ stdAddChar = I ^ (if χ.Even then 0 else 1) * (N : ℂ) ^ (1 / 2 : ℂ) := by
  have hN : (N : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; push Not; intro h0; exact absurd h0 (by exact_mod_cast NeZero.ne N)
  have hI : I ^ (if χ.Even then 0 else 1) ≠ 0 := pow_ne_zero _ I_ne_zero
  unfold DirichletCharacter.rootNumber at h
  rw [div_div, div_eq_one_iff_eq (mul_ne_zero hI hN)] at h
  exact h

open scoped Classical in
theorem rootNumber_of_gaussSum {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (h : gaussSum χ stdAddChar = I ^ (if χ.Even then 0 else 1) * (N : ℂ) ^ (1 / 2 : ℂ)) :
    DirichletCharacter.rootNumber χ = 1 := by
  have hN : (N : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]; push Not; intro h0; exact absurd h0 (by exact_mod_cast NeZero.ne N)
  have hI : I ^ (if χ.Even then 0 else 1) ≠ 0 := pow_ne_zero _ I_ne_zero
  unfold DirichletCharacter.rootNumber
  rw [div_div, h, div_self (mul_ne_zero hI hN)]

theorem sgnD_of_even {N : ℕ} {χ : DirichletCharacter ℂ N} (h : χ.Even) : sgnD χ = 1 := by
  unfold sgnD; rw [if_pos h]

theorem sgnD_of_not_even {N : ℕ} {χ : DirichletCharacter ℂ N} (h : ¬ χ.Even) : sgnD χ = -1 := by
  unfold sgnD; rw [if_neg h]

theorem two_ne_zero_mod {ℓ : ℕ} [hℓ : Fact ℓ.Prime] (h2 : ℓ ≠ 2) : ((2 : ℤ) : ZMod ℓ) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hd
  have : ℓ ∣ 2 := by exact_mod_cast hd
  exact h2 ((Nat.prime_dvd_prime_iff_eq hℓ.out Nat.prime_two).mp this)

theorem legendre_four {ℓ : ℕ} [Fact ℓ.Prime] (h2 : ℓ ≠ 2) (a : ℤ) :
    legendreSym ℓ (a * 4) = legendreSym ℓ a := by
  rw [legendreSym.mul, show (4 : ℤ) = 2 ^ 2 by norm_num, legendreSym.sq_one' ℓ (two_ne_zero_mod h2),
    mul_one]

theorem K_level_one (χ : DirichletCharacter ℂ 1) : Kprop χ := by
  intro ℓ _ _ _
  have hev : χ.Even := by
    show χ (-1) = 1
    rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]
  rw [sgnD_of_even hev, Nat.cast_one, mul_one, legendreSym.at_one, Int.cast_one,
    show ((ℓ : ℕ) : ZMod 1) = 1 from Subsingleton.elim _ _, map_one]

/-- `χ(−1) = χ₁(−1) χ₂(−1)`. -/
theorem decomp_neg_one {q M : ℕ} (h : q.Coprime M) (χ : DirichletCharacter ℂ (q * M)) :
    χ (-1) = comp1 h χ (-1) * comp2 h χ (-1) := by
  rw [decomp h χ, map_neg, map_one]; rfl

/-- Parity bookkeeping: `χ(−1) = χ₁(−1)χ₂(−1)` with all three `= ±1`. -/
theorem even_iff_comp {q M : ℕ} (h : q.Coprime M) (χ : DirichletCharacter ℂ (q * M)) :
    (χ.Even ↔ ((comp1 h χ).Even ↔ (comp2 h χ).Even)) := by
  unfold DirichletCharacter.Even
  rw [decomp_neg_one h χ]
  rcases neg_one_sq (comp1 h χ) with h1 | h1 <;> rcases neg_one_sq (comp2 h χ) with h2 | h2 <;>
    rw [h1, h2] <;> norm_num

/-- `sgnD` is multiplicative. -/
theorem sgnD_comp {q M : ℕ} (h : q.Coprime M) (χ : DirichletCharacter ℂ (q * M)) :
    sgnD χ = sgnD (comp1 h χ) * sgnD (comp2 h χ) := by
  have he := even_iff_comp h χ
  by_cases e1 : (comp1 h χ).Even <;> by_cases e2 : (comp2 h χ).Even
  · rw [sgnD_of_even (he.mpr (iff_of_true e1 e2)), sgnD_of_even e1, sgnD_of_even e2]; norm_num
  · rw [sgnD_of_not_even (fun hh ↦ e2 ((he.mp hh).mp e1)), sgnD_of_even e1, sgnD_of_not_even e2]
    norm_num
  · rw [sgnD_of_not_even (fun hh ↦ e1 ((he.mp hh).mpr e2)), sgnD_of_not_even e1, sgnD_of_even e2]
    norm_num
  · rw [sgnD_of_even (he.mpr (iff_of_false e1 e2)), sgnD_of_not_even e1, sgnD_of_not_even e2]
    norm_num

/-- `p* `-form of quadratic reciprocity: `(ℓ/p) = (p*/ℓ)`. -/
theorem qr_star {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime] (hp2 : p ≠ 2) (hℓ2 : ℓ ≠ 2) :
    legendreSym p ℓ = legendreSym ℓ ((if p % 4 = 1 then 1 else -1) * p) := by
  have hpo : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  have hℓo : ℓ % 2 = 1 := Nat.odd_iff.mp ((Fact.out : ℓ.Prime).odd_of_ne_two hℓ2)
  split_ifs with h4
  · rw [one_mul, legendreSym.quadratic_reciprocity_one_mod_four h4 hℓ2]
  · have h3 : p % 4 = 3 := by omega
    rw [legendreSym.mul, legendreSym.at_neg_one hℓ2]
    rcases (by omega : ℓ % 4 = 1 ∨ ℓ % 4 = 3) with hl | hl
    · rw [ZMod.χ₄_nat_one_mod_four hl, one_mul,
        legendreSym.quadratic_reciprocity_one_mod_four hl hp2]
    · rw [ZMod.χ₄_nat_three_mod_four hl, legendreSym.quadratic_reciprocity_three_mod_four h3 hl]
      ring

section step

variable {p M : ℕ} [hp : Fact p.Prime]

/-- `χ₁.Even ↔ p ≡ 1 mod 4` for the Legendre factor. -/
theorem legendre_even_iff (hp2 : p ≠ 2) (χ₁ : DirichletCharacter ℂ p)
    (hq : ∀ a, χ₁ a = (quadraticChar (ZMod p) a : ℂ)) : χ₁.Even ↔ p % 4 = 1 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have hl := legendreSym.at_neg_one (p := p) hp2
  unfold legendreSym at hl
  rw [Int.cast_neg, Int.cast_one] at hl
  unfold DirichletCharacter.Even
  rw [hq, hl]
  constructor
  · intro h1
    by_contra h4
    have h3 : p % 4 = 3 := by omega
    rw [ZMod.χ₄_nat_three_mod_four h3] at h1; norm_num at h1
  · intro h4; rw [ZMod.χ₄_nat_one_mod_four h4]; simp

/-- **Induction step.** -/
theorem sign_step (hp2 : p ≠ 2) (h : p.Coprime M) [NeZero M] (χ : DirichletCharacter ℂ (p * M))
    (hprim : χ.IsPrimitive) (hreal : ∀ n : ℕ, (χ n).im = 0)
    (ih : DirichletCharacter.rootNumber (comp2 h χ) = 1 ∧ Kprop (comp2 h χ)) :
    DirichletCharacter.rootNumber χ = 1 ∧ Kprop χ := by
  classical
  set χ₁ := comp1 h χ with hχ₁
  set χ₂ := comp2 h χ with hχ₂
  obtain ⟨hreal1, hreal2⟩ := comp_real h χ hreal
  have hprim1 : χ₁.IsPrimitive := comp1_isPrimitive h χ hprim
  have hχ₁1 : χ₁ ≠ 1 := by
    intro h1
    have := (DirichletCharacter.isPrimitive_def χ₁).mp hprim1
    rw [h1, DirichletCharacter.conductor_one] at this
    exact hp.out.ne_one this.symm
  have hq1 := real_char_eq_quadraticChar hp2 χ₁ hχ₁1 hreal1
  have hpM : ¬ p ∣ M := (Nat.Prime.coprime_iff_not_dvd hp.out).mp h
  have hMp : ((M : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hpM
  -- the twist `χ₁(M) χ₂(p)`
  have htw1 : χ₁ (M : ZMod p) = ((legendreSym p M : ℤ) : ℂ) := by
    rw [hq1]; unfold legendreSym; push_cast; rfl
  have htw2 : χ₂ (p : ZMod M) = ((legendreSym p (sgnD χ₂ * M) : ℤ) : ℂ) := ih.2 p hp2 hpM
  have htw : χ₁ (M : ZMod p) * χ₂ (p : ZMod M) = ((legendreSym p (sgnD χ₂) : ℤ) : ℂ) := by
    rw [htw1, htw2, legendreSym.mul, ← Int.cast_mul]
    congr 1
    have := legendreSym.sq_one p hMp
    linear_combination legendreSym p (sgnD χ₂) * this
  have hev1 := legendre_even_iff hp2 χ₁ hq1
  have hev := even_iff_comp h χ
  have hs1 : sgnD χ₁ = if p % 4 = 1 then 1 else -1 := by
    by_cases e1 : χ₁.Even
    · rw [sgnD_of_even e1, if_pos (hev1.mp e1)]
    · rw [sgnD_of_not_even e1, if_neg (fun h4 ↦ e1 (hev1.mpr h4))]
  have hlp : ((legendreSym p (-1) : ℤ) : ℂ) = if χ₁.Even then 1 else -1 := by
    rw [legendreSym.at_neg_one hp2]
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
    by_cases e1 : χ₁.Even
    · rw [if_pos e1, ZMod.χ₄_nat_one_mod_four (hev1.mp e1)]; simp
    · rw [if_neg e1, ZMod.χ₄_nat_three_mod_four (by have := mt hev1.mpr e1; omega)]; simp
  refine ⟨rootNumber_of_gaussSum ?_, ?_⟩
  · have ε1 := rootNumber_eq_one_of_prime hp2 χ₁ hχ₁1 hreal1
    rw [gaussSum_decomp h χ, htw, gaussSum_of_rootNumber ε1, gaussSum_of_rootNumber ih.1,
      Nat.cast_mul, natCast_mul_natCast_cpow]
    by_cases e1 : χ₁.Even <;> by_cases e2 : χ₂.Even
    · rw [if_pos (hev.mpr (iff_of_true e1 e2)), if_pos e1, if_pos e2, sgnD_of_even e2,
        legendreSym.at_one]
      push_cast; ring
    · rw [if_neg (fun hh ↦ e2 ((hev.mp hh).mp e1)), if_pos e1, if_neg e2, sgnD_of_not_even e2, hlp,
        if_pos e1]
      ring
    · rw [if_neg (fun hh ↦ e1 ((hev.mp hh).mpr e2)), if_neg e1, if_pos e2, sgnD_of_even e2,
        legendreSym.at_one]
      push_cast; ring
    · rw [if_pos (hev.mpr (iff_of_false e1 e2)), if_neg e1, if_neg e2, sgnD_of_not_even e2, hlp,
        if_neg e1]
      ring_nf; rw [I_sq]; ring
  · intro ℓ _ hℓ2 hℓd
    have hℓM : ¬ ℓ ∣ M := fun hd ↦ hℓd (dvd_mul_of_dvd_right hd p)
    rw [decomp_nat h χ ℓ, ih.2 ℓ hℓ2 hℓM, sgnD_comp h χ, hs1]
    have h1 : χ₁ (ℓ : ZMod p) = ((legendreSym p ℓ : ℤ) : ℂ) := by
      rw [hq1]; unfold legendreSym; push_cast; rfl
    rw [h1, qr_star hp2 hℓ2, ← Int.cast_mul, ← legendreSym.mul]
    congr 2
    push_cast
    ring

end step

end DBN.Gen
