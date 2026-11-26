import GaussianHermitePrimePolynomial
import GaussianPrimeSupport

/-! Read the odd coefficients of the checked Hermite polynomial at the
actual Gaussian radicand. On the rational comparison primes, their two
reductions agree and the real coordinate recovers the sign. -/

namespace AlpogeSuperZeta

open Finset Polynomial QuarticModel

noncomputable section

def hermiteOddPolynomial (m c : ℕ) : ℤ[X] :=
  ∑ k ∈ range m, C (((hermitePrimePolynomial m).comp (X + C (c : ℤ))).coeff (2 * k + 1)) * X ^ k

theorem hermiteOddPolynomial_mod_prime {m p : ℕ} (c : ℕ)
    (hp : p.Prime) (hp₂ : p ≠ 2) (hm : m ≤ p) (hpm : p < 2 * m) :
    (hermiteOddPolynomial m c).map (Int.castRingHom (ZMod p)) =
      C (hermitePrimeScale m : ZMod p) * X ^ (p / 2) := by
  let : Fact p.Prime := ⟨hp⟩
  let f : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let D := (hermitePrimeScale m : ZMod p)
  let W := (hermitePrimePolynomial m).comp (X + C (c : ℤ))
  have hodd := (hp.mod_two_eq_one_iff_ne_two).mpr hp₂
  have hpEq : 2 * (p / 2) + 1 = p := by omega
  have hmap : W.map f = C D * X ^ p + C (D * (c : ZMod p)) := by
    dsimp only [W, f]
    rw [map_comp, hermitePrimePolynomial_mod_prime hp hm hpm]
    simp only [Polynomial.map_add, map_X, map_natCast, Polynomial.map_natCast, mul_comp, C_comp, pow_comp, X_comp]
    have hc : ((c : (ZMod p)[X])) ^ p = C (c : ZMod p) := by
      change C (c : ZMod p) ^ p = C (c : ZMod p)
      rw [← C_pow, ZMod.pow_card]
    rw [add_pow_char _ _ p, hc, mul_add, ← C_mul]
  have hcoeff (k : ℕ) : f (W.coeff (2 * k + 1)) = if k = p / 2 then D else 0 := by
    rw [← coeff_map, hmap, coeff_add, coeff_C_mul, coeff_X_pow,
      coeff_C, if_neg (by omega : 2 * k + 1 ≠ 0), add_zero]
    by_cases h : k = p / 2
    · subst k
      simp [hpEq]
    · have hn : 2 * k + 1 ≠ p := by omega
      simp [h, hn]
  classical
  simp only [hermiteOddPolynomial, Polynomial.map_sum, Polynomial.map_mul, map_C,
    Polynomial.map_pow, map_X]
  change (∑ k ∈ range m, C (f (W.coeff (2 * k + 1))) * X ^ k) = _
  simp_rw [hcoeff, apply_ite C, C_0, ite_mul, zero_mul]
  rw [sum_ite_eq', if_pos (mem_range.mpr (by omega : p / 2 < m))]

def archivedHermiteRadicand : GaussianInt := ⟨-5045155, 1027708⟩

def archivedHermiteOddValue (m : ℕ) : GaussianInt :=
  (hermiteOddPolynomial m ((m - 1) / 2)).eval₂ (Int.castRingHom GaussianInt) archivedHermiteRadicand

private def gaussianReduction {p : ℕ} (r : ZMod p) (hr : r ^ 2 = -1) :
    GaussianInt →+* ZMod p :=
  Zsqrtd.lift ⟨r, by simpa only [pow_two, Int.cast_neg, Int.cast_one] using hr⟩

private theorem gaussianReduction_apply {p : ℕ} (r : ZMod p) (hr : r ^ 2 = -1)
    (u : GaussianInt) : gaussianReduction r hr u = (u.re : ZMod p) + (u.im : ZMod p) * r := rfl

private theorem gaussianReduction_archivedHermiteOddValue {m p : ℕ}
    (hp : p.Prime) (hp₂ : p ≠ 2) (hm : m ≤ p) (hpm : p < 2 * m)
    (r : ZMod p) (hr : r ^ 2 = -1) :
    gaussianReduction r hr (archivedHermiteOddValue m) =
      (hermitePrimeScale m : ZMod p) * ((-5045155 : ZMod p) + 1027708 * r) ^ (p / 2) := by
  have hhom : (gaussianReduction r hr).comp (Int.castRingHom GaussianInt) =
      Int.castRingHom (ZMod p) := by ext z; simp
  rw [archivedHermiteOddValue, Polynomial.hom_eval₂, hhom, eval₂_eq_eval_map,
    hermiteOddPolynomial_mod_prime _ hp hp₂ hm hpm, eval_mul, eval_C, eval_pow, eval_X,
    gaussianReduction_apply]
  norm_num [archivedHermiteRadicand]

theorem hermitePrimeScale_cast_ne_zero {m p : ℕ} (hp : p.Prime) (hm : m ≤ p) :
    (hermitePrimeScale m : ZMod p) ≠ 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hn : (((m - 1).factorial : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hd := (CharP.cast_eq_zero_iff (ZMod p) p _).mp h
    have hle := hp.dvd_factorial.mp hd
    have hpos := hp.pos
    omega
  simpa only [hermitePrimeScale, Int.cast_pow, Int.cast_natCast] using pow_ne_zero 2 hn

/-- On the rational comparison primes, both marked reductions give the
same sign. The imaginary coordinate vanishes modulo the rational prime. -/
theorem archivedHermiteOddValue_mod_comparison_prime {m p : ℕ}
    (hp : p.Prime) (hm : m ≤ p) (hpm : p < 2 * m) (hp₁ : p % 4 = 1)
    (hC : p.Coprime 26509772707289) (hD : rationalNormSign p = 1) :
    ∃ e : ℤ, (e = 1 ∨ e = -1) ∧ archivedGaussianPrimeWeight p = 2 * (e : ℝ) ∧
      ((archivedHermiteOddValue m).re : ZMod p) = (hermitePrimeScale m : ZMod p) * (e : ZMod p) ∧
      ((archivedHermiteOddValue m).im : ZMod p) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  have hp₂ : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_num, ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun hd => hp₂ ((Nat.dvd_prime_two_le Nat.prime_two hp.two_le).mp hd)
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  have hr₀ : r ^ 2 = -1 := by simpa only [pow_two] using hr.symm
  have hrNe : r ≠ 0 := by intro h; rw [h] at hr₀; simp at hr₀
  let u : ZMod p := -5045155 + 1027708 * r
  let v : ZMod p := -5045155 - 1027708 * r
  let e := quadraticChar (ZMod p) u
  let f := quadraticChar (ZMod p) v
  have huv : u * v ≠ 0 := by
    dsimp only [u, v]
    rw [discriminant_pair_product r hr₀]
    exact norm_discriminant_ne_zero hC
  have he : e = 1 ∨ e = -1 := quadraticChar_dichotomy (left_ne_zero_of_mul huv)
  have hprod : e * f = 1 := (discriminant_pair_sign_product hp₂ r hr₀).trans hD
  have hEF : f = e := by rcases he with h | h <;> rw [h] at hprod ⊢ <;> linarith
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hU : u ^ (p / 2) = (e : ZMod p) := by
    change _ = (quadraticChar (ZMod p) u : ZMod p)
    rw [quadraticChar_eq_pow_of_char_ne_two' hchar, ZMod.card]
  have hV : v ^ (p / 2) = (e : ZMod p) := by
    rw [← hEF]
    change _ = (quadraticChar (ZMod p) v : ZMod p)
    rw [quadraticChar_eq_pow_of_char_ne_two' hchar, ZMod.card]
  have hL := gaussianReduction_archivedHermiteOddValue hp hp₂ hm hpm r hr₀
  have hR := gaussianReduction_archivedHermiteOddValue hp hp₂ hm hpm (-r) ((neg_sq r).trans hr₀)
  rw [gaussianReduction_apply] at hL hR
  simp only [mul_neg, ← sub_eq_add_neg] at hR
  change _ = (hermitePrimeScale m : ZMod p) * u ^ (p / 2) at hL
  change _ = (hermitePrimeScale m : ZMod p) * v ^ (p / 2) at hR
  rw [hU] at hL
  rw [hV] at hR
  let z := archivedHermiteOddValue m
  have hIm : (z.im : ZMod p) = 0 := by
    have h : (2 : ZMod p) * (z.im : ZMod p) * r = 0 := by
      change _ + _ * _ = _ at hL
      change _ - _ * _ = _ at hR
      linear_combination hL - hR
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hrNe)).resolve_left h2
  refine ⟨e, he, ?_, ?_, hIm⟩
  · rw [archivedGaussianPrimeWeight_split hp₂ r hr₀]
    change (e : ℝ) + (f : ℝ) = _
    rw [hEF, two_mul]
  · change (z.re : ZMod p) + (z.im : ZMod p) * r = _ at hL
    simpa only [hIm, zero_mul, add_zero] using hL

#print axioms hermiteOddPolynomial_mod_prime
#print axioms hermitePrimeScale_cast_ne_zero
#print axioms archivedHermiteOddValue_mod_comparison_prime

end
end AlpogeSuperZeta
