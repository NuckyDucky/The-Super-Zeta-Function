import GaussianMoebiusPairContent

/-! Local Euler corrections for the pair of coprime squarefree norms.
One cutoff can be removed at a time after cancelling the factors on the
unrestricted side. -/

namespace AlpogeSuperZeta

open QuarticModel

/-- The common cutoff product and the overlap where both cutoffs differ from one. -/
theorem gaussianPrimitive_cutoff_identity {R : Type*} [CommRing R] (u v : R) :
    u * v = u + v - 1 + (1 - u) * (1 - v) := by ring

def gaussianPrimitiveInversePolynomial {R : Type*} [CommRing R] (a c x : R) : R :=
  1 - a * x + c * x ^ 2

/-- Inverse Euler factors at steps two through seven for the unrestricted variable. -/
def gaussianPrimitiveHigherFactors {R : Type*} [CommRing R] (a b e x : R) : R :=
  let c := b * e
  let q := gaussianPrimitiveInversePolynomial a c
  (1 - c * x ^ 2) * q (x ^ 3) *
    ((1 - b * x ^ 4) * (1 - e * x ^ 4) * (1 - c * x ^ 4)) * q (x ^ 5) ^ 3 *
    ((1 - x ^ 6) ^ 2 * (1 - b * x ^ 6) ^ 2 * (1 - e * x ^ 6) ^ 2 *
      (1 - c * x ^ 6) ^ 3) * q (x ^ 7) ^ 9

private def primeCases {R : Type*} [CommRing R] (a b e : R) : Prop :=
  (a = 2 ∧ b = 1 ∧ e = 1) ∨ (a = -2 ∧ b = 1 ∧ e = 1) ∨
  (a = 0 ∧ b = -1 ∧ e = -1) ∨ (a = 0 ∧ b = 1 ∧ e = -1) ∨
  (a = 0 ∧ b = -1 ∧ e = 1)

private theorem linear_mul {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = 0)
    (a b : R) : (1 - a * x) * (1 - b * x) = 1 - (a + b) * x := by
  linear_combination a * b * hx

private theorem linear_pow {R : Type*} [CommRing R] {x : R} (hx : x ^ 2 = 0)
    (a : R) (n : ℕ) : (1 - a * x) ^ n = 1 - ((n : R) * a) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, linear_mul hx, Nat.cast_succ]
    ring

private theorem primeCases_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {a b e : R} (h : primeCases a b e) :
    primeCases (f a) (f b) (f e) := by
  have h₂ : f (2 : R) = 2 := map_ofNat f 2
  have hn₂ : f (-2 : R) = -2 := by rw [map_neg, h₂]
  have hn₁ : f (-1 : R) = -1 := by rw [map_neg, map_one]
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Or.inl ⟨h₂, map_one f, map_one f⟩
  · exact Or.inr (Or.inl ⟨hn₂, map_one f, map_one f⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨map_zero f, hn₁, hn₁⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨map_zero f, map_one f, hn₁⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨map_zero f, hn₁, map_one f⟩)))

private theorem primitive_product_nilpotent {R : Type*} [CommRing R]
    (a b e x : R) (hx : x ^ 8 = 0) (h : primeCases a b e) :
    gaussianPrimitiveInversePolynomial a (b * e) x *
      gaussianPrimitiveHigherFactors a b e x = 1 - a * x := by
  have hn (n : ℕ) (hle : 8 ≤ n) : x ^ n = 0 := pow_eq_zero_of_le hle hx
  have h4 : (x ^ 4) ^ 2 = 0 := by rw [← pow_mul]; exact hx
  have h5 : (x ^ 5) ^ 2 = 0 := by rw [← pow_mul]; exact hn 10 (by decide)
  have h6 : (x ^ 6) ^ 2 = 0 := by rw [← pow_mul]; exact hn 12 (by decide)
  have h7 : (x ^ 7) ^ 2 = 0 := by rw [← pow_mul]; exact hn 14 (by decide)
  have h6one : (1 - x ^ 6) ^ 2 = 1 - 2 * x ^ 6 := by
    simpa only [one_mul, mul_one, Nat.cast_ofNat] using linear_pow h6 (1 : R) 2
  dsimp only [gaussianPrimitiveHigherFactors, gaussianPrimitiveInversePolynomial]
  rw [linear_mul h4, linear_mul h4, h5, h7]
  simp only [mul_zero, add_zero]
  rw [linear_pow h5, linear_pow h7, h6one, linear_pow h6, linear_pow h6,
    linear_pow h6, linear_mul h6, linear_mul h6, linear_mul h6]
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    push_cast <;> ring_nf <;>
    simp (disch := decide) only [hn, zero_mul, add_zero, sub_zero]

private theorem primitive_product_dvd {R : Type*} [CommRing R] (a b e x : R)
    (h : primeCases a b e) :
    x ^ 8 ∣ 1 - a * x - gaussianPrimitiveInversePolynomial a (b * e) x *
      gaussianPrimitiveHigherFactors a b e x := by
  let I : Ideal R := Ideal.span {x ^ 8}
  let f := Ideal.Quotient.mk I
  have hx : (f x) ^ 8 = 0 := by
    rw [← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp) : x ^ 8 ∈ I)
  have heq := primitive_product_nilpotent (f a) (f b) (f e) (f x) hx (primeCases_map f h)
  apply Ideal.mem_span_singleton.mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change f _ = 0
  simp only [gaussianPrimitiveHigherFactors, gaussianPrimitiveInversePolynomial] at heq ⊢
  simp only [map_sub, map_one, map_mul, map_pow]
  exact sub_eq_zero.mpr heq.symm

private theorem archivedGaussianPrimitive_primeCases {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hc : p.Coprime 26509772707289) :
    primeCases (archivedGaussianPrimeWeight p : ℂ) (ZMod.χ₄ (p : ZMod 4) : ℂ)
      (rationalNormSign p : ℂ) := by
  have ho := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
  have hb : ZMod.χ₄ (p : ZMod 4) = 1 ∨ ZMod.χ₄ (p : ZMod 4) = -1 := by
    by_cases h : p % 4 = 1
    · exact Or.inl (ZMod.χ₄_nat_one_mod_four h)
    · exact Or.inr (ZMod.χ₄_nat_three_mod_four (by omega))
  have he : rationalNormSign p = 1 ∨ rationalNormSign p = -1 := by
    rw [← rationalNormSign_reciprocity p hp]
    apply legendreSym.eq_one_or_neg_one
    simpa only [Int.cast_ofNat] using norm_discriminant_ne_zero hc
  have hsq : (archivedGaussianPrimeWeight p : ℂ) ^ 2 =
      (1 + (ZMod.χ₄ (p : ZMod 4) : ℂ)) * (1 + (rationalNormSign p : ℂ)) := by
    exact_mod_cast archivedGaussianPrimeWeight_sq hp hc
  have hzero (h : (1 + (ZMod.χ₄ (p : ZMod 4) : ℂ)) *
      (1 + (rationalNormSign p : ℂ)) = 0) :
      (archivedGaussianPrimeWeight p : ℂ) = 0 := by
    have hz := hsq.trans h
    rw [pow_two] at hz
    exact (mul_eq_zero.mp hz).elim id id
  rcases hb with hb | hb <;> rcases he with he | he
  · have ha : (archivedGaussianPrimeWeight p : ℂ) ^ 2 = 4 :=
      hsq.trans (by rw [hb, he]; norm_num)
    have hf : ((archivedGaussianPrimeWeight p : ℂ) - 2) *
        ((archivedGaussianPrimeWeight p : ℂ) + 2) = 0 := by
      linear_combination ha
    rcases mul_eq_zero.mp hf with h | h
    · exact Or.inl ⟨sub_eq_zero.mp h, by exact_mod_cast hb, by exact_mod_cast he⟩
    · exact Or.inr (Or.inl ⟨eq_neg_of_add_eq_zero_left h,
        by exact_mod_cast hb, by exact_mod_cast he⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hzero (by rw [hb, he]; norm_num),
      by exact_mod_cast hb, by exact_mod_cast he⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hzero (by rw [hb, he]; norm_num),
      by exact_mod_cast hb, by exact_mod_cast he⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨hzero (by rw [hb, he]; norm_num),
      by exact_mod_cast hb, by exact_mod_cast he⟩))

/-- The actual prime weight agrees with the product through degree seven.
The statement is divisibility in the polynomial ring over the complex numbers. -/
theorem archivedGaussianPrimitive_euler_correction {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (hc : p.Coprime 26509772707289) :
    let a := Polynomial.C (archivedGaussianPrimeWeight p : ℂ)
    let b := Polynomial.C (ZMod.χ₄ (p : ZMod 4) : ℂ)
    let e := Polynomial.C (rationalNormSign p : ℂ)
    Polynomial.X ^ 8 ∣ 1 - a * Polynomial.X -
      gaussianPrimitiveInversePolynomial a (b * e) Polynomial.X *
        gaussianPrimitiveHigherFactors a b e Polynomial.X := by
  dsimp only
  exact primitive_product_dvd _ _ _ _
    (primeCases_map Polynomial.C (archivedGaussianPrimitive_primeCases hp hc))

/-- After the one-variable Euler correction, the other terms have
degree at least two in x or contain x*y. -/
theorem gaussianPrimitive_mixed_correction {R : Type*} [CommRing R]
    (a b e x y : R) :
    let q := gaussianPrimitiveInversePolynomial a (b * e)
    let v := gaussianPrimitiveHigherFactors a b e y
    1 - a * (x + y) - q x * q y * v =
      q x * (1 - a * y - q y * v) - a ^ 2 * x * y - b * e * x ^ 2 * (1 - a * y) := by
  dsimp only
  generalize gaussianPrimitiveHigherFactors a b e y = v
  simp only [gaussianPrimitiveInversePolynomial]
  ring

/-- The unrestricted splitting factor stays nonzero once the local variable
has norm less than one quarter. -/
theorem archivedGaussianPrimitive_scalarFactor_ne_zero (p : ℕ) {x : ℂ}
    (hx : ‖x‖ < 1 / 4) : 1 - 2 * (archivedGaussianPrimeWeight p : ℂ) * x ≠ 0 := by
  have ha : ‖(archivedGaussianPrimeWeight p : ℂ)‖ ≤ 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      archivedGaussianPrimeWeight_abs_le_two p
  have hm : ‖2 * (archivedGaussianPrimeWeight p : ℂ) * x‖ < 1 := calc
    _ = 2 * ‖(archivedGaussianPrimeWeight p : ℂ)‖ * ‖x‖ := by
      norm_num [norm_mul]
    _ ≤ 4 * ‖x‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x)
    _ < 1 := by linarith
  intro hz
  rw [← sub_eq_zero.mp hz, norm_one] at hm
  exact (lt_irrefl 1) hm

/-- The square-root contour approaches the mixed Euler boundary from its
absolutely convergent side. -/
theorem gaussianPrimitive_oneCutoff_exponents {ε : ℝ} (hε : 0 < ε) :
    ∃ (b z : ℝ), archivedGaussianKnownBoundary < b ∧ 1 < 2 * b ∧ 1 < 8 * z ∧
      1 < b + z ∧ z < b ∧ (b + z) / 2 < 1 / 2 + ε := by
  let δ := min ε (1 / 100)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ₁ : δ ≤ 1 / 100 := min_le_right _ _
  refine ⟨8734 / 10000, 1 - 8734 / 10000 + δ, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [archivedGaussianKnownBoundary] <;> linarith

#print axioms gaussianPrimitive_cutoff_identity
#print axioms archivedGaussianPrimitive_euler_correction
#print axioms gaussianPrimitive_mixed_correction
#print axioms archivedGaussianPrimitive_scalarFactor_ne_zero
#print axioms gaussianPrimitive_oneCutoff_exponents

end AlpogeSuperZeta
