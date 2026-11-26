import GaussianRelativeFrobenius

/-! An integral coefficient recurrence with the archived relative sign
at every marked Gaussian prime. Its multiplication determinant carries
the square of the marked prime ideal at a negative sign. -/

namespace AlpogeSuperZeta

open QuarticModel QuadraticAlgebra

private def gaussianRotationSeed : GaussianInt := ⟨1, 1⟩

private def gaussianBinomialBase : QuadraticAlgebra GaussianInt gaussianDiscriminant 0 :=
  ⟨gaussianRotationSeed, 1⟩

/-- The coefficient of the quadratic generator in (1 + i + ω)^n. -/
def gaussianMarkedCoefficient (n : ℕ) : GaussianInt :=
  (gaussianBinomialBase ^ n).im

theorem gaussianMarkedCoefficient_recurrence (n : ℕ) :
    gaussianMarkedCoefficient (n + 2) =
      2 * gaussianRotationSeed * gaussianMarkedCoefficient (n + 1) -
        (gaussianRotationSeed ^ 2 - gaussianDiscriminant) * gaussianMarkedCoefficient n := by
  simp [gaussianMarkedCoefficient, gaussianBinomialBase, pow_succ]
  ring

/-- The determinant of multiplication by b_n ω in the basis (1, ω). -/
def gaussianMarkedDeterminant (n : ℕ) : GaussianInt :=
  -gaussianDiscriminant * gaussianMarkedCoefficient n ^ 2

private def reduceQuadratic {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r ^ 2 = -1) :
    QuadraticAlgebra GaussianInt gaussianDiscriminant 0 →+*
      QuadraticAlgebra (ZMod p) ((-5045155 : ZMod p) + 1027708 * r) 0 where
  toFun x := ⟨gaussianResidue r hr x.re, gaussianResidue r hr x.im⟩
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' := by intro x y; ext <;> simp
  map_mul' := by intro x y; ext <;> simp [gaussianResidue_discriminant, mul_assoc]

private theorem reduceQuadratic_base {p : ℕ} [Fact p.Prime] (r : ZMod p)
    (hr : r ^ 2 = -1) :
    reduceQuadratic r hr gaussianBinomialBase = ⟨1 + r, 1⟩ := by
  ext <;> simp [reduceQuadratic, gaussianBinomialBase, gaussianRotationSeed,
    gaussianResidue, Zsqrtd.lift_apply_apply]

/-- The same integral recurrence reads the actual ideal sign. The odd
prime and its marked square root of minus one select the residue map. -/
theorem gaussianMarkedCoefficient_residue {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r ^ 2 = -1) (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p) :
    gaussianResidue r hr (gaussianMarkedCoefficient (p + 1)) =
      (1 + r) * (1 + (archivedIdealCharacter (gaussianPrimeAt r hr) : ZMod p)) := by
  let d := (-5045155 : ZMod p) + 1027708 * r
  let t : QuadraticAlgebra (ZMod p) d 0 := ⟨1 + r, 1⟩
  have hbase : reduceQuadratic r hr gaussianBinomialBase = t := reduceQuadratic_base r hr
  have hf := quadratic_frobenius_pow hp d t 1
  rw [pow_one] at hf
  change (reduceQuadratic r hr (gaussianBinomialBase ^ (p + 1))).im = _
  rw [map_pow, hbase, pow_succ, hf, archivedIdealCharacter_at_root hp r hr hI]
  simp only [QuadraticAlgebra.im_mul, t, pow_one, mul_one, zero_mul, add_zero]
  change (1 + r) + (quadraticChar (ZMod p) d : ZMod p) * (1 + r) = _
  ring

/-- The preceding power carries the complementary sign. The factor on
the left is the quadratic norm of the common base. -/
theorem gaussianMarkedCoefficient_residue_before_prime {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r ^ 2 = -1) (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p) :
    ((1 + r) ^ 2 - ((-5045155 : ZMod p) + 1027708 * r)) *
      gaussianResidue r hr (gaussianMarkedCoefficient (p - 1)) =
      (1 + r) * ((archivedIdealCharacter (gaussianPrimeAt r hr) : ZMod p) - 1) := by
  let d := (-5045155 : ZMod p) + 1027708 * r
  let q : ZMod p := (1 + r) ^ 2 - d
  let t : QuadraticAlgebra (ZMod p) d 0 := ⟨1 + r, 1⟩
  have hbase : reduceQuadratic r hr gaussianBinomialBase = t := reduceQuadratic_base r hr
  have hnorm : t * star t = QuadraticAlgebra.C q := by
    ext <;> simp [t, q, pow_two]
    ring
  have hf := quadratic_frobenius_pow hp d t 1
  rw [pow_one] at hf
  have hshift : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le
  have he : (t ^ (p - 1)) * QuadraticAlgebra.C q =
      (⟨t.re, (quadraticChar (ZMod p) d : ZMod p) ^ 1 * t.im⟩ :
        QuadraticAlgebra (ZMod p) d 0) * star t := by
    rw [← hnorm, ← mul_assoc, ← pow_succ, hshift, hf]
  have him := congrArg QuadraticAlgebra.im he
  change q * (reduceQuadratic r hr (gaussianBinomialBase ^ (p - 1))).im = _
  rw [map_pow, hbase, archivedIdealCharacter_at_root hp r hr hI]
  simp only [mul_C_eq_smul, im_smul, smul_eq_mul, QuadraticAlgebra.im_mul,
    re_star, im_star, t, pow_one, mul_one, zero_mul, add_zero] at him
  linear_combination him

theorem gaussianMarkedCoefficient_mem_prime_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r ^ 2 = -1) (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p) :
    gaussianMarkedCoefficient (p + 1) ∈ gaussianPrimeAt r hr ↔
      archivedIdealCharacter (gaussianPrimeAt r hr) = -1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hone := Ring.neg_one_ne_one_of_char_ne_two hchar
  have hs : 1 + r ≠ 0 := by
    intro he
    have hr' : r = -1 := by linear_combination he
    exact hone.symm (by simpa [hr'] using hr)
  have htwo : (1 : ZMod p) + 1 ≠ 0 := by
    intro he
    exact hone (by linear_combination -he)
  change gaussianResidue r hr (gaussianMarkedCoefficient (p + 1)) = 0 ↔ _
  rw [gaussianMarkedCoefficient_residue hp r hr hI, mul_eq_zero, or_iff_right hs,
    archivedIdealCharacter_at_root hp r hr hI]
  let d := (-5045155 : ZMod p) + 1027708 * r
  change 1 + (quadraticChar (ZMod p) d : ZMod p) = 0 ↔ quadraticChar (ZMod p) d = -1
  by_cases hd : d = 0
  · rw [hd, quadraticChar_zero]
    simp
  · rcases quadraticChar_dichotomy hd with h | h
    · rw [h, Int.cast_one]
      simp [htwo]
    · rw [h, Int.cast_neg, Int.cast_one]
      simp

theorem gaussianMarkedCoefficient_before_mem_prime_iff {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (r : ZMod p) (hr : r ^ 2 = -1)
    (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p)
    (hq : (1 + r) ^ 2 ≠ (-5045155 : ZMod p) + 1027708 * r) :
    gaussianMarkedCoefficient (p - 1) ∈ gaussianPrimeAt r hr ↔
      archivedIdealCharacter (gaussianPrimeAt r hr) = 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hone := Ring.neg_one_ne_one_of_char_ne_two hchar
  have hs : 1 + r ≠ 0 := by
    intro he
    have hr' : r = -1 := by linear_combination he
    exact hone.symm (by simpa [hr'] using hr)
  change gaussianResidue r hr (gaussianMarkedCoefficient (p - 1)) = 0 ↔ _
  have hprod :
      ((1 + r) ^ 2 - ((-5045155 : ZMod p) + 1027708 * r)) *
          gaussianResidue r hr (gaussianMarkedCoefficient (p - 1)) = 0 ↔
        gaussianResidue r hr (gaussianMarkedCoefficient (p - 1)) = 0 :=
    mul_eq_zero.trans (or_iff_right (sub_ne_zero.mpr hq))
  rw [← hprod,
    gaussianMarkedCoefficient_residue_before_prime hp r hr hI, mul_eq_zero, or_iff_right hs,
    sub_eq_zero, archivedIdealCharacter_at_root hp r hr hI]
  let d := (-5045155 : ZMod p) + 1027708 * r
  change (quadraticChar (ZMod p) d : ZMod p) = 1 ↔ quadraticChar (ZMod p) d = 1
  by_cases hd : d = 0
  · rw [hd, quadraticChar_zero]
    simp
  · rcases quadraticChar_dichotomy hd with h | h
    · rw [h, Int.cast_one]
      exact ⟨fun _ => rfl, fun _ => rfl⟩
    · rw [h, Int.cast_neg, Int.cast_one]
      simp [hone]

private theorem gaussianMarkedDeterminant_mem_sq {p : ℕ} [Fact p.Prime]
    (r : ZMod p) (hr : r ^ 2 = -1) (n : ℕ)
    (hb : gaussianMarkedCoefficient n ∈ gaussianPrimeAt r hr) :
    gaussianMarkedDeterminant n ∈ (gaussianPrimeAt r hr) ^ 2 := by
  unfold gaussianMarkedDeterminant
  rw [pow_two (gaussianPrimeAt r hr), pow_two (gaussianMarkedCoefficient n)]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul hb hb)

private theorem gaussianMarkedDeterminant_mem_sq_iff {p : ℕ} [Fact p.Prime]
    (r : ZMod p) (hr : r ^ 2 = -1) (n : ℕ)
    (hd : gaussianResidue r hr gaussianDiscriminant ≠ 0) :
    gaussianMarkedDeterminant n ∈ (gaussianPrimeAt r hr) ^ 2 ↔
      gaussianMarkedCoefficient n ∈ gaussianPrimeAt r hr := by
  refine ⟨fun h => ?_, gaussianMarkedDeterminant_mem_sq r hr n⟩
  have hmem : gaussianMarkedDeterminant n ∈ gaussianPrimeAt r hr :=
    Ideal.pow_le_self two_ne_zero h
  change gaussianResidue r hr (gaussianMarkedDeterminant n) = 0 at hmem
  change gaussianResidue r hr (gaussianMarkedCoefficient n) = 0
  simp only [gaussianMarkedDeterminant, map_mul, map_neg, map_pow, mul_eq_zero, neg_eq_zero,
    pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0), hd, false_or] at hmem
  exact hmem

theorem gaussianMarkedDeterminant_mem_prime_sq_of_negative {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (r : ZMod p) (hr : r ^ 2 = -1)
    (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p)
    (hneg : archivedIdealCharacter (gaussianPrimeAt r hr) = -1) :
    gaussianMarkedDeterminant (p + 1) ∈ (gaussianPrimeAt r hr) ^ 2 :=
  gaussianMarkedDeterminant_mem_sq r hr _
    ((gaussianMarkedCoefficient_mem_prime_iff hp r hr hI).mpr hneg)

theorem gaussianMarkedDeterminant_mem_prime_sq_iff {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (r : ZMod p) (hr : r ^ 2 = -1)
    (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p)
    (hd : gaussianResidue r hr gaussianDiscriminant ≠ 0) :
    gaussianMarkedDeterminant (p + 1) ∈ (gaussianPrimeAt r hr) ^ 2 ↔
      archivedIdealCharacter (gaussianPrimeAt r hr) = -1 :=
  (gaussianMarkedDeterminant_mem_sq_iff r hr (p + 1) hd).trans
    (gaussianMarkedCoefficient_mem_prime_iff hp r hr hI)

theorem gaussianMarkedDeterminant_before_mem_prime_sq_iff {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (r : ZMod p) (hr : r ^ 2 = -1)
    (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p)
    (hd : gaussianResidue r hr gaussianDiscriminant ≠ 0)
    (hq : (1 + r) ^ 2 ≠ (-5045155 : ZMod p) + 1027708 * r) :
    gaussianMarkedDeterminant (p - 1) ∈ (gaussianPrimeAt r hr) ^ 2 ↔
      archivedIdealCharacter (gaussianPrimeAt r hr) = 1 :=
  (gaussianMarkedDeterminant_mem_sq_iff r hr (p - 1) hd).trans
    (gaussianMarkedCoefficient_before_mem_prime_iff hp r hr hI hq)

set_option maxRecDepth 20000 in
theorem gaussian_marked_determinant_norm_at_73 :
    (gaussianMarkedDeterminant 72).norm.natAbs % 73 ^ 3 = 111909 ∧
    (gaussianMarkedDeterminant 74).norm.natAbs % 73 ^ 3 = 298424 := by decide +kernel

set_option maxRecDepth 20000 in
theorem gaussian_marked_determinant_cross_contribution_at_5 :
    (gaussianMarkedDeterminant 72).norm.natAbs % 5 ^ 9 = 390625 ∧
    (gaussianMarkedDeterminant 74).norm.natAbs % 5 = 1 := by decide +kernel

#print axioms gaussianMarkedCoefficient_recurrence
#print axioms gaussianMarkedCoefficient_residue
#print axioms gaussianMarkedCoefficient_residue_before_prime
#print axioms gaussianMarkedCoefficient_mem_prime_iff
#print axioms gaussianMarkedCoefficient_before_mem_prime_iff
#print axioms gaussianMarkedDeterminant_mem_prime_sq_iff
#print axioms gaussianMarkedDeterminant_before_mem_prime_sq_iff
#print axioms gaussian_marked_determinant_norm_at_73
#print axioms gaussian_marked_determinant_cross_contribution_at_5

end AlpogeSuperZeta
