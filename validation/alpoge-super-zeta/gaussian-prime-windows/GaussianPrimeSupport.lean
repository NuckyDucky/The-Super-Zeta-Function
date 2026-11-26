import GaussianPrimeOnlyWindow
import RelativeQuarticNormCharacter

/-! The rational characters determine where the Gaussian prime coefficient
is supported. The two marked residue characters determine its sign. -/

namespace AlpogeSuperZeta

open QuarticModel
open scoped Classical

noncomputable section

private theorem primeWeight_first {p : ℕ} (hp : p.Prime) :
    archivedGaussianPrimeWeight p = archivedGaussianPrimePowerWeight p 1 := by
  simpa only [pow_one] using archivedGaussianPrimeWeight_prime_power hp Nat.one_ne_zero

theorem archivedGaussianPrimeWeight_inert {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    archivedGaussianPrimeWeight p = 0 := by
  rw [primeWeight_first Fact.out, archivedGaussianPrimePowerWeight, inert_gaussian_primes hp,
    Finset.sum_singleton, inert_gaussian_prime_degree hp]
  norm_num

theorem archivedIdealCharacter_at_root {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r ^ 2 = -1) (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p) :
    archivedIdealCharacter (gaussianPrimeAt r hr) =
      quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708 * r) := by
  let J : ↥(gaussianPrimesAbove p) := ⟨gaussianPrimeAt r hr, hI⟩
  exact (quarticDiscriminantSign_eq_archivedIdealCharacter p J).symm.trans
    (quarticDiscriminantSign_split hp r hr J rfl)

/-- At a split rational prime, the two local characters are raised to
the same power and then added. -/
theorem archivedGaussianPrimePowerWeight_split {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r ^ 2 = -1) (j : ℕ) :
    archivedGaussianPrimePowerWeight p j =
      (quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708 * r) : ℝ) ^ j +
      (quadraticChar (ZMod p) ((-5045155 : ZMod p) - 1027708 * r) : ℝ) ^ j := by
  have hn : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hr
  have hs := split_gaussian_primes hp r hr hn
  have ha : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p := by simp [hs]
  have hb : gaussianPrimeAt (-r) hn ∈ gaussianPrimesAbove p := by simp [hs]
  have hne := gaussianPrimeAt_distinct hp r hr
  rw [archivedGaussianPrimePowerWeight, hs,
    Finset.sum_insert (by simpa only [Finset.mem_singleton] using hne), Finset.sum_singleton,
    primeAt_degree r hr ha, primeAt_degree (-r) hn hb,
    archivedIdealCharacter_at_root hp r hr ha, archivedIdealCharacter_at_root hp (-r) hn hb]
  simp [mul_neg, ← sub_eq_add_neg]

/-- The residual signs at the two marked primes sum to the first Euler
logarithmic-derivative coefficient. -/
theorem archivedGaussianPrimeWeight_split {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r ^ 2 = -1) :
    archivedGaussianPrimeWeight p =
      (quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708 * r) : ℝ) +
      (quadraticChar (ZMod p) ((-5045155 : ZMod p) - 1027708 * r) : ℝ) := by
  rw [primeWeight_first Fact.out]
  simpa only [pow_one] using archivedGaussianPrimePowerWeight_split hp r hr 1

theorem norm_discriminant_ne_zero {p : ℕ} [Fact p.Prime]
    (hc : p.Coprime 26509772707289) : (26509772707289 : ZMod p) ≠ 0 := by
  have hp : p.Prime := Fact.out
  have h := hp.coprime_iff_not_dvd.mp hc
  simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_zero_iff 26509772707289 p).not.mpr h

private theorem norm_sign_cases {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) : rationalNormSign p = 1 ∨ rationalNormSign p = -1 := by
  rw [← rationalNormSign_reciprocity p hp]
  exact legendreSym.eq_one_or_neg_one p (a := (26509772707289 : ℤ)) (by
    simpa only [Int.cast_ofNat] using norm_discriminant_ne_zero hc)

/-- Away from two and the conductor, two rational quadratic characters
determine the square of the actual Gaussian prime coefficient. -/
theorem archivedGaussianPrimeWeight_sq {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) :
    archivedGaussianPrimeWeight p ^ 2 =
      (1 + (ZMod.χ₄ (p : ZMod 4) : ℝ)) * (1 + (rationalNormSign p : ℝ)) := by
  have ho := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
  by_cases h₃ : p % 4 = 3
  · rw [archivedGaussianPrimeWeight_inert h₃, ZMod.χ₄_nat_three_mod_four h₃]
    norm_num
  have h₁ : p % 4 = 1 := by omega
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr h₃
  have hr' : r ^ 2 = -1 := by rw [pow_two, ← hr]
  let u : ZMod p := (-5045155 : ZMod p) + 1027708 * r
  let v : ZMod p := (-5045155 : ZMod p) - 1027708 * r
  have huv : u * v ≠ 0 := by
    change ((-5045155 : ZMod p) + 1027708 * r) *
      ((-5045155 : ZMod p) - 1027708 * r) ≠ 0
    rw [discriminant_pair_product r hr']
    exact norm_discriminant_ne_zero hc
  have hu : (quadraticChar (ZMod p) u : ℝ) ^ 2 = 1 :=
    by exact_mod_cast quadraticChar_sq_one (left_ne_zero_of_mul huv)
  have hv : (quadraticChar (ZMod p) v : ℝ) ^ 2 = 1 :=
    by exact_mod_cast quadraticChar_sq_one (right_ne_zero_of_mul huv)
  have hprod : (quadraticChar (ZMod p) u : ℝ) * (quadraticChar (ZMod p) v : ℝ) =
      (rationalNormSign p : ℝ) := by
    dsimp only [u, v]
    exact_mod_cast discriminant_pair_sign_product hp r hr'
  rw [archivedGaussianPrimeWeight_split hp r hr', ZMod.χ₄_nat_one_mod_four h₁, Int.cast_one]
  change ((quadraticChar (ZMod p) u : ℝ) + (quadraticChar (ZMod p) v : ℝ)) ^ 2 = _
  rw [add_sq, hu, hv, mul_assoc, hprod]
  ring

theorem archivedGaussianPrimeWeight_ne_zero_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) :
    archivedGaussianPrimeWeight p ≠ 0 ↔ p % 4 = 1 ∧ rationalNormSign p = 1 := by
  have h := archivedGaussianPrimeWeight_sq hp hc
  have ho := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
  by_cases h₁ : p % 4 = 1
  · rw [ZMod.χ₄_nat_one_mod_four h₁] at h
    rcases norm_sign_cases hp hc with hD | hD
    · rw [hD] at h
      norm_num at h
      have hn : archivedGaussianPrimeWeight p ≠ 0 := by
        intro hz
        simp [hz] at h
      simp [hn, h₁, hD]
    · rw [hD] at h
      norm_num at h
      simp [h₁, hD, h]
  · have h₃ : p % 4 = 3 := by omega
    simp [h₁, archivedGaussianPrimeWeight_inert h₃]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩

theorem archivedGaussianPrimeWeight_at_5_and_13 :
    archivedGaussianPrimeWeight 5 = 2 ∧ archivedGaussianPrimeWeight 13 = -2 := by
  rw [archivedGaussianPrimeWeight_split (p := 5) (by decide) 2 (by decide),
    archivedGaussianPrimeWeight_split (p := 13) (by decide) 5 (by decide)]
  have h5a : quadraticChar (ZMod 5) ((-5045155 : ZMod 5) + 1027708 * 2) = 1 := by
    decide +kernel
  have h5b : quadraticChar (ZMod 5) ((-5045155 : ZMod 5) - 1027708 * 2) = 1 := by
    decide +kernel
  have h13a : quadraticChar (ZMod 13) ((-5045155 : ZMod 13) + 1027708 * 5) = -1 := by
    decide +kernel
  have h13b : quadraticChar (ZMod 13) ((-5045155 : ZMod 13) - 1027708 * 5) = -1 := by
    decide +kernel
  rw [h5a, h5b, h13a, h13b]
  norm_num

/-- Even though both rational characters agree at 5 and 13, the signed
prime weights differ. No function of just these two character values can
give the signed weights. -/
theorem no_prime_weight_from_two_rational_characters (F : ℤ → ℤ → ℝ)
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → p.Coprime 26509772707289 →
      archivedGaussianPrimeWeight p = F (ZMod.χ₄ (p : ZMod 4)) (rationalNormSign p)) : False := by
  have h5cop : Nat.Coprime 5 26509772707289 := by decide +kernel
  have h13cop : Nat.Coprime 13 26509772707289 := by decide +kernel
  obtain ⟨h5, h13⟩ := archivedGaussianPrimeWeight_at_5_and_13
  have h5D := (archivedGaussianPrimeWeight_ne_zero_iff (p := 5) (by decide) h5cop).mp
    (by rw [h5]; norm_num)
  have h13D := (archivedGaussianPrimeWeight_ne_zero_iff (p := 13) (by decide) h13cop).mp
    (by rw [h13]; norm_num)
  have hpos := h 5 Fact.out (by decide) h5cop
  have hneg := h 13 Fact.out (by decide) h13cop
  rw [h5, ZMod.χ₄_nat_one_mod_four h5D.1, h5D.2] at hpos
  rw [h13, ZMod.χ₄_nat_one_mod_four h13D.1, h13D.2] at hneg
  linarith

private theorem archivedGaussianSign_natCast (p : ℕ) :
    archivedGaussianSign (p : GaussianInt) = rationalNormSign p := by
  simp [archivedGaussianSign_eq_legendre, rationalNormSign]

private theorem gaussian_inertia_eq_one_or_two {p : ℕ} [Fact p.Prime] {I : Ideal GaussianInt}
    (hi : I ∈ gaussianPrimesAbove p) : I.inertiaDeg ℤ = 1 ∨ I.inertiaDeg ℤ = 2 := by
  by_cases hp : p = 2
  · subst p
    rw [dyadic_gaussian_prime, Finset.mem_singleton] at hi
    exact Or.inl (hi.symm ▸ dyadic_gaussian_prime_degree)
  by_cases h₃ : p % 4 = 3
  · have hI := eq_inert_gaussian_prime h₃ hi
    exact Or.inr (hI.symm ▸ inert_gaussian_prime_degree h₃)
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr h₃
  have hpos : r ^ 2 = -1 := by rw [pow_two, ← hr]
  have hneg : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hpos
  have hsplit := hi
  rw [split_gaussian_primes hp r hpos hneg, Finset.mem_insert, Finset.mem_singleton] at hsplit
  left
  rcases hsplit with hI | hI
  · subst I
    exact primeAt_degree r hpos hi
  · subst I
    exact primeAt_degree (-r) hneg hi

private theorem archivedIdealCharacter_odd_power (I : Ideal GaussianInt) (j : ℕ) :
    (archivedIdealCharacter I : ℝ) ^ (2 * j + 1) = (archivedIdealCharacter I : ℝ) := by
  obtain ⟨z, rfl⟩ : Submodule.IsPrincipal I := inferInstance
  have h (a : ℤ) (b : ℕ) : (jacobiSym a b : ℝ) ^ (2 * j + 1) = (jacobiSym a b : ℝ) := by
    rcases jacobiSym.trichotomy a b with ha | ha | ha <;> simp [ha, pow_add, pow_mul]
  rw [archivedIdealCharacter_span]
  simp only [archivedGaussianSign, Int.cast_mul, mul_pow, h]

/-- Every odd power of a rational prime has exactly the same Gaussian
logarithmic-derivative weight as the first power. -/
theorem archivedGaussianPrimeWeight_odd {p : ℕ} [Fact p.Prime] (j : ℕ) :
    archivedGaussianPrimeWeight (p ^ (2 * j + 1)) = archivedGaussianPrimeWeight p := by
  rw [archivedGaussianPrimeWeight_prime_power Fact.out (by omega), primeWeight_first Fact.out]
  simp only [archivedGaussianPrimePowerWeight]
  refine Finset.sum_congr rfl fun I hI => ?_
  rcases gaussian_inertia_eq_one_or_two hI with h₁ | h₂
  · simp [h₁, archivedIdealCharacter_odd_power]
  · have hodd : ¬ 2 ∣ 2 * j + 1 := by omega
    simp [h₂, hodd]

/-- Away from two and the conductor, all even powers are determined by
the quadratic character of the Gaussian base and the rational norm character. -/
theorem archivedGaussianPrimeWeight_even {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) (j : ℕ) (hj : j ≠ 0) :
    archivedGaussianPrimeWeight (p ^ (2 * j)) =
      1 + (ZMod.χ₄ (p : ZMod 4) : ℝ) ^ j + (rationalNormSign p : ℝ) ^ j -
        ((ZMod.χ₄ (p : ZMod 4) : ℝ) * (rationalNormSign p : ℝ)) ^ j := by
  rw [archivedGaussianPrimeWeight_prime_power Fact.out (by omega)]
  have ho := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
  by_cases h₃ : p % 4 = 3
  · rw [archivedGaussianPrimePowerWeight, inert_gaussian_primes h₃, Finset.sum_singleton,
      inert_gaussian_prime_degree h₃, archivedIdealCharacter_span, archivedGaussianSign_natCast,
      ZMod.χ₄_nat_three_mod_four h₃]
    have hdvd : 2 ∣ 2 * j := dvd_mul_right 2 j
    have hdiv : 2 * j / 2 = j := by omega
    rw [if_pos hdvd, hdiv]
    rcases norm_sign_cases hp hc with hD | hD <;> rw [hD] <;> push_cast <;> simp <;> ring
  · have h₁ : p % 4 = 1 := by omega
    obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr h₃
    have hf : r ^ 2 = -1 := by rw [pow_two, ← hr]
    have huv :
        ((-5045155 : ZMod p) + 1027708 * r) * ((-5045155 : ZMod p) - 1027708 * r) ≠ 0 := by
      rw [discriminant_pair_product r hf]
      exact norm_discriminant_ne_zero hc
    have hu : (quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708 * r) : ℝ) ^ 2 = 1 :=
      by exact_mod_cast quadraticChar_sq_one (left_ne_zero_of_mul huv)
    have hv : (quadraticChar (ZMod p) ((-5045155 : ZMod p) - 1027708 * r) : ℝ) ^ 2 = 1 :=
      by exact_mod_cast quadraticChar_sq_one (right_ne_zero_of_mul huv)
    rw [archivedGaussianPrimePowerWeight_split hp r hf, pow_mul, pow_mul, hu, hv,
      ZMod.χ₄_nat_one_mod_four h₁]
    simp

private theorem archivedGaussianPrimeWeight_even_of_dvd_discriminant {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) (hD : p ∣ 26509772707289) (j : ℕ) (hj : j ≠ 0) :
    archivedGaussianPrimeWeight (p ^ (2 * j)) = 1 := by
  let a : ZMod p := -5045155
  let b : ZMod p := 1027708
  have hz : (26509772707289 : ZMod p) = 0 := by
    simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_zero_iff 26509772707289 p).mpr hD
  have hcop (n : ℕ) (hn : Nat.Coprime 26509772707289 n) : (n : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff n p).mp h
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, Fact.out, hD, hd⟩) hn
  have hb : b ≠ 0 := by
    simpa only [b, Nat.cast_ofNat] using hcop 1027708 (by decide +kernel)
  have hsum : a + a ≠ 0 := by
    rw [show a + a = -(10090310 : ZMod p) by dsimp only [a]; ring]
    exact neg_ne_zero.mpr (by simpa only [Nat.cast_ofNat] using hcop 10090310 (by decide +kernel))
  have hsq : a ^ 2 + b ^ 2 = 0 := by
    rw [show a ^ 2 + b ^ 2 = (26509772707289 : ZMod p) by dsimp only [a, b]; ring, hz]
  let r : ZMod p := -a / b
  have hr : r ^ 2 = -1 := by
    dsimp only [r]
    rw [div_pow, neg_sq]
    apply (div_eq_iff (pow_ne_zero 2 hb)).2
    linear_combination hsq
  have hbr : b * r = -a := by
    dsimp only [r]
    rw [mul_comm b, div_mul_cancel₀ _ hb]
  have hpos : a + b * r = 0 := by rw [hbr]; simp
  have hneg : a - b * r ≠ 0 := by rwa [hbr, sub_neg_eq_add]
  rw [archivedGaussianPrimeWeight_prime_power Fact.out (by omega),
    archivedGaussianPrimePowerWeight_split hp r hr]
  change (quadraticChar (ZMod p) (a + b * r) : ℝ) ^ (2 * j) +
    (quadraticChar (ZMod p) (a - b * r) : ℝ) ^ (2 * j) = 1
  have hchar : (quadraticChar (ZMod p) (a - b * r) : ℝ) ^ 2 = 1 := by
    exact_mod_cast quadraticChar_sq_one hneg
  rw [hpos, quadraticChar_zero, Int.cast_zero, zero_pow (by omega), zero_add, pow_mul, hchar,
    one_pow]

private theorem archivedGaussianPrimeWeight_at_two_power (j : ℕ) (hj : j ≠ 0) :
    archivedGaussianPrimeWeight (2 ^ j) = 1 := by
  rw [archivedGaussianPrimeWeight_prime_power Nat.prime_two hj, archivedGaussianPrimePowerWeight,
    dyadic_gaussian_prime, Finset.sum_singleton, dyadic_gaussian_prime_degree,
    archivedIdealCharacter_span]
  have hsign : archivedGaussianSign (⟨1, 1⟩ : GaussianInt) = 1 := by
    rw [archivedGaussianSign_eq_norm_projection]
    norm_num
  simp [hsign]

/-- The even weights at two and at every prime dividing the conductor are
one. At the other primes the four Dirichlet terms give them exactly. -/
theorem archivedGaussianPrimeWeight_even_all {p : ℕ} [Fact p.Prime] (j : ℕ) (hj : j ≠ 0) :
    archivedGaussianPrimeWeight (p ^ (2 * j)) =
      if p ∣ 2 * 26509772707289 then 1 else
        1 + (ZMod.χ₄ (p : ZMod 4) : ℝ) ^ j + (rationalNormSign p : ℝ) ^ j -
          ((ZMod.χ₄ (p : ZMod 4) : ℝ) * (rationalNormSign p : ℝ)) ^ j := by
  have hprime : p.Prime := Fact.out
  by_cases h : p ∣ 2 * 26509772707289
  · rw [if_pos h]
    by_cases hp : p = 2
    · subst p
      exact archivedGaussianPrimeWeight_at_two_power _ (by omega)
    have hnot : ¬ p ∣ 2 := fun hd => hp ((Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp hd)
    exact archivedGaussianPrimeWeight_even_of_dvd_discriminant hp
      ((hprime.dvd_mul.mp h).resolve_left hnot) j hj
  · rw [if_neg h]
    have hp : p ≠ 2 := by
      intro he
      subst p
      exact h (dvd_mul_right 2 (26509772707289 : ℕ))
    have hc : p.Coprime 26509772707289 :=
      hprime.coprime_iff_not_dvd.mpr (fun hd => h (hd.trans (dvd_mul_left _ _)))
    exact archivedGaussianPrimeWeight_even hp hc j hj

#print axioms archivedGaussianPrimeWeight_split
#print axioms archivedGaussianPrimeWeight_sq
#print axioms archivedGaussianPrimeWeight_ne_zero_iff
#print axioms archivedGaussianPrimeWeight_at_5_and_13
#print axioms no_prime_weight_from_two_rational_characters
#print axioms archivedGaussianPrimeWeight_odd
#print axioms archivedGaussianPrimeWeight_even
#print axioms archivedGaussianPrimeWeight_even_all

end
end AlpogeSuperZeta
