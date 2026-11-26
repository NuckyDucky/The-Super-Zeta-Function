import GaussianPrimeSupport

/-! The original signed prime coefficient is the unramified degree-one
count minus twice the inert degree-one count. -/

namespace AlpogeSuperZeta

open QuarticModel
open scoped Classical

noncomputable section

/-- Count degree-one primes over p with a nonzero relative character. -/
def archivedUnramifiedDegreeOneWeight (p : ℕ) : ℝ :=
  ∑ I ∈ gaussianPrimesAbove p,
    if I.inertiaDeg ℤ = 1 ∧ archivedIdealCharacter I ≠ 0 then 1 else 0

/-- Count degree-one primes over p with relative character minus one. -/
def archivedInertDegreeOneWeight (p : ℕ) : ℝ :=
  ∑ I ∈ gaussianPrimesAbove p,
    if I.inertiaDeg ℤ = 1 ∧ archivedIdealCharacter I = -1 then 1 else 0

theorem archivedGaussianPrimeWeight_eq_unramified_sub_twice_inert {p : ℕ} (hp : p.Prime) :
    archivedGaussianPrimeWeight p =
      archivedUnramifiedDegreeOneWeight p - 2 * archivedInertDegreeOneWeight p := by
  have hpw := archivedGaussianPrimeWeight_prime_power hp Nat.one_ne_zero
  rw [pow_one] at hpw
  rw [hpw, archivedGaussianPrimePowerWeight, archivedUnramifiedDegreeOneWeight,
    archivedInertDegreeOneWeight, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun I _ => ?_
  by_cases hf : I.inertiaDeg ℤ = 1
  · have ha := abs_le.mp (archivedIdealCharacter_abs_le_one I)
    have hl : (-1 : ℤ) ≤ archivedIdealCharacter I := by exact_mod_cast ha.1
    have hu : archivedIdealCharacter I ≤ 1 := by exact_mod_cast ha.2
    have hc : archivedIdealCharacter I = -1 ∨
        archivedIdealCharacter I = 0 ∨ archivedIdealCharacter I = 1 := by omega
    rcases hc with h | h | h <;> norm_num [hf, h]
  · have hd : ¬ I.inertiaDeg ℤ ∣ 1 := fun h => hf (Nat.dvd_one.mp h)
    simp [hf, hd]

/-- Away from two and the conductor, the base Dirichlet character counts
all the degree-one primes in the Gaussian field. -/
theorem archivedUnramifiedDegreeOneWeight_eq_base {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) :
    archivedUnramifiedDegreeOneWeight p = 1 + (ZMod.χ₄ (p : ZMod 4) : ℝ) := by
  have ho := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
  by_cases h₃ : p % 4 = 3
  · rw [archivedUnramifiedDegreeOneWeight, inert_gaussian_primes h₃, Finset.sum_singleton,
      inert_gaussian_prime_degree h₃, ZMod.χ₄_nat_three_mod_four h₃]
    norm_num
  have h₁ : p % 4 = 1 := by omega
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr h₃
  have hpos : r ^ 2 = -1 := by rw [pow_two, ← hr]
  have hneg : (-r) ^ 2 = -1 := by simpa only [neg_sq] using hpos
  have hs := split_gaussian_primes hp r hpos hneg
  have ha : gaussianPrimeAt r hpos ∈ gaussianPrimesAbove p := by simp [hs]
  have hb : gaussianPrimeAt (-r) hneg ∈ gaussianPrimesAbove p := by simp [hs]
  have hprod : ((-5045155 : ZMod p) + 1027708 * r) *
      ((-5045155 : ZMod p) + 1027708 * (-r)) ≠ 0 := by
    rw [mul_neg, ← sub_eq_add_neg, discriminant_pair_product r hpos]
    exact norm_discriminant_ne_zero hc
  have hleft : archivedIdealCharacter (gaussianPrimeAt r hpos) ≠ 0 :=
    (archivedIdealCharacter_at_root hp r hpos ha).trans_ne
      (quadraticChar_eq_zero_iff.not.mpr (left_ne_zero_of_mul hprod))
  have hright : archivedIdealCharacter (gaussianPrimeAt (-r) hneg) ≠ 0 :=
    (archivedIdealCharacter_at_root hp (-r) hneg hb).trans_ne
      (quadraticChar_eq_zero_iff.not.mpr (right_ne_zero_of_mul hprod))
  have hne := gaussianPrimeAt_distinct hp r hpos
  rw [archivedUnramifiedDegreeOneWeight, hs,
    Finset.sum_insert (by simpa only [Finset.mem_singleton] using hne), Finset.sum_singleton,
    primeAt_degree r hpos ha, primeAt_degree (-r) hneg hb, ZMod.χ₄_nat_one_mod_four h₁]
  simp [hleft, hright]

theorem archivedInertDegreeOneWeight_of_good_prime {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : p.Coprime 26509772707289) :
    2 * archivedInertDegreeOneWeight p =
      1 + (ZMod.χ₄ (p : ZMod 4) : ℝ) - archivedGaussianPrimeWeight p := by
  rw [archivedGaussianPrimeWeight_eq_unramified_sub_twice_inert Fact.out,
    archivedUnramifiedDegreeOneWeight_eq_base hp hc]
  ring

#print axioms archivedGaussianPrimeWeight_eq_unramified_sub_twice_inert
#print axioms archivedUnramifiedDegreeOneWeight_eq_base
#print axioms archivedInertDegreeOneWeight_of_good_prime

end
end AlpogeSuperZeta
