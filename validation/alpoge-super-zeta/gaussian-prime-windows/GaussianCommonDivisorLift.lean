import GaussianIdealCommonDivisor
import Mathlib.NumberTheory.Multiplicity

/-! Lifting the common divisor at the first occurrence of an inert
prime. A generator of that prime is an explicit starting value that
attains valuation one. -/

namespace AlpogeSuperZeta

open QuarticModel QuadraticAlgebra

local notation "R₀" => QuadraticAlgebra GaussianInt gaussianDiscriminant (0 : GaussianInt)
local notation "C₀" => algebraMap GaussianInt R₀

private theorem omega_even_power (k : ℕ) :
    (ω : QuadraticAlgebra GaussianInt gaussianDiscriminant 0) ^ (2 * k) =
      algebraMap GaussianInt _ (gaussianDiscriminant ^ k) := by
  have h : (ω : QuadraticAlgebra GaussianInt gaussianDiscriminant 0) ^ 2 =
      algebraMap GaussianInt _ gaussianDiscriminant := by
    rw [pow_two, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero]
  rw [pow_mul, h, ← map_pow]

/-- The linear term at the starting value zero, evaluated at the
generator π. The even power has zero constant coefficient. -/
theorem gaussianPowerCoefficient_even_mod_square (π : GaussianInt) (k : ℕ) :
    π ^ 2 ∣ gaussianPowerCoefficient π (2 * (k + 1)) -
      π * (2 * (k + 1) : ℕ) * gaussianDiscriminant ^ k := by
  let n := 2 * (k + 1)
  have hsum : (ω : R₀) + C₀ π = ⟨π, 1⟩ :=
    QuadraticAlgebra.ext (by simp) (by simp)
  have hbase : ((ω : R₀) ^ n).im = 0 := by
    rw [omega_even_power]
    exact algebraMap_im _
  have hlin : ((ω : R₀) ^ (n - 1) * C₀ π * n).im =
      π * (n : GaussianInt) * gaussianDiscriminant ^ k := by
    have hn : n - 1 = 2 * k + 1 := by dsimp [n]; omega
    rw [hn, pow_succ, omega_even_power, ← map_natCast C₀ n]
    simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_mul, QuadraticAlgebra.algebraMap_re,
      QuadraticAlgebra.algebraMap_im, QuadraticAlgebra.omega_re, QuadraticAlgebra.omega_im]
    ring
  have hd := sq_dvd_add_pow_sub_sub (C₀ π) (ω : R₀) n
  rw [← map_pow, QuadraticAlgebra.algebraMap_dvd_iff] at hd
  have hi := hd.2
  rw [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_sub, hsum, hlin, hbase, sub_zero] at hi
  exact hi

/-- At a nonzero Gaussian prime, an even index prime to the residue
characteristic has a starting value whose coefficient does not land
in the square of the prime. -/
theorem gaussianCommonDivisor_not_le_prime_sq_of_even {I : Ideal GaussianInt}
    [I.IsPrime] (hI : I ≠ ⊥) {n : ℕ} (hn : 0 < n) (he : Even n)
    (hnI : (n : GaussianInt) ∉ I) (hd : gaussianDiscriminant ∉ I) :
    ¬gaussianCommonDivisorIdeal n ≤ I ^ 2 := by
  obtain ⟨k, hk⟩ := even_iff_two_dvd.mp he
  have hk' : k ≠ 0 := by omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk'
  subst n
  obtain ⟨π, rfl⟩ : Submodule.IsPrincipal I := inferInstance
  have hπ : π ≠ 0 := fun h => hI (Ideal.span_singleton_eq_bot.mpr h)
  have hπp : Prime π := (Ideal.span_singleton_prime hπ).mp inferInstance
  intro h
  have hb := h (Ideal.subset_span (Set.mem_range_self π))
  change gaussianPowerCoefficient π (2 * (j + 1)) ∈ (Ideal.span {π} : Ideal GaussianInt) ^ 2 at hb
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
  have hdiv := (dvd_iff_dvd_of_dvd_sub (gaussianPowerCoefficient_even_mod_square π j)).mp hb
  rw [pow_two, mul_assoc, mul_dvd_mul_iff_left hπ] at hdiv
  rw [Ideal.mem_span_singleton] at hnI hd
  rcases hπp.dvd_or_dvd hdiv with hbad | hbad
  · exact hnI hbad
  · exact hd (hπp.dvd_of_dvd_pow hbad)

#print axioms gaussianPowerCoefficient_even_mod_square
#print axioms gaussianCommonDivisor_not_le_prime_sq_of_even

end AlpogeSuperZeta
