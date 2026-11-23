import GaussianPrimePowerCoefficients
import Mathlib.NumberTheory.ArithmeticFunction.LFunction

/-! Identify the actual quartic ideal-count coefficient at every prime
power with Dirichlet convolution of the original three arithmetic factors. -/

namespace QuarticModel

open FieldCoefficientTransfer ArithmeticFunction PowerSeries
open scoped Classical

noncomputable def signedIdealCoefficients : ArithmeticFunction ℂ :=
  toArithmeticFunction signedIdealNormSum

private noncomputable def atPrimePowers (f : ArithmeticFunction ℂ) (p : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk (fun j => f (p^j))

private theorem atPrimePowers_mul (p : ℕ) (hp : p.Prime) (f g : ArithmeticFunction ℂ) :
    atPrimePowers (f * g) p = atPrimePowers f p * atPrimePowers g p := by
  ext n
  let F := atPrimePowers f p
  let G := atPrimePowers g p
  have hrestrict (h : ArithmeticFunction ℂ) (d : ℕ) (hd : d ∣ p^n) :
      ofPowerSeries p (atPrimePowers h p) d = h d := by
    obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hd
    rw [ofPowerSeries_apply_pow hp.one_lt, atPrimePowers, coeff_mk]
  calc
    coeff n (atPrimePowers (f*g) p) = (f*g) (p^n) := coeff_mk _ _
    _ = (ofPowerSeries p F * ofPowerSeries p G) (p^n) := by
      rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
      apply Finset.sum_congr rfl
      intro d hd
      rw [hrestrict f d.1 (Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hd)),
        hrestrict g d.2 (Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hd))]
    _ = coeff n (F*G) := by rw [← map_mul, ofPowerSeries_apply_pow hp.one_lt]

private theorem atPrimePowers_zeta (p : ℕ) [Fact p.Prime] :
    atPrimePowers zetaCoeff p = weightedGeometricAtDegree 1 1 := by
  ext n
  rw [atPrimePowers, coeff_mk, coeff_weightedGeometricAtDegree _ one_ne_zero]
  simp [zetaCoeff, toArithmeticFunction, (Fact.out : p.Prime).ne_zero]

private theorem atPrimePowers_beta (p : ℕ) [Fact p.Prime] :
    atPrimePowers betaCoeff p = weightedGeometricAtDegree (ZMod.χ₄ (p : ZMod 4) : ℂ) 1 := by
  ext n
  rw [atPrimePowers, coeff_mk, coeff_weightedGeometricAtDegree _ one_ne_zero]
  have h : chi4 (p : ZMod 4) = (ZMod.χ₄ (p : ZMod 4) : ℂ) := rfl
  simp [betaCoeff, toArithmeticFunction, (Fact.out : p.Prime).ne_zero, h]

private theorem atPrimePowers_signed (p : ℕ) [Fact p.Prime] :
    atPrimePowers signedIdealCoefficients p = signedLocalEulerSeries p := by
  ext n
  rw [atPrimePowers, coeff_mk, ← signedIdealNormSum_primePower]
  simp [signedIdealCoefficients, toArithmeticFunction, (Fact.out : p.Prime).ne_zero]

theorem idealCounts_primePower_eq_archived_convolution (p n : ℕ) (hp : p.Prime) :
    idealCounts K (p^n) = (zetaCoeff * betaCoeff * signedIdealCoefficients) (p^n) := by
  let : Fact p.Prime := ⟨hp⟩
  rw [idealCounts_primePower_eq_archived_series]
  symm
  calc
    _ = coeff n (atPrimePowers (zetaCoeff * betaCoeff * signedIdealCoefficients) p) := (coeff_mk _ _).symm
    _ = _ := by rw [atPrimePowers_mul p hp, atPrimePowers_mul p hp,
      atPrimePowers_zeta, atPrimePowers_beta, atPrimePowers_signed]

#print axioms signedIdealCoefficients
#print axioms idealCounts_primePower_eq_archived_convolution

end QuarticModel
