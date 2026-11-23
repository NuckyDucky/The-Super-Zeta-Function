import ArchivedGaussianIdealCharacter
import RelativeQuarticDyadicSign
import RelativeQuarticInertSign
import RelativeQuarticSplitSign

/-! At every Gaussian prime, the original conductor reading supplies the
actual quartic Euler denominator. -/

namespace QuarticModel

open FieldCoefficientTransfer
open scoped Classical

local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

private theorem eq_archived_at_split_root {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) (J : ↥(gaussianPrimesAbove p))
    (hJ : J.val = gaussianPrimeAt r hr) (z : GaussianInt) (hzNorm : z.norm.natAbs = p)
    (hz : gaussianResidue r hr z = 0)
    (hχ : quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708*r) = archivedGaussianSign z) :
    quarticDiscriminantSign p J = archivedIdealCharacter J.val := by
  rw [quarticDiscriminantSign_split hp r hr J hJ, hχ, hJ, gaussianPrimeAt_eq_span r hr z hzNorm hz,
    archivedIdealCharacter_span]

private theorem eq_archived_at_split_pair {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) (rn : (-r)^2 = -1) (J : ↥(gaussianPrimesAbove p))
    (zPos zNeg : GaussianInt) (hPosNorm : zPos.norm.natAbs = p) (hNegNorm : zNeg.norm.natAbs = p)
    (hPosRoot : gaussianResidue r hr zPos = 0) (hNegRoot : gaussianResidue (-r) rn zNeg = 0)
    (hPos : quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708*r) = archivedGaussianSign zPos)
    (hNeg : quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708*(-r)) = archivedGaussianSign zNeg) :
    quarticDiscriminantSign p J = archivedIdealCharacter J.val := by
  have hm {I : Ideal GaussianInt} (hI : I ∈ gaussianPrimesAbove p) :
      I = gaussianPrimeAt r hr ∨ I = gaussianPrimeAt (-r) rn := by
    simpa only [split_gaussian_primes hp r hr rn, Finset.mem_insert, Finset.mem_singleton] using hI
  rcases hm J.property with hJ | hJ
  · exact eq_archived_at_split_root hp r hr J hJ zPos hPosNorm hPosRoot hPos
  · exact eq_archived_at_split_root hp (-r) rn J hJ zNeg hNegNorm hNegRoot hNeg

private theorem split_root_of_mem {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1)
    {I : Ideal GaussianInt} (hI : I ∈ gaussianPrimesAbove p) :
    ∃ r : ZMod p, ∃ hr : r^2 = -1, I = gaussianPrimeAt r hr := by
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  have hs : r^2 = -1 := (pow_two r).trans hr.symm
  have hn : (-r)^2 = -1 := by simpa only [neg_sq] using hs
  have hp₂ : p ≠ 2 := by omega
  rw [split_gaussian_primes hp₂ r hs hn, Finset.mem_insert, Finset.mem_singleton] at hI
  exact hI.elim (fun h => ⟨r,hs,h⟩) (fun h => ⟨-r,hn,h⟩)

private theorem eq_archived_at_split_coprime {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1)
    (hcop : p.Coprime 26509772707289) (J : ↥(gaussianPrimesAbove p)) :
    quarticDiscriminantSign p J = archivedIdealCharacter J.val := by
  obtain ⟨r, hr, hJ⟩ := split_root_of_mem hp J.property
  obtain ⟨m, n, hm, hnorm, hzero⟩ := gaussian_split_generator_at_root hp r hr
  have hzNorm : (⟨m,n⟩ : GaussianInt).norm.natAbs = p := by
    rw [← Int.natAbs_natCast p, hnorm]
    congr 1
    simp only [Zsqrtd.norm_def]
    ring
  exact eq_archived_at_split_root (by omega) r hr J hJ ⟨m,n⟩ hzNorm hzero
    (archivedGaussianSign_at_split_root hp hcop r hr ⟨m,n⟩ hm hnorm hzero)

private theorem coprime_conductor {p : ℕ} (hp : p.Prime)
    (h₁ : p ≠ 41) (h₂ : p ≠ 457) (h₃ : p ≠ 1414835497) : p.Coprime 26509772707289 := by
  apply hp.coprime_iff_not_dvd.mpr
  rw [show (26509772707289 : ℕ) = 41*457*1414835497 by decide,
    hp.dvd_mul, hp.dvd_mul, Nat.prime_dvd_prime_iff_eq hp (Fact.out : Nat.Prime 41),
    Nat.prime_dvd_prime_iff_eq hp (Fact.out : Nat.Prime 457),
    Nat.prime_dvd_prime_iff_eq hp (Fact.out : Nat.Prime 1414835497)]
  simp [h₁,h₂,h₃]

private theorem eq_archived_at_41 (J : ↥(gaussianPrimesAbove 41)) :
    quarticDiscriminantSign 41 J = archivedIdealCharacter J.val :=
  eq_archived_at_split_pair (p := 41) (by decide) 32 (by decide) (by decide) J
    ⟨4,5⟩ ⟨4,-5⟩ (by decide) (by decide) (by decide) (by decide)
    conductor_prime_41_signs.1 conductor_prime_41_signs.2

private theorem eq_archived_at_457 (J : ↥(gaussianPrimesAbove 457)) :
    quarticDiscriminantSign 457 J = archivedIdealCharacter J.val :=
  eq_archived_at_split_pair (p := 457) (by decide) 109 (by decide) (by decide) J
    ⟨4,-21⟩ ⟨4,21⟩ (by decide) (by decide) (by decide) (by decide)
    conductor_prime_457_signs.1 conductor_prime_457_signs.2

set_option maxRecDepth 60000 in
private theorem eq_archived_at_1414835497 (J : ↥(gaussianPrimesAbove 1414835497)) :
    quarticDiscriminantSign 1414835497 J = archivedIdealCharacter J.val :=
  eq_archived_at_split_pair (p := 1414835497) (by decide) 516876951 (by decide) (by decide) J
    ⟨10596,-36091⟩ ⟨10596,36091⟩ (by decide) (by decide) (by decide) (by decide)
    conductor_prime_1414835497_signs.1 conductor_prime_1414835497_signs.2

/-- The sign comparison holds at each prime ideal, including the three
exceptional conductor primes, with the actual residue map of that ideal. -/
theorem quarticDiscriminantSign_eq_archivedIdealCharacter (p : ℕ) [Fact p.Prime]
    (J : ↥(gaussianPrimesAbove p)) :
    quarticDiscriminantSign p J = archivedIdealCharacter J.val := by
  by_cases hp₂ : p = 2
  · subst p
    have hI {I : Ideal GaussianInt} (h : I ∈ gaussianPrimesAbove 2) :
        I = Ideal.span {(⟨1,1⟩ : GaussianInt)} := by
      simpa only [dyadic_gaussian_prime, Finset.mem_singleton] using h
    rw [quarticDiscriminantSign_dyadic, hI J.property, archivedIdealCharacter_span]
  · have ho := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp₂
    by_cases hp₃ : p % 4 = 3
    · rw [quarticDiscriminantSign_inert p hp₃ J, eq_inert_gaussian_prime hp₃ J.property,
        archivedIdealCharacter_span]
    · have hp₁ : p % 4 = 1 := by omega
      by_cases h₁ : p = 41
      · subst p
        exact eq_archived_at_41 J
      by_cases h₂ : p = 457
      · subst p
        exact eq_archived_at_457 J
      by_cases h₃ : p = 1414835497
      · subst p
        exact eq_archived_at_1414835497 J
      exact eq_archived_at_split_coprime hp₁ (coprime_conductor Fact.out h₁ h₂ h₃) J

local notation "T" => (PowerSeries.X : PowerSeries ℂ)

theorem fieldLocalEulerSeries_mul_archived_denominators (p : ℕ) [Fact p.Prime] :
    fieldLocalEulerSeries K p *
      (((1-T)*(1-(ZMod.χ₄ (p : ZMod 4) : PowerSeries ℂ)*T)) *
        ∏ I : ↥(gaussianPrimesAbove p), (1-(archivedIdealCharacter I.val : PowerSeries ℂ)*T^(I.val.inertiaDeg ℤ))) = 1 := by
  simpa only [quarticDiscriminantSign_eq_archivedIdealCharacter] using
    fieldLocalEulerSeries_mul_character_denominators p

#print axioms quarticDiscriminantSign_eq_archivedIdealCharacter
#print axioms fieldLocalEulerSeries_mul_archived_denominators

end QuarticModel
