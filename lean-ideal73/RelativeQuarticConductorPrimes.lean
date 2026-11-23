import RelativeQuarticSplitPrimes
import RelativeQuarticPrimeNorms
import Mathlib.Tactic.NormNum.LegendreSymbol

/-! The three exceptional rational primes from the archived conductor
calculation, with their two exact Gaussian prime generators. -/

namespace QuarticModel

open NumberField UniqueFactorizationMonoid
open scoped Classical

/-- The three archived symbols, written as Jacobi symbols at the same
three prime denominators. -/
noncomputable def archivedGaussianSign (z : GaussianInt) : ℤ :=
  jacobiSym (z.re + z.im*32) 41 * jacobiSym (z.re + z.im*109) 457 *
    jacobiSym (z.re + z.im*516876951) 1414835497

local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

theorem archivedGaussianSign_eq_legendre (z : GaussianInt) :
    archivedGaussianSign z =
      legendreSym 41 (z.re+z.im*32) * legendreSym 457 (z.re+z.im*109) *
        legendreSym 1414835497 (z.re+z.im*516876951) := by
  simp only [archivedGaussianSign, jacobiSym.legendreSym.to_jacobiSym]

private theorem irreducible_of_prime_norm {p : ℕ} [Fact p.Prime] (z : GaussianInt)
    (hz : z.norm.natAbs = p) : Irreducible z := by
  have hp : p.Prime := Fact.out
  refine ⟨fun hu => hp.ne_one (hz.symm.trans (Zsqrtd.norm_eq_one_iff.mpr hu)), ?_⟩
  intro a b hab
  have h : a.norm.natAbs * b.norm.natAbs = p := by
    rw [← Int.natAbs_mul, ← Zsqrtd.norm_mul, ← hab, hz]
  rcases hp.eq_one_or_self_of_dvd _ ⟨b.norm.natAbs, h.symm⟩ with ha | ha
  · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp ha)
  · apply Or.inr
    apply Zsqrtd.norm_eq_one_iff.mp
    rw [ha] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (h.trans (Nat.mul_one p).symm)

theorem gaussianPrimeAt_eq_span {p : ℕ} [Fact p.Prime]
    (r : ZMod p) (hr : r^2 = -1) (z : GaussianInt) (hn : z.norm.natAbs = p)
    (hz : gaussianResidue r hr z = 0) :
    gaussianPrimeAt r hr = Ideal.span {z} := by
  have hp : Prime z := (irreducible_of_prime_norm z hn).prime
  have hm : (Ideal.span {z} : Ideal GaussianInt).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal_of_ne_bot
      (by simpa using hp.ne_zero)
  exact (hm.eq_of_le
    (RingHom.ker_isMaximal_of_surjective _ (ZMod.ringHom_surjective (gaussianResidue r hr))).ne_top
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (show z ∈ gaussianPrimeAt r hr from hz)))).symm

private noncomputable def quarticFactorsAt (z : GaussianInt) : ℕ × ℕ :=
  factorCounts (normalizedFactors ((Ideal.span {z}).map (algebraMap GaussianInt (𝓞 K))))

private theorem factorCounts_of_symbol {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) (z : GaussianInt)
    (hn : z.norm.natAbs = p) (hz : gaussianResidue r hr z = 0)
    (hχ : quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708*r) = archivedGaussianSign z) :
    quarticFactorsAt z =
      if archivedGaussianSign z = 0 then (1,2) else if archivedGaussianSign z = 1 then (2,2) else (1,1) := by
  have hcount := split_rational_prime_factor_counts hp r hr
  dsimp only at hcount
  rw [gaussianPrimeAt_eq_span r hr z hn hz, hχ] at hcount
  exact hcount

private theorem residue_discriminant_zero {p : ℕ} [Fact p.Prime]
    (r : ZMod p) (h : (-5045155 : ZMod p) + 1027708*r = 0) :
    quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708*r) = 0 :=
  quadraticChar_eq_zero_iff.mpr h

private theorem other_discriminant {p : ℕ} [Fact p.Prime] (r : ZMod p)
    (h : (-5045155 : ZMod p)+1027708*r = 0) :
    (-5045155 : ZMod p) + 1027708*(-r) = ((-10090310 : ℤ) : ZMod p) := by
  push_cast
  linear_combination -h

theorem conductor_prime_41_signs :
    quadraticChar (ZMod 41) ((-5045155 : ZMod 41)+1027708*32) = archivedGaussianSign ⟨4,5⟩ ∧
    quadraticChar (ZMod 41) ((-5045155 : ZMod 41)+1027708*(-32)) = archivedGaussianSign ⟨4,-5⟩ := by
  constructor
  · rw [residue_discriminant_zero 32 (by decide)]
    norm_num [archivedGaussianSign]
  · rw [other_discriminant 32 (by decide)]
    change legendreSym 41 (-10090310) = _
    norm_num [archivedGaussianSign]

theorem conductor_prime_457_signs :
    quadraticChar (ZMod 457) ((-5045155 : ZMod 457)+1027708*109) = archivedGaussianSign ⟨4,-21⟩ ∧
    quadraticChar (ZMod 457) ((-5045155 : ZMod 457)+1027708*(-109)) = archivedGaussianSign ⟨4,21⟩ := by
  constructor
  · rw [residue_discriminant_zero 109 (by decide)]
    norm_num [archivedGaussianSign]
  · rw [other_discriminant 109 (by decide)]
    change legendreSym 457 (-10090310) = _
    norm_num [archivedGaussianSign]

set_option maxRecDepth 60000 in
theorem conductor_prime_1414835497_signs :
    quadraticChar (ZMod 1414835497) ((-5045155 : ZMod 1414835497)+1027708*516876951) =
      archivedGaussianSign ⟨10596,-36091⟩ ∧
    quadraticChar (ZMod 1414835497) ((-5045155 : ZMod 1414835497)+1027708*(-516876951)) =
      archivedGaussianSign ⟨10596,36091⟩ := by
  constructor
  · rw [residue_discriminant_zero 516876951 (by decide)]
    norm_num [archivedGaussianSign]
  · rw [other_discriminant 516876951 (by decide)]
    change legendreSym 1414835497 (-10090310) = _
    norm_num [archivedGaussianSign]

theorem conductor_prime_41_counts :
    quarticFactorsAt ⟨4,5⟩ = (1,2) ∧ quarticFactorsAt ⟨4,-5⟩ = (2,2) := by
  constructor
  · rw [factorCounts_of_symbol (p := 41) (by decide) 32 (by decide) _ (by decide) (by decide)
      conductor_prime_41_signs.1]
    norm_num [archivedGaussianSign]
  · rw [factorCounts_of_symbol (p := 41) (by decide) (-32) (by decide) _ (by decide) (by decide)
      conductor_prime_41_signs.2]
    norm_num [archivedGaussianSign]

theorem conductor_prime_457_counts :
    quarticFactorsAt ⟨4,-21⟩ = (1,2) ∧ quarticFactorsAt ⟨4,21⟩ = (1,1) := by
  constructor
  · rw [factorCounts_of_symbol (p := 457) (by decide) 109 (by decide) _ (by decide) (by decide)
      conductor_prime_457_signs.1]
    norm_num [archivedGaussianSign]
  · rw [factorCounts_of_symbol (p := 457) (by decide) (-109) (by decide) _ (by decide) (by decide)
      conductor_prime_457_signs.2]
    norm_num [archivedGaussianSign]

set_option maxRecDepth 60000 in
theorem conductor_prime_1414835497_counts :
    quarticFactorsAt ⟨10596,-36091⟩ = (1,2) ∧ quarticFactorsAt ⟨10596,36091⟩ = (1,1) := by
  constructor
  · rw [factorCounts_of_symbol (p := 1414835497) (by decide) 516876951 (by decide) _ (by decide)
      (by decide) conductor_prime_1414835497_signs.1]
    norm_num [archivedGaussianSign]
  · rw [factorCounts_of_symbol (p := 1414835497) (by decide) (-516876951) (by decide) _ (by decide)
      (by decide) conductor_prime_1414835497_signs.2]
    norm_num [archivedGaussianSign]

#print axioms archivedGaussianSign_eq_legendre
#print axioms conductor_prime_41_counts
#print axioms conductor_prime_457_counts
#print axioms conductor_prime_1414835497_counts

end QuarticModel
