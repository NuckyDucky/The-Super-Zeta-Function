import QuarticEulerFactorization

/-! The local Euler factor with the two Gaussian prime addresses retained.
The three conductor primes are unconditional specializations. -/

namespace QuarticModel

open FieldCoefficientTransfer
open scoped Classical

attribute [local instance] Ideal.Quotient.field

theorem quarticDiscriminantSign_split {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) (J : ↥(gaussianPrimesAbove p))
    (hJ : J.val = gaussianPrimeAt r hr) :
    quarticDiscriminantSign p J = quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708*r) := by
  obtain ⟨I, hI⟩ := J
  change I = gaussianPrimeAt r hr at hJ
  subst I
  let I := gaussianPrimeAt r hr
  let : I.IsMaximal := gaussianPrimesAbove_isMaximal hI
  let : Finite (GaussianInt ⧸ I) := gaussian_finiteQuotient I (gaussianPrimesAbove_ne_bot hI)
  let : Fintype (GaussianInt ⧸ I) := Fintype.ofFinite _
  let e := gaussianPrimeAtResidueEquiv r hr
  have h₂ : (2 : GaussianInt ⧸ I) ≠ 0 := by
    intro h
    have he := congrArg e h
    rw [map_ofNat, map_zero] at he
    exact Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n]) he
  have hχ := (quadraticChar_ringEquiv e (Ideal.Quotient.mk I gaussianDiscriminant)).symm
  have hD : e (Ideal.Quotient.mk I gaussianDiscriminant) =
      (-5045155 : ZMod p) + 1027708*r := gaussianResidue_discriminant r hr
  rw [hD] at hχ
  simpa only [quarticDiscriminantSign, if_neg h₂] using hχ

theorem fieldLocalEulerSeries_mul_archived_split_denominator (p : ℕ) [Fact p.Prime]
    (hp : p % 4 = 1) (r : ZMod p) (hr : r^2 = -1) (zPos zNeg : GaussianInt)
    (hPos : quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708*r) = archivedGaussianSign zPos)
    (hNeg : quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708*(-r)) = archivedGaussianSign zNeg) :
    let T := (PowerSeries.X : PowerSeries ℂ)
    fieldLocalEulerSeries K p * ((1-T)^2 *
      ((1-(archivedGaussianSign zPos : PowerSeries ℂ)*T)*(1-(archivedGaussianSign zNeg : PowerSeries ℂ)*T))) = 1 := by
  let T := (PowerSeries.X : PowerSeries ℂ)
  have hp₂ : p ≠ 2 := by omega
  have hn : (-r)^2 = -1 := by simpa only [neg_sq] using hr
  let IPos := gaussianPrimeAt r hr
  let INeg := gaussianPrimeAt (-r) hn
  have hs : gaussianPrimesAbove p = {IPos, INeg} := split_gaussian_primes hp₂ r hr hn
  have hne : IPos ≠ INeg := gaussianPrimeAt_distinct hp₂ r hr
  have hmPos : IPos ∈ gaussianPrimesAbove p := by simp [hs]
  have hmNeg : INeg ∈ gaussianPrimesAbove p := by simp [hs]
  let markedSign (I : Ideal GaussianInt) := if I = IPos then archivedGaussianSign zPos else archivedGaussianSign zNeg
  have hf (J : ↥(gaussianPrimesAbove p)) : quarticDiscriminantSign p J = markedSign J.val := by
    have hcases : J.val = IPos ∨ J.val = INeg := by
      have hh {I : Ideal GaussianInt} (hI : I ∈ gaussianPrimesAbove p) : I ∈ ({IPos, INeg} : Finset _) := hs ▸ hI
      simpa using hh J.property
    rcases hcases with hJ | hJ
    · rw [quarticDiscriminantSign_split hp₂ r hr J hJ, hPos, hJ]
      simp [markedSign]
    · rw [quarticDiscriminantSign_split hp₂ (-r) hn J hJ, hNeg, hJ]
      simp [markedSign, hne.symm]
  have hc := fieldLocalEulerSeries_mul_character_denominators p
  simp_rw [hf] at hc
  rw [Finset.prod_coe_sort (gaussianPrimesAbove p)
      (fun I => 1-(markedSign I : PowerSeries ℂ)*T^(I.inertiaDeg ℤ)), hs,
    Finset.prod_insert (by simpa only [Finset.mem_singleton] using hne), Finset.prod_singleton,
    primeAt_degree r hr hmPos, primeAt_degree (-r) hn hmNeg, ZMod.χ₄_nat_one_mod_four hp] at hc
  simpa only [markedSign, if_pos rfl, if_neg hne.symm, pow_one, Int.cast_one, one_mul, pow_two] using hc

local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

local notation "T" => (PowerSeries.X : PowerSeries ℂ)

theorem fieldLocalEulerSeries_mul_conductor_41_denominator :
    fieldLocalEulerSeries K 41 * ((1-T)^2 *
      ((1-(archivedGaussianSign ⟨4,5⟩ : PowerSeries ℂ)*T)*(1-(archivedGaussianSign ⟨4,-5⟩ : PowerSeries ℂ)*T))) = 1 :=
  fieldLocalEulerSeries_mul_archived_split_denominator 41 (by decide) 32 (by decide) _ _
    conductor_prime_41_signs.1 conductor_prime_41_signs.2

theorem fieldLocalEulerSeries_mul_conductor_457_denominator :
    fieldLocalEulerSeries K 457 * ((1-T)^2 *
      ((1-(archivedGaussianSign ⟨4,-21⟩ : PowerSeries ℂ)*T)*(1-(archivedGaussianSign ⟨4,21⟩ : PowerSeries ℂ)*T))) = 1 :=
  fieldLocalEulerSeries_mul_archived_split_denominator 457 (by decide) 109 (by decide) _ _
    conductor_prime_457_signs.1 conductor_prime_457_signs.2

set_option maxRecDepth 60000 in
theorem fieldLocalEulerSeries_mul_conductor_1414835497_denominator :
    fieldLocalEulerSeries K 1414835497 * ((1-T)^2 *
      ((1-(archivedGaussianSign ⟨10596,-36091⟩ : PowerSeries ℂ)*T)*
        (1-(archivedGaussianSign ⟨10596,36091⟩ : PowerSeries ℂ)*T))) = 1 :=
  fieldLocalEulerSeries_mul_archived_split_denominator 1414835497 (by decide) 516876951 (by decide) _ _
    conductor_prime_1414835497_signs.1 conductor_prime_1414835497_signs.2

#print axioms quarticDiscriminantSign_split
#print axioms fieldLocalEulerSeries_mul_archived_split_denominator
#print axioms fieldLocalEulerSeries_mul_conductor_41_denominator
#print axioms fieldLocalEulerSeries_mul_conductor_457_denominator
#print axioms fieldLocalEulerSeries_mul_conductor_1414835497_denominator

end QuarticModel
