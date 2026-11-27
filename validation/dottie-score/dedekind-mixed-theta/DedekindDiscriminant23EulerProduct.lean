import DedekindDiscriminant23Hilbert
import DedekindZetaZeroFree.LFunctions.Dedekind.EulerProductRegrouping
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace FieldTarget

open scoped NumberField BigOperators nonZeroDivisors
open NumberField IsDedekindDomain ClassFieldTheory
open DedekindZetaZeroFree.AbelianQuotient

noncomputable section

local notation "F" => (discriminant23QuadraticSubfield : Type)
local notation "L23" => Discriminant23GaloisField

private def discriminant23ClassEquivRoots : ClassGroup (𝓞 F) ≃* rootsOfUnity 3 ℂ := by
  let : Fact (Nat.Prime 3) := ⟨by decide +kernel⟩
  apply mulEquivOfPrimeCardEq (p := 3)
  · rw [Nat.card_eq_fintype_card, ← NumberField.classNumber, discriminant23_class_number]
  · exact Complex.card_rootsOfUnity 3

/-- A faithful complex character of the ideal class group of the quadratic field. -/
def discriminant23ClassCharacter : ClassGroup (𝓞 F) →* ℂ :=
  (Units.coeHom ℂ).comp ((rootsOfUnity 3 ℂ).subtype.comp
    discriminant23ClassEquivRoots.toMonoidHom)

private theorem discriminant23ClassCharacter_injective :
    Function.Injective discriminant23ClassCharacter :=
  Units.val_injective.comp (Subtype.val_injective.comp discriminant23ClassEquivRoots.injective)

private theorem discriminant23ClassCharacter_cube (g : ClassGroup (𝓞 F)) :
    discriminant23ClassCharacter g ^ 3 = 1 := by
  rw [← discriminant23_class_number, ← map_pow]
  exact congrArg discriminant23ClassCharacter (pow_card_eq_one (x := g)) |>.trans
    (map_one discriminant23ClassCharacter)

/-- The (k)-th power of the class character, extended by zero at the zero ideal. -/
def discriminant23ClassWeight (k : ℕ) (I : Ideal (𝓞 F)) : ℂ := by
  classical
  exact if hI : I ≠ ⊥ then
    discriminant23ClassCharacter (ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩) ^ k
  else 0

private theorem discriminant23ClassWeight_mul (k : ℕ) (I J : Ideal (𝓞 F)) :
    discriminant23ClassWeight k (I * J) =
      discriminant23ClassWeight k I * discriminant23ClassWeight k J := by
  by_cases hI : I = ⊥
  · subst I
    simp [discriminant23ClassWeight]
  by_cases hJ : J = ⊥
  · subst J
    simp [discriminant23ClassWeight]
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  have hProd : (⟨I * J, mem_nonZeroDivisors_of_ne_zero hIJ⟩ : (Ideal (𝓞 F))⁰) =
      (⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 F))⁰) *
        ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩ := rfl
  simp only [discriminant23ClassWeight, dite_eq_left hI, dite_eq_left hJ, dite_eq_left hIJ, hProd,
    map_mul, mul_pow]

private theorem discriminant23ClassWeight_top (k : ℕ) :
    discriminant23ClassWeight k ⊤ = 1 := by
  have h : (⟨⊤, mem_nonZeroDivisors_of_ne_zero (top_ne_bot : (⊤ : Ideal (𝓞 F)) ≠ ⊥)⟩ :
      (Ideal (𝓞 F))⁰) = 1 := Subtype.ext Ideal.one_eq_top.symm
  simp [discriminant23ClassWeight, h]

private theorem discriminant23ClassWeight_bot (k : ℕ) :
    discriminant23ClassWeight k ⊥ = 0 := by
  simp [discriminant23ClassWeight]

private theorem discriminant23ClassWeight_norm_le (k : ℕ) (I : Ideal (𝓞 F)) :
    ‖discriminant23ClassWeight k I‖ ≤ 1 := by
  by_cases hI : I = ⊥
  · simp [hI, discriminant23ClassWeight_bot]
  · rw [discriminant23ClassWeight, dite_eq_left hI, norm_pow,
      Complex.norm_eq_one_of_pow_eq_one (discriminant23ClassCharacter_cube _) (by decide), one_pow]

private theorem discriminant23ClassWeight_prime (k : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) :
    discriminant23ClassWeight k v.asIdeal =
      discriminant23ClassCharacter (ClassGroup.mk F (finitePrimeFractionalIdeal v)) ^ k := by
  rw [discriminant23ClassWeight, dite_eq_left v.ne_bot, ← ClassGroup.mk_mk0 F]
  rfl

private theorem cubicRootFactorization {u : ℂ} (hCube : u ^ 3 = 1) (hNe : u ≠ 1)
    (x : ℂ) : (1 - x) * (1 - u * x) * (1 - u ^ 2 * x) = 1 - x ^ 3 := by
  have hSum : u ^ 2 + u + 1 = 0 := by
    have hProd : (u - 1) * (u ^ 2 + u + 1) = 0 := by linear_combination hCube
    exact (mul_eq_zero.mp hProd).resolve_left (sub_ne_zero.mpr hNe)
  linear_combination (x ^ 2 - x) * hSum + (x ^ 2 - x ^ 3) * hCube

/-- The actual finite Euler denominator above each base prime is the product
of the trivial, character and squared-character denominators. -/
theorem discriminant23_relative_eulerDenominator
    (v : HeightOneSpectrum (𝓞 F)) (w : ℂ) :
    (∏ Q ∈ IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L23),
      (1 - (Ideal.absNorm Q : ℂ) ^ (-w))) =
      (1 - (v.asIdeal.absNorm : ℂ) ^ (-w)) *
        (1 - discriminant23ClassWeight 1 v.asIdeal * (v.asIdeal.absNorm : ℂ) ^ (-w)) *
        (1 - discriminant23ClassWeight 2 v.asIdeal * (v.asIdeal.absNorm : ℂ) ^ (-w)) := by
  classical
  let S := IsDedekindDomain.primesOverFinset v.asIdeal (𝓞 L23)
  let x := (v.asIdeal.absNorm : ℂ) ^ (-w)
  let g := ClassGroup.mk F (finitePrimeFractionalIdeal v)
  let u := discriminant23ClassCharacter g
  let d := orderOf g
  let toSpectrum (Q : v.asIdeal.primesOver (𝓞 L23)) : HeightOneSpectrum (𝓞 L23) :=
    ⟨Q.val, Q.property.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.property⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 L23)))
  have hCard : S.card * d = 3 := by
    have h : (toSpectrum P).asIdeal.inertiaDeg (𝓞 F) = d :=
      discriminant23_relative_residue_degree_eq_class_order v (toSpectrum P) P.property.2
    rw [← h]
    exact discriminant23_relative_prime_count_mul_residue_degree v (toSpectrum P) P.property.2
  have hFactors : (∏ Q ∈ S, (1 - (Ideal.absNorm Q : ℂ) ^ (-w))) =
      (1 - x ^ d) ^ S.card := by
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro Q hQ
    have hOver := (IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot (𝓞 L23)).mp hQ
    refine congrArg (fun y : ℂ ↦ 1 - y) ?_
    have hdQ : Q.inertiaDeg (𝓞 F) = d :=
      discriminant23_relative_residue_degree_eq_class_order v (toSpectrum ⟨Q, hOver⟩) hOver.2
    let : Q.IsPrime := hOver.1
    let : Q.LiesOver v.asIdeal := hOver.2
    rw [← hdQ]
    symm
    dsimp [x]
    rw [← Complex.cpow_nat_mul, Complex.natCast_cpow_natCast_mul, ← Nat.cast_pow,
      Ideal.absNorm_pow_inertiaDeg (p := v.asIdeal) (q := Q)]
  change (∏ Q ∈ S, (1 - (Ideal.absNorm Q : ℂ) ^ (-w))) =
    (1 - x) * (1 - discriminant23ClassWeight 1 v.asIdeal * x) *
      (1 - discriminant23ClassWeight 2 v.asIdeal * x)
  rw [hFactors, discriminant23ClassWeight_prime, discriminant23ClassWeight_prime]
  change (1 - x ^ d) ^ S.card = (1 - x) * (1 - u ^ 1 * x) * (1 - u ^ 2 * x)
  by_cases hg : g = 1
  · have hd : d = 1 := orderOf_eq_one_iff.mpr hg
    have hu : u = 1 := by simp [u, hg]
    have hS : S.card = 3 := by simpa [hd] using hCard
    rw [hd, hS, hu]
    ring
  · have hd : d ≠ 1 := fun h ↦ hg (orderOf_eq_one_iff.mp h)
    have hD : d = 3 := ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp
      ⟨S.card, by simpa only [Nat.mul_comm] using hCard.symm⟩).resolve_left hd
    have hS : S.card = 1 := by
      rw [hD] at hCard
      omega
    have hu : u ≠ 1 := by
      intro h
      apply hg
      apply discriminant23ClassCharacter_injective
      simpa [u] using h
    rw [hD, hS, pow_one, pow_one]
    exact (cubicRootFactorization (discriminant23ClassCharacter_cube g) hu x).symm

/-- The weighted Dirichlet series of integral ideals in the quadratic base. -/
def discriminant23ClassSeries (k : ℕ) (w : ℂ) : ℂ :=
  ∑' I : Ideal (𝓞 F), discriminant23ClassWeight k I * (Ideal.absNorm I : ℂ) ^ (-w)

/-- On the domain of absolute convergence the genuine degree-six Dedekind
zeta is the product of the base zeta and the two class-character series. -/
theorem discriminant23_dedekindZeta_eq_classSeries {w : ℂ} (hw : 1 < w.re) :
    dedekindZeta L23 w = dedekindZeta F w *
      discriminant23ClassSeries 1 w * discriminant23ClassSeries 2 w := by
  let hBase := dedekindZeta_idealEulerProduct_hasProd F w hw
  have hChar (k : ℕ) := weightedIdealEulerProduct_hasProd F (discriminant23ClassWeight k)
    (discriminant23ClassWeight_mul k) (discriminant23ClassWeight_top k)
    (discriminant23ClassWeight_bot k) (discriminant23ClassWeight_norm_le k) w hw
  apply (primeEulerRegroup F L23 w hw).unique
  refine ((hBase.mul (hChar 1)).mul (hChar 2)).congr_fun ?_
  intro v
  rw [Finset.prod_inv_distrib, discriminant23_relative_eulerDenominator, mul_inv, mul_inv]

#check @discriminant23_relative_eulerDenominator
#check @discriminant23_dedekindZeta_eq_classSeries
#print axioms discriminant23ClassCharacter
#print axioms discriminant23_relative_eulerDenominator
#print axioms discriminant23_dedekindZeta_eq_classSeries

end
end FieldTarget
