import RelativeQuarticPrimeNorms
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! The exact factorization types of reductions of the relative quadratic. -/

namespace QuarticModel

open NumberField Polynomial UniqueFactorizationMonoid
open scoped Classical

private noncomputable def quadratic {F : Type*} [Field F] (c : F) : F[X] :=
  X^2 - X + C c

private theorem quadratic_monic {F : Type*} [Field F] (c : F) : (quadratic c).Monic := by
  unfold quadratic
  monicity!

private theorem quadratic_natDegree {F : Type*} [Field F] (c : F) :
    (quadratic c).natDegree = 2 := by
  unfold quadratic
  compute_degree!

private theorem root_iff_discriminant {F : Type*} [Field F] (h₂ : (2 : F) ≠ 0) (c x : F) :
    IsRoot (quadratic c) x ↔ (2*x-1)^2 = 1-4*c := by
  unfold IsRoot quadratic
  simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C]
  have h₄ : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2*2 by ring]
    exact mul_ne_zero h₂ h₂
  constructor
  · intro h
    linear_combination 4*h
  · intro h
    have he : 4*(x^2-x+c) = 0 := by linear_combination h
    exact (mul_eq_zero.mp he).resolve_left h₄

private theorem quadratic_factors_of_square {F : Type*} [Field F] (h₂ : (2 : F) ≠ 0)
    (c d : F) (hd : d^2 = 1-4*c) :
    quadratic c = (X - C ((1+d)/2)) * (X - C ((1-d)/2)) := by
  let r := (1+d)/2
  let s := (1-d)/2
  have hr : r+s=1 := by dsimp [r, s]; field_simp; ring
  have hp : r*s=c := by
    dsimp [r, s]
    field_simp
    linear_combination -hd
  change quadratic c = (X - C r) * (X - C s)
  calc
    _ = X^2 - C (r+s) * X + C (r*s) := by rw [hr, hp, map_one, one_mul]; rfl
    _ = _ := by rw [map_add, map_mul]; ring

private theorem normalized_linear_product {F : Type*} [Field F] (r s : F) :
    normalizedFactors ((X-C r)*(X-C s)) = {X-C r} + {X-C s} := by
  rw [normalizedFactors_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    normalizedFactors_irreducible (irreducible_X_sub_C _),
    normalizedFactors_irreducible (irreducible_X_sub_C _),
    (normalize_eq_self_iff_monic (X_sub_C_ne_zero _)).mpr (monic_X_sub_C _),
    (normalize_eq_self_iff_monic (X_sub_C_ne_zero _)).mpr (monic_X_sub_C _)]

private theorem normalized_quadratic_of_square {F : Type*} [Field F] (h₂ : (2 : F) ≠ 0)
    (c d : F) (hd : d^2 = 1-4*c) :
    normalizedFactors (quadratic c) =
      {X - C ((1+d)/2)} + {X - C ((1-d)/2)} := by
  rw [quadratic_factors_of_square h₂ c d hd, normalized_linear_product]

private theorem normalized_quadratic_of_nonsquare {F : Type*} [Field F] (h₂ : (2 : F) ≠ 0)
    (c : F) (hc : ¬ IsSquare (1-4*c)) : normalizedFactors (quadratic c) = {quadratic c} := by
  have hi : Irreducible (quadratic c) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · simp [quadratic_natDegree]
    · intro x hx
      have h := (root_iff_discriminant h₂ c x).mp hx
      exact hc ⟨2*x-1, by rw [← pow_two, h]⟩
  rw [normalizedFactors_irreducible hi,
    (normalize_eq_self_iff_monic (quadratic_monic c).ne_zero).mpr (quadratic_monic c)]

private theorem distinct_linear_factors {F : Type*} [Field F] (h₂ : (2 : F) ≠ 0)
    {d : F} (hd₀ : d ≠ 0) :
    (X : F[X])-C ((1+d)/2) ≠ X-C ((1-d)/2) := by
  have hrs : (1+d)/2 ≠ (1-d)/2 := by
    intro h
    have hh := congrArg (fun x : F => x*2) h
    simp only [div_mul_cancel₀ _ h₂] at hh
    exact (mul_ne_zero h₂ hd₀) (by linear_combination hh)
  intro h
  have he := congrArg (fun f : F[X] => f.eval ((1+d)/2)) h
  exact hrs (sub_eq_zero.mp (by simpa using he.symm))

/-- The number of distinct factors followed by the total multiplicity. -/
def factorCounts {A : Type*} [DecidableEq A] (f : Multiset A) : ℕ × ℕ :=
  (f.toFinset.card, f.card)

private theorem quadratic_factorCounts {F : Type*} [Field F] [Fintype F]
    (h₂ : (2 : F) ≠ 0) (c : F) :
    factorCounts (normalizedFactors (quadratic c)) =
      if quadraticChar F (1-4*c) = 0 then (1,2)
      else if quadraticChar F (1-4*c) = 1 then (2,2)
      else (1,1) := by
  by_cases h₀ : 1-4*c = 0
  · have hd : (0 : F)^2 = 1-4*c := by rw [h₀, zero_pow (by decide : 2 ≠ 0)]
    rw [normalized_quadratic_of_square h₂ c 0 hd, if_pos (quadraticChar_eq_zero_iff.mpr h₀)]
    simp [factorCounts]
  · rw [if_neg (mt quadraticChar_eq_zero_iff.mp h₀)]
    by_cases hs : IsSquare (1-4*c)
    · rw [if_pos ((quadraticChar_one_iff_isSquare h₀).mpr hs)]
      obtain ⟨d, hd⟩ := hs
      have hds : d^2 = 1-4*c := by rw [pow_two, hd]
      rw [normalized_quadratic_of_square h₂ c d hds]
      have hd₀ : d ≠ 0 := fun h => h₀ (by simpa [h] using hds.symm)
      simp [factorCounts, distinct_linear_factors h₂ hd₀]
    · rw [if_neg (mt (quadraticChar_one_iff_isSquare h₀).mp hs),
        normalized_quadratic_of_nonsquare h₂ c hs]
      simp [factorCounts]

attribute [local instance] Ideal.Quotient.field

private theorem reduce_polynomial (I : Ideal GaussianInt) [I.IsMaximal] :
    relativePolynomial.map (Ideal.Quotient.mk I) =
      quadratic (Ideal.Quotient.mk I (⟨1261289, -256927⟩ : GaussianInt)) := by
  simp only [relativePolynomial, quadratic, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_pow, map_X, map_C]

private theorem quartic_factorCounts (I : Ideal GaussianInt) [hI : I.IsMaximal] (hI' : I ≠ ⊥) :
    factorCounts (normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))) =
      factorCounts (normalizedFactors (relativePolynomial.map (Ideal.Quotient.mk I))) := by
  let L := normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))
  let R := normalizedFactors (relativePolynomial.map (Ideal.Quotient.mk I))
  have hL : ∀ J, J ∈ L.toFinset ↔ J ∈ L := fun _ => Multiset.mem_toFinset
  have hR : ∀ q, q ∈ R.toFinset ↔ q ∈ R := fun _ => Multiset.mem_toFinset
  let : Fintype {J // J ∈ L} := Fintype.ofFinset L.toFinset hL
  let : Fintype {q // q ∈ R} := Fintype.ofFinset R.toFinset hR
  apply Prod.ext
  · change L.toFinset.card = R.toFinset.card
    calc
      L.toFinset.card = Fintype.card {J // J ∈ L} := (Fintype.card_ofFinset L.toFinset hL).symm
      _ = Fintype.card {q // q ∈ R} := Fintype.card_congr (quarticPrimeFactorEquiv I hI')
      _ = R.toFinset.card := Fintype.card_ofFinset R.toFinset hR
  · have hcon : (conductor GaussianInt thetaHalf).comap (algebraMap GaussianInt (𝓞 K)) ⊔ I = ⊤ := by
      rw [conductor_eq_top_of_adjoin_eq_top gaussian_adjoin_thetaHalf_eq_top, Ideal.comap_top, top_sup_eq]
    have h := KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map
      hI hI' hcon thetaHalf_integral_gaussian
    have hc := congrArg Multiset.card h
    rw [Multiset.card_map, Multiset.card_attach, thetaHalf_minpoly_gaussian] at hc
    exact hc

/-- The first coordinate counts distinct primes and the second counts them
with their multiplicities. The sign is the quadratic character of the
discriminant in the residue field at the actual Gaussian prime. -/
theorem quartic_odd_prime_counts (I : Ideal GaussianInt) [I.IsMaximal] (hI : I ≠ ⊥)
    [Fintype (GaussianInt ⧸ I)] (h₂ : (2 : GaussianInt ⧸ I) ≠ 0) :
    factorCounts (normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))) =
      if quadraticChar (GaussianInt ⧸ I) (Ideal.Quotient.mk I gaussianDiscriminant) = 0 then (1,2)
      else if quadraticChar (GaussianInt ⧸ I) (Ideal.Quotient.mk I gaussianDiscriminant) = 1 then (2,2)
      else (1,1) := by
  rw [quartic_factorCounts I hI, reduce_polynomial]
  rw [quadratic_factorCounts h₂]
  have h := congrArg (Ideal.Quotient.mk I) relative_discriminant
  rw [map_sub, map_one, map_mul, map_ofNat] at h
  rw [h]

private theorem constant_zero_at_two {F : Type*} [Field F] (f : GaussianInt →+* F)
    (h₂ : (2 : F) = 0) : f ⟨1261289, -256927⟩ = 0 := by
  let j : GaussianInt := ⟨0, 1⟩
  have hj : (f j)^2 = -1 := by
    rw [← map_pow, show j^2 = -1 by decide, map_neg, map_one]
  have hsq : (f j - 1)^2 = 0 := by
    linear_combination hj - (f j)*h₂
  have hj' : f j = 1 := by
    rw [pow_two, mul_eq_zero, or_self] at hsq
    exact sub_eq_zero.mp hsq
  have hconst : (⟨1261289, -256927⟩ : GaussianInt) =
      (1261289 : GaussianInt) + ((-256927 : ℤ) : GaussianInt) * j := by decide
  rw [hconst, map_add, map_mul, map_ofNat, map_intCast, hj', mul_one]
  push_cast
  linear_combination (502181 : F)*h₂

/-- The dyadic Gaussian prime splits into two distinct factors. -/
theorem quartic_even_prime_counts (I : Ideal GaussianInt) [I.IsMaximal] (hI : I ≠ ⊥)
    (h₂ : (2 : GaussianInt ⧸ I) = 0) :
    factorCounts (normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))) = (2,2) := by
  rw [quartic_factorCounts I hI, reduce_polynomial, constant_zero_at_two _ h₂]
  have hsplit : quadratic (0 : GaussianInt ⧸ I) = (X-C 0)*(X-C 1) := by
    simp only [quadratic, map_zero, map_one, sub_zero, add_zero]
    ring
  rw [hsplit, normalized_linear_product]
  have hlin : (X : (GaussianInt ⧸ I)[X]) ≠ X-1 := by
    intro h
    have he := congrArg (fun f : (GaussianInt ⧸ I)[X] => f.eval 0) h
    simp at he
  simp [factorCounts, hlin]

/-- One factor per distinct quartic prime above `I`. The variable stands
for the Gaussian ideal norm raised to the negative spectral variable. -/
noncomputable def quarticEulerDenominator (I : Ideal GaussianInt) : ℤ[X] :=
  ∏ J ∈ (normalizedFactors (I.map (algebraMap GaussianInt (𝓞 K)))).toFinset,
    (1 - X^(J.inertiaDeg GaussianInt))

private theorem quadratic_euler_denominator {F : Type*} [Field F] [Fintype F]
    (h₂ : (2 : F) ≠ 0) (c : F) :
    (∏ f ∈ (normalizedFactors (quadratic c)).toFinset, (1 - (X : ℤ[X])^f.natDegree)) =
      (1-X)*(1-C (quadraticChar F (1-4*c))*X) := by
  by_cases h₀ : 1-4*c = 0
  · have hd : (0 : F)^2 = 1-4*c := by rw [h₀, zero_pow (by decide : 2 ≠ 0)]
    rw [normalized_quadratic_of_square h₂ c 0 hd, quadraticChar_eq_zero_iff.mpr h₀]
    simp
  · by_cases hs : IsSquare (1-4*c)
    · rw [(quadraticChar_one_iff_isSquare h₀).mpr hs]
      obtain ⟨d, hd⟩ := hs
      have hds : d^2 = 1-4*c := by rw [pow_two, hd]
      have hd₀ : d ≠ 0 := fun h => h₀ (by simpa [h] using hds.symm)
      have hlin := distinct_linear_factors h₂ hd₀
      rw [normalized_quadratic_of_square h₂ c d hds, Multiset.toFinset_add,
        Multiset.toFinset_singleton, Multiset.toFinset_singleton, Finset.singleton_union,
        Finset.prod_insert (by simpa only [Finset.mem_singleton] using hlin), Finset.prod_singleton]
      simp
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hs, normalized_quadratic_of_nonsquare h₂ c hs]
      simp only [Multiset.toFinset_singleton, Finset.prod_singleton, quadratic_natDegree,
        map_neg, map_one, neg_one_mul, sub_neg_eq_add]
      ring

/-- The actual local reciprocal Euler factor at every odd Gaussian prime. -/
theorem quartic_odd_euler_denominator (I : Ideal GaussianInt) [I.IsMaximal] (hI : I ≠ ⊥)
    [Fintype (GaussianInt ⧸ I)] (h₂ : (2 : GaussianInt ⧸ I) ≠ 0) :
    quarticEulerDenominator I =
      (1-X)*(1-C (quadraticChar (GaussianInt ⧸ I) (Ideal.Quotient.mk I gaussianDiscriminant))*X) := by
  unfold quarticEulerDenominator
  rw [relative_product_inertiaDeg I hI (fun k => 1 - (X : ℤ[X])^k), reduce_polynomial,
    quadratic_euler_denominator h₂]
  have h := congrArg (Ideal.Quotient.mk I) relative_discriminant
  rw [map_sub, map_one, map_mul, map_ofNat] at h
  rw [h]

theorem quartic_even_euler_denominator (I : Ideal GaussianInt) [I.IsMaximal] (hI : I ≠ ⊥)
    (h₂ : (2 : GaussianInt ⧸ I) = 0) :
    quarticEulerDenominator I = (1-X)^2 := by
  unfold quarticEulerDenominator
  rw [relative_product_inertiaDeg I hI (fun k => 1 - (X : ℤ[X])^k), reduce_polynomial,
    constant_zero_at_two _ h₂]
  have hsplit : quadratic (0 : GaussianInt ⧸ I) = (X-C 0)*(X-C 1) := by
    simp only [quadratic, map_zero, map_one, sub_zero, add_zero]
    ring
  have hlin : (X : (GaussianInt ⧸ I)[X])-C 0 ≠ X-C 1 := by
    intro h
    have he := congrArg (fun f : (GaussianInt ⧸ I)[X] => f.eval 0) h
    simp at he
  rw [hsplit, normalized_linear_product, Multiset.toFinset_add,
    Multiset.toFinset_singleton, Multiset.toFinset_singleton, Finset.singleton_union,
    Finset.prod_insert (by simpa only [Finset.mem_singleton] using hlin), Finset.prod_singleton]
  rw [natDegree_X_sub_C, natDegree_X_sub_C, pow_one, pow_two]

#print axioms quartic_odd_prime_counts
#print axioms quartic_even_prime_counts
#print axioms quartic_odd_euler_denominator
#print axioms quartic_even_euler_denominator

end QuarticModel
