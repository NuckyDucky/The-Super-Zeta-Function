import QuarticAt73
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.RamificationInertia.Inertia

/-! The three actual prime ideals over 73 of the quartic field, their generators,
residue degrees, and absolute norms, from the proved good reduction. -/

noncomputable section
namespace PrimeDecomposition73

open NumberField Polynomial QuarticModel UniqueFactorizationMonoid

private instance : Fact (Nat.Prime 73) := ⟨by decide⟩

private abbrev red := Int.castRingHom (ZMod 73)
private abbrev q₁ : (ZMod 73)[X] := X - C 9
private abbrev q₂ : (ZMod 73)[X] := X - C 64
private abbrev q₃ : (ZMod 73)[X] := X^2 - C 34
private abbrev above := Ideal.primesOver (Ideal.span {(73:ℤ)}) (𝓞 K)
private abbrev primesEquiv := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod QuarticAt73.good_reduction

private theorem reduced_poly : (minpoly ℤ theta).map red = q₁*q₂*q₃ := by
  rw [minpoly_theta]
  simp only [QuarticCoefficient.sqrtDeltaPolynomial, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_ofNat, q₁, q₂, q₃, Polynomial.C_ofNat]
  have h : (73 : Polynomial (ZMod 73)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (Polynomial.C (R := ZMod 73)) (by decide : (73 : ZMod 73) = 0)
  linear_combination (X^3+138216*X^2-34*X+363147571601)*h

private theorem irr₃ : Irreducible q₃ := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Polynomial.natDegree_X_pow_sub_C]
    decide
  · intro x hx
    apply (by decide : ∀ t : ZMod 73, t^2 ≠ 34) x
    simpa [q₃, Polynomial.IsRoot, sub_eq_zero] using hx

private theorem factors : normalizedFactors ((minpoly ℤ theta).map red) =
    {q₁}+{q₂}+{q₃} := by
  have hi := Polynomial.irreducible_X_sub_C (9 : ZMod 73)
  have hj := Polynomial.irreducible_X_sub_C (64 : ZMod 73)
  rw [reduced_poly, normalizedFactors_mul (mul_ne_zero hi.ne_zero hj.ne_zero) irr₃.ne_zero,
    normalizedFactors_mul hi.ne_zero hj.ne_zero, normalizedFactors_irreducible hi,
    normalizedFactors_irreducible hj, normalizedFactors_irreducible irr₃,
    (monic_X_sub_C (9:ZMod 73)).normalize_eq_self,
    (monic_X_sub_C (64:ZMod 73)).normalize_eq_self,
    (monic_X_pow_sub_C (34:ZMod 73) (by decide : 2 ≠ 0)).normalize_eq_self]

private theorem mem_factors (q : (ZMod 73)[X]) :
    q ∈ RingOfIntegers.monicFactorsMod theta 73 ↔ q = q₁ ∨ q = q₂ ∨ q = q₃ := by
  change q ∈ (normalizedFactors ((minpoly ℤ theta).map red)).toFinset ↔ _
  simp [factors]

/-- The primes in the maximal order, specified by the two integer-generator relations. -/
def P₉ : Ideal (𝓞 K) := Ideal.span {(73 : 𝓞 K), theta-9}
def P₆₄ : Ideal (𝓞 K) := Ideal.span {(73 : 𝓞 K), theta-64}
def P₃₄ : Ideal (𝓞 K) := Ideal.span {(73 : 𝓞 K), theta^2-34}

private theorem identify (Q : ℤ[X]) (hq : Q.map red ∈ RingOfIntegers.monicFactorsMod theta 73) :
    (primesEquiv.symm ⟨Q.map red,hq⟩ : Ideal (𝓞 K)) = Ideal.span {(73 : 𝓞 K), aeval theta Q} :=
  NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span QuarticAt73.good_reduction hq

private theorem h₁ : q₁ ∈ RingOfIntegers.monicFactorsMod theta 73 := (mem_factors _).mpr (Or.inl rfl)
private theorem h₂ : q₂ ∈ RingOfIntegers.monicFactorsMod theta 73 := (mem_factors _).mpr (Or.inr (Or.inl rfl))
private theorem h₃ : q₃ ∈ RingOfIntegers.monicFactorsMod theta 73 := (mem_factors _).mpr (Or.inr (Or.inr rfl))

private theorem span₁ : (primesEquiv.symm ⟨q₁,h₁⟩ : Ideal (𝓞 K)) = P₉ := by
  have h : (X-9 : ℤ[X]).map red ∈ RingOfIntegers.monicFactorsMod theta 73 := by
    simpa only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_ofNat, q₁,
      Polynomial.C_ofNat] using h₁
  simpa only [P₉, q₁, Polynomial.C_ofNat, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_ofNat, map_sub, aeval_X, map_ofNat] using identify (X-9) h
private theorem span₂ : (primesEquiv.symm ⟨q₂,h₂⟩ : Ideal (𝓞 K)) = P₆₄ := by
  have h : (X-64 : ℤ[X]).map red ∈ RingOfIntegers.monicFactorsMod theta 73 := by
    simpa only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_ofNat, q₂,
      Polynomial.C_ofNat] using h₂
  simpa only [P₆₄, q₂, Polynomial.C_ofNat, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_ofNat, map_sub, aeval_X, map_ofNat] using identify (X-64) h
private theorem span₃ : (primesEquiv.symm ⟨q₃,h₃⟩ : Ideal (𝓞 K)) = P₃₄ := by
  have h : (X^2-34 : ℤ[X]).map red ∈ RingOfIntegers.monicFactorsMod theta 73 := by
    simpa only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_ofNat, q₃,
      Polynomial.C_ofNat] using h₃
  simpa only [P₃₄, q₃, Polynomial.C_ofNat, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_pow, Polynomial.map_ofNat, map_sub, map_pow, aeval_X, map_ofNat]
    using identify (X^2-34) h

/-- Being a prime over 73 is equivalent to being one of the three displayed ideals. -/
theorem prime_ideals (P : Ideal (𝓞 K)) : P ∈ above ↔ P = P₉ ∨ P = P₆₄ ∨ P = P₃₄ := by
  constructor
  · intro hP
    let p : above := ⟨P,hP⟩
    have hf := (mem_factors _).mp (primesEquiv p).property
    have reduce {q : (ZMod 73)[X]} (hq : q ∈ RingOfIntegers.monicFactorsMod theta 73)
        (h : (primesEquiv p).val = q) : P = (primesEquiv.symm ⟨q,hq⟩ : Ideal (𝓞 K)) := by
      have he : primesEquiv p = ⟨q,hq⟩ := Subtype.ext h
      have he' : p = primesEquiv.symm ⟨q,hq⟩ := primesEquiv.eq_symm_apply.mpr he
      exact congrArg Subtype.val he'
    rcases hf with h | h | h
    · exact Or.inl ((reduce h₁ h).trans span₁)
    · exact Or.inr (Or.inl ((reduce h₂ h).trans span₂))
    · exact Or.inr (Or.inr ((reduce h₃ h).trans span₃))
  · rintro (rfl | rfl | rfl)
    · exact span₁ ▸ (primesEquiv.symm ⟨_,h₁⟩).property
    · exact span₂ ▸ (primesEquiv.symm ⟨_,h₂⟩).property
    · exact span₃ ▸ (primesEquiv.symm ⟨_,h₃⟩).property

private theorem unequal_factors : q₁ ≠ q₂ ∧ q₁ ≠ q₃ ∧ q₂ ≠ q₃ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have he := congrArg (fun q : (ZMod 73)[X] => q.eval 0) h
    simp only [q₁, q₂, eval_sub, eval_X, eval_C, zero_sub, neg_inj] at he
    exact (by decide : (9 : ZMod 73) ≠ 64) he
  · intro h
    exact (by decide : (1:ℕ) ≠ 2) (by simpa only [q₁, q₃, natDegree_X_sub_C,
      natDegree_X_pow_sub_C] using congrArg natDegree h)
  · intro h
    exact (by decide : (1:ℕ) ≠ 2) (by simpa only [q₂, q₃, natDegree_X_sub_C,
      natDegree_X_pow_sub_C] using congrArg natDegree h)

theorem distinct : P₉ ≠ P₆₄ ∧ P₉ ≠ P₃₄ ∧ P₆₄ ≠ P₃₄ := by
  rw [← span₁, ← span₂, ← span₃]
  exact ⟨fun h => unequal_factors.1 (congrArg Subtype.val (primesEquiv.symm.injective (Subtype.ext h))),
    fun h => unequal_factors.2.1 (congrArg Subtype.val (primesEquiv.symm.injective (Subtype.ext h))),
    fun h => unequal_factors.2.2 (congrArg Subtype.val (primesEquiv.symm.injective (Subtype.ext h)))⟩

theorem unramified : P₉.ramificationIdx ℤ = 1 ∧ P₆₄.ramificationIdx ℤ = 1 ∧
    P₃₄.ramificationIdx ℤ = 1 := by
  have h0 := Polynomial.map_monic_ne_zero (minpoly.monic theta.isIntegral) (f := red)
  have ha := Polynomial.irreducible_X_sub_C (9 : ZMod 73)
  have hb := Polynomial.irreducible_X_sub_C (64 : ZMod 73)
  obtain ⟨hab,hac,hbc⟩ := unequal_factors
  rw [← span₁, ← span₂, ← span₃]
  simp only [primesEquiv, NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply',
    multiplicity_eq_count_normalizedFactors ha h0, multiplicity_eq_count_normalizedFactors hb h0,
    multiplicity_eq_count_normalizedFactors irr₃ h0, (monic_X_sub_C (9:ZMod 73)).normalize_eq_self,
    (monic_X_sub_C (64:ZMod 73)).normalize_eq_self,
    (monic_X_pow_sub_C (34:ZMod 73) (by decide : 2 ≠ 0)).normalize_eq_self, factors]
  simp [hab, hac, hbc, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

theorem degrees : P₉.inertiaDeg ℤ = 1 ∧ P₆₄.inertiaDeg ℤ = 1 ∧ P₃₄.inertiaDeg ℤ = 2 := by
  rw [← span₁, ← span₂, ← span₃]
  simp only [primesEquiv, NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply',
    q₁, q₂, q₃, natDegree_X_sub_C, natDegree_X_pow_sub_C, and_self]

private theorem norm_from_degree (P : Ideal (𝓞 K)) (h : P ∈ above) :
    P.absNorm = 73 ^ P.inertiaDeg ℤ := by
  have := h.1
  have := h.2
  exact (Ideal.pow_inertiaDeg 73 P).symm

theorem norms : P₉.absNorm = 73 ∧ P₆₄.absNorm = 73 ∧ P₃₄.absNorm = 5329 := by
  obtain ⟨ha,hb,hc⟩ := degrees
  rw [norm_from_degree _ ((prime_ideals _).mpr (Or.inl rfl)),
    norm_from_degree _ ((prime_ideals _).mpr (Or.inr (Or.inl rfl))),
    norm_from_degree _ ((prime_ideals _).mpr (Or.inr (Or.inr rfl))), ha,hb,hc]
  norm_num

section GaussianMarks

open QuarticAt73

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private abbrev R := 𝓞 K

private theorem basis_relations (v : R) :
    let f := Ideal.Quotient.mk (Ideal.span {(73 : R), v})
    f 73 = 0 ∧ f v = 0 := by
  exact ⟨Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)),
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))⟩

private theorem relation {A : Type*} [CommRing A] (f : R →+* A) :
    (f theta)^2 = -5045155 + 1027708 * f iIntegral := by
  have h : theta^2 = -5045155 + 1027708*iIntegral := by
    apply Subtype.ext
    exact theta_sq
  simpa only [map_pow,map_add,map_mul,map_neg,map_ofNat] using congrArg f h

private theorem linear_mark {A : Type*} [CommRing A] {j t : A} (hp : (73 : A) = 0)
    (h : t^2 = -5045155 + 1027708*j) (ht : t = 9 ∨ t = 64) : j = 46 := by
  have h8 : (8:A) = -5045155 + 1027708*j := by
    rcases ht with rfl | rfl
    · linear_combination h - hp
    · linear_combination h - 56 * hp
  linear_combination -47 * h8 + (3248255-661675*j)*hp

private theorem quadratic_mark {A : Type*} [CommRing A] {j t : A} (hp : (73 : A) = 0)
    (h : t^2 = -5045155 + 1027708*j) (ht : t^2 = 34) : j = 27 := by
  linear_combination -47 * (h - ht) + (3248272-661675*j)*hp

/-- The two degree-one primes lie over the mark where i reduces to 46.
The degree-two prime lies over the conjugate mark where i reduces to 27. -/
theorem reduction_of_i :
    Ideal.Quotient.mk P₉ iIntegral = 46 ∧
    Ideal.Quotient.mk P₆₄ iIntegral = 46 ∧
    Ideal.Quotient.mk P₃₄ iIntegral = 27 := by
  refine ⟨?_,?_,?_⟩
  · obtain ⟨hp,ht⟩ := basis_relations (theta-9)
    apply linear_mark (by simpa only [map_ofNat, P₉] using hp) (relation (Ideal.Quotient.mk P₉))
    exact Or.inl (by simpa only [P₉,map_sub,map_ofNat,sub_eq_zero] using ht)
  · obtain ⟨hp,ht⟩ := basis_relations (theta-64)
    apply linear_mark (by simpa only [map_ofNat, P₆₄] using hp) (relation (Ideal.Quotient.mk P₆₄))
    exact Or.inr (by simpa only [P₆₄,map_sub,map_ofNat,sub_eq_zero] using ht)
  · obtain ⟨hp,ht⟩ := basis_relations (theta^2-34)
    apply quadratic_mark (by simpa only [map_ofNat, P₃₄] using hp) (relation (Ideal.Quotient.mk P₃₄))
    simpa only [P₃₄,map_sub,map_pow,map_ofNat,sub_eq_zero] using ht

/-- The original Gaussian prime generators in the actual three prime ideals. -/
theorem gaussian_marks :
    3-8*iIntegral ∈ P₉ ∧ 3-8*iIntegral ∈ P₆₄ ∧ 3+8*iIntegral ∈ P₃₄ := by
  obtain ⟨ha,hb,hc⟩ := reduction_of_i
  refine ⟨Ideal.Quotient.eq_zero_iff_mem.mp ?_, Ideal.Quotient.eq_zero_iff_mem.mp ?_,
    Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  · rw [map_sub,map_mul,map_ofNat,map_ofNat,ha]
    have h : (73 : R ⧸ P₉) = 0 := by simpa only [P₉,map_ofNat] using (basis_relations (theta-9)).1
    linear_combination -5*h
  · rw [map_sub,map_mul,map_ofNat,map_ofNat,hb]
    have h : (73 : R ⧸ P₆₄) = 0 := by simpa only [P₆₄,map_ofNat] using (basis_relations (theta-64)).1
    linear_combination -5*h
  · rw [map_add,map_mul,map_ofNat,map_ofNat,hc]
    have h : (73 : R ⧸ P₃₄) = 0 := by simpa only [P₃₄,map_ofNat] using (basis_relations (theta^2-34)).1
    linear_combination 3*h

end GaussianMarks

end PrimeDecomposition73
