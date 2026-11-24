import RelativeQuarticNormCharacter

/-! Apply the relative factor counts at the two Gaussian primes above a
split rational prime, using their explicit residue maps. -/

namespace QuarticModel

open NumberField UniqueFactorizationMonoid
open scoped Classical

def gaussianResidue {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r^2 = -1) :
    GaussianInt →+* ZMod p :=
  Zsqrtd.lift ⟨r, by simpa [pow_two] using hr⟩

def gaussianPrimeAt {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r^2 = -1) :
    Ideal GaussianInt := RingHom.ker (gaussianResidue r hr)

private theorem gaussianPrimeAt_isMaximal {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r^2 = -1) :
    (gaussianPrimeAt r hr).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (ZMod.ringHom_surjective (gaussianResidue r hr))

private theorem gaussianPrimeAt_ne_bot {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r^2 = -1) :
    gaussianPrimeAt r hr ≠ ⊥ := by
  intro h
  have hm : (p : GaussianInt) ∈ gaussianPrimeAt r hr := by
    change gaussianResidue r hr (p : GaussianInt) = 0
    rw [map_natCast, ZMod.natCast_self]
  rw [h, Ideal.mem_bot] at hm
  exact (Fact.out : p.Prime).ne_zero (Nat.cast_eq_zero.mp hm)

noncomputable def gaussianPrimeAtResidueEquiv {p : ℕ} [Fact p.Prime]
    (r : ZMod p) (hr : r^2 = -1) :
    (GaussianInt ⧸ gaussianPrimeAt r hr) ≃+* ZMod p :=
  (gaussianResidue r hr).quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (gaussianResidue r hr))

theorem quadraticChar_ringEquiv {F E : Type*} [Field F] [Field E] [Fintype F] [Fintype E]
    [DecidableEq F] [DecidableEq E]
    (e : F ≃+* E) (x : F) : quadraticChar E (e x) = quadraticChar F x := by
  have hs : IsSquare (e x) ↔ IsSquare x := by
    constructor
    · intro h
      simpa only [RingEquiv.symm_apply_apply] using h.map e.symm
    · intro h
      exact h.map e
  by_cases hx : x = 0
  · simp only [hx, map_zero, quadraticChar_zero]
  · have he : e x ≠ 0 := fun h => hx (e.injective (h.trans e.map_zero.symm))
    by_cases h : IsSquare x
    · rw [(quadraticChar_one_iff_isSquare he).mpr (hs.mpr h),
        (quadraticChar_one_iff_isSquare hx).mpr h]
    · rw [quadraticChar_neg_one_iff_not_isSquare.mpr (mt hs.mp h),
        quadraticChar_neg_one_iff_not_isSquare.mpr h]

attribute [local instance] Ideal.Quotient.field

theorem gaussianResidue_discriminant {p : ℕ} [Fact p.Prime]
    (r : ZMod p) (hr : r^2 = -1) :
    gaussianResidue r hr gaussianDiscriminant = (-5045155 : ZMod p) + 1027708*r := by
  simp only [gaussianResidue, gaussianDiscriminant, Zsqrtd.lift_apply_apply]
  push_cast
  rfl

theorem split_rational_prime_factor_counts {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) :
    let factors := normalizedFactors ((gaussianPrimeAt r hr).map (algebraMap GaussianInt (𝓞 K)))
    let sign := quadraticChar (ZMod p) ((-5045155 : ZMod p) + 1027708*r)
    factorCounts factors =
      if sign = 0 then (1,2) else if sign = 1 then (2,2) else (1,1) := by
  let I := gaussianPrimeAt r hr
  let : I.IsMaximal := gaussianPrimeAt_isMaximal r hr
  let e := gaussianPrimeAtResidueEquiv r hr
  let : Fintype (GaussianInt ⧸ I) := Fintype.ofEquiv (ZMod p) e.symm.toEquiv
  have h₂ : (2 : GaussianInt ⧸ I) ≠ 0 := by
    intro h
    have he := congrArg e h
    rw [map_ofNat, map_zero] at he
    exact Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n]) he
  have hcount := quartic_odd_prime_counts I (gaussianPrimeAt_ne_bot r hr) h₂
  have hχ := quadraticChar_ringEquiv e (Ideal.Quotient.mk I gaussianDiscriminant)
  have hD : e (Ideal.Quotient.mk I gaussianDiscriminant) =
      (-5045155 : ZMod p) + 1027708*r := gaussianResidue_discriminant r hr
  rw [hD] at hχ
  rw [← hχ] at hcount
  exact hcount

private theorem neg_root {p : ℕ} [Fact p.Prime] {r : ZMod p} (hr : r^2 = -1) :
    (-r)^2 = -1 := by simpa only [neg_sq] using hr

private theorem odd_two_ne_zero {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])

private theorem gaussianPrimeAt_mem_iff {p : ℕ} [Fact p.Prime] {r : ZMod p} {hr : r^2 = -1}
    {z : GaussianInt} :
    z ∈ gaussianPrimeAt r hr ↔ (z.re : ZMod p) + (z.im : ZMod p)*r = 0 := Iff.rfl

theorem gaussianPrimeAt_distinct {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) : gaussianPrimeAt r hr ≠ gaussianPrimeAt (-r) (neg_root hr) := by
  intro h
  let z : GaussianInt := ⟨-(r.val : ℤ), 1⟩
  have hre : (z.re : ZMod p) = -r := by
    simp only [z, Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
  have him : (z.im : ZMod p) = 1 := Int.cast_one
  have hz : z ∈ gaussianPrimeAt r hr := gaussianPrimeAt_mem_iff.mpr (by rw [hre, him, one_mul, neg_add_cancel])
  have hz' : z ∈ gaussianPrimeAt (-r) (neg_root hr) := h ▸ hz
  have hz'' := gaussianPrimeAt_mem_iff.mp hz'
  rw [hre, him, one_mul] at hz''
  have hr0 : r ≠ 0 := by
    intro he
    simp [he] at hr
  exact mul_ne_zero (odd_two_ne_zero hp) hr0 (by linear_combination -hz'')

/-- The two explicit residue kernels are exactly the two factors of the
principal Gaussian ideal generated by the split rational prime. -/
theorem gaussianPrimeAt_product {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) :
    gaussianPrimeAt r hr * gaussianPrimeAt (-r) (neg_root hr) =
      Ideal.span ({(p : GaussianInt)} : Set GaussianInt) := by
  have htop := (gaussianPrimeAt_isMaximal r hr).coprime_of_ne
    (gaussianPrimeAt_isMaximal (-r) (neg_root hr)) (gaussianPrimeAt_distinct hp r hr)
  rw [Ideal.mul_eq_inf_of_coprime htop]
  ext z
  constructor
  · intro hz
    obtain ⟨hleft, hright⟩ := Ideal.mem_inf.mp hz
    have hpos := gaussianPrimeAt_mem_iff.mp hleft
    have hneg := gaussianPrimeAt_mem_iff.mp hright
    have hre : (z.re : ZMod p) = 0 :=
      (mul_eq_zero.mp (show (2 : ZMod p) * (z.re : ZMod p) = 0 by
        linear_combination hpos + hneg)).resolve_left (odd_two_ne_zero hp)
    have hmul : (z.im : ZMod p) * r = 0 := by simpa only [hre, zero_add] using hpos
    have hr0 : r ≠ 0 := by
      intro he
      simp [he] at hr
    have him := (mul_eq_zero.mp hmul).resolve_right hr0
    rw [Ideal.mem_span_singleton, ← Int.cast_natCast, Zsqrtd.intCast_dvd]
    exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hre,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp him⟩
  · intro hz
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hz
    apply Ideal.mem_inf.mpr
    constructor <;> change gaussianResidue _ _ ((p : GaussianInt) * d) = 0 <;>
      rw [map_mul, map_natCast, ZMod.natCast_self, zero_mul]

/-- At a split rational prime with negative norm sign, the two Gaussian
residue maps give one split prime and one inert prime in the quartic. -/
theorem opposite_norm_sign_factor_counts {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) (h : rationalNormSign p = -1) :
    (factorCounts (normalizedFactors ((gaussianPrimeAt r hr).map (algebraMap GaussianInt (𝓞 K)))),
      factorCounts (normalizedFactors ((gaussianPrimeAt (-r) (neg_root hr)).map
        (algebraMap GaussianInt (𝓞 K))))) ∈
      ({((2,2),(1,1)), ((1,1),(2,2))} : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
  have hl := split_rational_prime_factor_counts hp r hr
  have hρ := split_rational_prime_factor_counts hp (-r) (neg_root hr)
  dsimp only at hl hρ
  rw [hl, hρ]
  have hs := discriminant_pair_opposite hp r hr h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hs
  have he : (-5045155 : ZMod p) + 1027708*(-r) = -5045155 - 1027708*r := by ring
  rw [he]
  rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> simp [ha, hb]

#print axioms split_rational_prime_factor_counts
#print axioms gaussianPrimeAt_product
#print axioms opposite_norm_sign_factor_counts

end QuarticModel
