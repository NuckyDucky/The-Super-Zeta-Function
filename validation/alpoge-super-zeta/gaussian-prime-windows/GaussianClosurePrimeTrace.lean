import GaussianClosureFrobenius
import GaussianPrimeSupport

/-! Compare the two signed Gaussian Euler coefficients with the actual
quartic Frobenius reading. The four ordered roots are kept through reduction. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open NumberField Polynomial

noncomputable section

private def residueRootAt {F : Type*} [Neg F] (a b : F) (j : ZMod 4) : F :=
  ![a, b, -a, -b] (show Fin 4 from j)

private theorem residueRootAt_injective {F : Type*} [Field F] {a b : F}
    (h2 : (2 : F) ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ^ 2 ≠ b ^ 2) :
    Function.Injective (residueRootAt a b) := by
  have hA : a ≠ -a := by
    intro h
    apply mul_ne_zero h2 ha
    rw [two_mul]
    exact (congrArg (fun u : F => u + a) h).trans (neg_add_cancel _)
  have hB : b ≠ -b := by
    intro h
    apply mul_ne_zero h2 hb
    rw [two_mul]
    exact (congrArg (fun u : F => u + b) h).trans (neg_add_cancel _)
  have hAB : a ≠ b := fun h => hab (congrArg (· ^ 2) h)
  have hAnB : a ≠ -b := fun h => hab (by rw [h, neg_sq])
  have hBnA : b ≠ -a := fun h => hAnB (by rw [h, neg_neg])
  intro j k h
  fin_cases j <;> fin_cases k <;>
    first
    | rfl
    | change a = b at h; exact (hAB h).elim
    | change b = a at h; exact (hAB h.symm).elim
    | change a = -a at h; exact (hA h).elim
    | change -a = a at h; exact (hA h.symm).elim
    | change b = -b at h; exact (hB h).elim
    | change -b = b at h; exact (hB h.symm).elim
    | change a = -b at h; exact (hAnB h).elim
    | change -b = a at h; exact (hAnB h.symm).elim
    | change b = -a at h; exact (hBnA h).elim
    | change -a = b at h; exact (hBnA h.symm).elim
    | change -a = -b at h; exact (hAB (neg_injective h)).elim
    | change -b = -a at h; exact (hAB (neg_injective h.symm)).elim

private theorem closurePrimeTrace_of_antipodal (g : GaussianClosureGroup)
    (h₀ : d4Action g 0 = 0 ∨ d4Action g 0 = 2)
    (h₁ : d4Action g 1 = 1 ∨ d4Action g 1 = 3) :
    closurePrimeTrace g = (if d4Action g 0 = 0 then 1 else -1) +
      (if d4Action g 1 = 1 then 1 else -1) := by
  revert g
  decide +kernel

private theorem pow_prime_of_square {p : ℕ} [Fact p.Prime] (hp₂ : p ≠ 2)
    {F : Type*} [Field F] [CharP F p] (u : F) (v : ZMod p)
    (he : u ^ 2 = ZMod.castHom (dvd_refl p) F v) :
    u ^ p = (quadraticChar (ZMod p) v : F) * u := by
  let ι := ZMod.castHom (dvd_refl p) F
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hodd := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp₂
  have hdegree : p / 2 * 2 + 1 = p := by omega
  calc
    _ = (u ^ 2) ^ (p / 2) * u := by rw [← pow_mul, mul_comm 2, ← pow_succ, hdegree]
    _ = ι (v ^ (p / 2)) * u := by rw [he, map_pow]
    _ = ι (quadraticChar (ZMod p) v) * u := by
      rw [quadraticChar_eq_pow_of_char_ne_two' hchar, ZMod.card]
    _ = _ := by rw [map_intCast]

private theorem pow_prime_of_intCast {p : ℕ} [Fact p.Prime]
    {F : Type*} [Field F] [CharP F p] (v : ℤ) : (v : F) ^ p = v := by
  let ι := ZMod.castHom (dvd_refl p) F
  have hv : ι ((v : ZMod p) ^ p) = ι (v : ZMod p) := by rw [ZMod.pow_card]
  simpa only [map_pow, map_intCast] using hv

/-- In the split base both Gaussian signs are the signed actions on the
two pairs of roots. In the inert base Frobenius moves between the pairs. -/
theorem archivedGaussianPrimeWeight_eq_trace_of_residue {p : ℕ} [Fact p.Prime]
    (hp₂ : p ≠ 2) (hpD : p.Coprime 26509772707289) (hpB : ¬ p ∣ 1027708)
    {F : Type*} [Field F] [CharP F p] (a b i : F)
    (hi : i ^ 2 = -1) (ha : a ^ 2 = -5045155 + 1027708 * i)
    (hb : b ^ 2 = -5045155 - 1027708 * i) (g : GaussianClosureGroup)
    (hf : ∀ j : ZMod 4, residueRootAt a b (d4Action g j) = (residueRootAt a b j) ^ p) :
    archivedGaussianPrimeWeight p = (closurePrimeTrace g : ℝ) := by
  classical
  let ι := ZMod.castHom (dvd_refl p) F
  have h2 : (2 : F) ≠ 0 := by
    change (↑(2 : ℕ) : F) ≠ 0
    rw [ne_eq, CharP.cast_eq_zero_iff F p]
    exact fun hd => hp₂ ((Nat.dvd_prime_two_le Nat.prime_two (Fact.out : p.Prime).two_le).mp hd)
  have hB : (1027708 : F) ≠ 0 := by
    change (↑(1027708 : ℕ) : F) ≠ 0
    rwa [ne_eq, CharP.cast_eq_zero_iff F p]
  have hD : (26509772707289 : F) ≠ 0 := by
    have h := fun H : ι (26509772707289 : ZMod p) = 0 =>
      norm_discriminant_ne_zero hpD (ι.injective (H.trans ι.map_zero.symm))
    simpa only [map_ofNat] using h
  have hi0 : i ≠ 0 := fun h => by simp [h] at hi
  have hab : a ^ 2 ≠ b ^ 2 := by
    intro he
    apply mul_ne_zero (mul_ne_zero h2 hB) hi0
    rw [ha, hb] at he
    linear_combination he
  have hv : a ^ 2 * b ^ 2 = (26509772707289 : F) := by
    rw [ha, hb]
    linear_combination -(1027708 : F) ^ 2 * hi
  have ha0 : a ≠ 0 := by
    intro he
    exact hD (by simpa [he] using hv.symm)
  have hb0 : b ≠ 0 := by
    intro he
    exact hD (by simpa [he] using hv.symm)
  by_cases hinert : p % 4 = 3
  · have hI3 : i ^ 3 = -i := by rw [pow_succ, hi]; ring
    have hI4 : i ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, hi]; norm_num
    have hIp : i ^ p = -i := calc
      _ = i ^ (4 * (p / 4) + 3) := congrArg (i ^ ·) (by omega)
      _ = _ := by rw [pow_add, pow_mul, hI4, one_pow, one_mul, hI3]
    have hIntA : (-5045155 : F) ^ p = -5045155 := by
      exact_mod_cast pow_prime_of_intCast (p := p) (F := F) (-5045155)
    have hIntB : (1027708 : F) ^ p = 1027708 := by
      exact_mod_cast pow_prime_of_intCast (p := p) (F := F) 1027708
    have hap : (a ^ p) ^ 2 = b ^ 2 := calc
      _ = (a ^ 2) ^ p := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ = _ := by rw [ha, hb, add_pow_char _ _ p, mul_pow, hIp, hIntA, hIntB, mul_neg, sub_eq_add_neg]
    have h1 : g ≠ 1 := fun he => by
      subst g
      have h := hf 0
      change a = a ^ p at h
      exact hab ((congrArg (· ^ 2) h).trans hap)
    have hz : g ≠ gaussianCentralElement := fun he => by
      subst g
      have h := hf 0
      change -a = a ^ p at h
      exact hab ((neg_sq a).symm.trans ((congrArg (· ^ 2) h).trans hap))
    rw [archivedGaussianPrimeWeight_inert hinert]
    simp [closurePrimeTrace, h1, hz]
  · obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr hinert
    have hr0 : r ^ 2 = -1 := by simpa only [pow_two] using hr.symm
    have hiEq : i ^ 2 = (ι r) ^ 2 := by rw [← map_pow, hr0, map_neg, map_one, hi]
    obtain ⟨r, hr, hIr⟩ : ∃ r : ZMod p, r ^ 2 = -1 ∧ ι r = i := by
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hiEq with h | h
      · exact ⟨r, hr0, h.symm⟩
      · exact ⟨-r, (neg_sq r).trans hr0, (map_neg ι r).trans h.symm⟩
    let u : ZMod p := -5045155 + 1027708 * r
    let v : ZMod p := -5045155 - 1027708 * r
    have hC : u * v = (26509772707289 : ZMod p) := by
      dsimp [u, v]
      linear_combination -(1027708 : ZMod p) ^ 2 * hr
    have hu : u ≠ 0 := fun he => norm_discriminant_ne_zero hpD (by simpa [he] using hC.symm)
    have hv : v ≠ 0 := fun he => norm_discriminant_ne_zero hpD (by simpa [he] using hC.symm)
    have hpa : a ^ p = (quadraticChar (ZMod p) u : F) * a :=
      pow_prime_of_square hp₂ a u (show a ^ 2 = ι u by
        simpa only [u, map_add, map_neg, map_ofNat, map_mul, hIr] using ha)
    have hpb : b ^ p = (quadraticChar (ZMod p) v : F) * b :=
      pow_prime_of_square hp₂ b v (show b ^ 2 = ι v by
        simpa only [v, map_sub, map_neg, map_ofNat, map_mul, hIr] using hb)
    have hInject := residueRootAt_injective h2 ha0 hb0 hab
    have hra : (d4Action g 0 = 0 ∧ quadraticChar (ZMod p) u = 1) ∨
        (d4Action g 0 = 2 ∧ quadraticChar (ZMod p) u = -1) := by
      rcases quadraticChar_dichotomy hu with h | h
      · left
        refine ⟨hInject ?_, h⟩
        rw [hf 0]
        change a ^ p = a
        rw [hpa, h, Int.cast_one, one_mul]
      · right
        refine ⟨hInject ?_, h⟩
        rw [hf 0]
        change a ^ p = -a
        rw [hpa, h, Int.cast_neg, Int.cast_one, neg_one_mul]
    have hrb : (d4Action g 1 = 1 ∧ quadraticChar (ZMod p) v = 1) ∨
        (d4Action g 1 = 3 ∧ quadraticChar (ZMod p) v = -1) := by
      rcases quadraticChar_dichotomy hv with h | h
      · left
        refine ⟨hInject ?_, h⟩
        rw [hf 1]
        change b ^ p = b
        rw [hpb, h, Int.cast_one, one_mul]
      · right
        refine ⟨hInject ?_, h⟩
        rw [hf 1]
        change b ^ p = -b
        rw [hpb, h, Int.cast_neg, Int.cast_one, neg_one_mul]
    have he := closurePrimeTrace_of_antipodal g (hra.imp And.left And.left) (hrb.imp And.left And.left)
    rw [archivedGaussianPrimeWeight_split hp₂ r hr, ← Int.cast_add]
    change (↑(quadraticChar (ZMod p) u + quadraticChar (ZMod p) v) : ℝ) = _
    exact congrArg (Int.cast : ℤ → ℝ) (by
      rw [he]
      rcases hra with ⟨hA, hU⟩ | ⟨hA, hU⟩ <;> rcases hrb with ⟨hB, hV⟩ | ⟨hB, hV⟩ <;>
        simp only [hA, hB, hU, hV] <;> decide)

private def integerRootAt (j : ZMod 4) : 𝓞 L :=
  ⟨rootAt j, QuarticCoefficient.sqrtDeltaPolynomial, QuarticModel.monic_g, by
    change aeval (rootAt j) QuarticCoefficient.sqrtDeltaPolynomial = 0
    have hr := ((QuarticModel.monic_g.map (algebraMap ℤ ℚ)).mem_rootSet.mp (rootAt_mem j))
    simpa only [QuarticModel.rationalPolynomial, aeval_map_algebraMap] using hr⟩

private def integerI : 𝓞 L :=
  ⟨iLift, X ^ 2 + 1, by monicity!, by
    change aeval iLift ((X : ℤ[X]) ^ 2 + 1) = 0
    simp only [map_add, map_pow, aeval_X, map_one, iLift_sq, neg_add_cancel]⟩

private theorem integerAction_on_root (σ : ClosureAut) (j : ZMod 4) :
    integerAction (closureGaloisEquiv σ) (integerRootAt j) =
      integerRootAt (d4Action (closureGaloisEquiv σ) j) := by
  apply Subtype.ext
  change closureGaloisEquiv.symm (closureGaloisEquiv σ) (rootAt j) =
    rootAt (d4Action (closureGaloisEquiv σ) j)
  rw [closureGaloisEquiv.symm_apply_apply]
  exact (closureGaloisLabels_on_root σ j).symm

attribute [local instance] Ideal.Quotient.field

/-- Away from the finite coefficient exceptions, the actual arithmetic
Frobenius of the closure gives the archived Gaussian prime coefficient. -/
theorem archivedGaussianPrimeWeight_eq_arithmeticFrobenius {p : ℕ} (hp : p.Prime)
    (hp₂ : p ≠ 2) (hpD : p.Coprime 26509772707289) (hpB : ¬ p ∣ 1027708)
    {P : Ideal (𝓞 L)} (hP : P ∈ closurePrimeFiber p)
    {σ : ClosureAut} (hσ : IsArithFrobAt ℤ σ P) :
    archivedGaussianPrimeWeight p = (closurePrimeTrace (closureGaloisEquiv σ) : ℝ) := by
  let : Fact p.Prime := ⟨hp⟩
  let : P.IsMaximal := closurePrimeFiber_isMaximal hp hP
  let : CharP (𝓞 L ⧸ P) p := closurePrimeFiber_charP hp hP
  let m := Ideal.Quotient.mk P
  have hi : integerI ^ 2 = (-1 : 𝓞 L) := by
    apply Subtype.ext
    exact iLift_sq
  have ha : integerRootAt 0 ^ 2 = -5045155 + 1027708 * integerI := by
    apply Subtype.ext
    exact alpha_sq
  have hb : integerRootAt 1 ^ 2 = -5045155 - 1027708 * integerI := by
    apply Subtype.ext
    exact beta_sq
  have hAt (j : ZMod 4) :
      m (integerRootAt j) = residueRootAt (m (integerRootAt 0)) (m (integerRootAt 1)) j := by
    have h₂ : integerRootAt 2 = -integerRootAt 0 := Subtype.ext rfl
    have h₃ : integerRootAt 3 = -integerRootAt 1 := Subtype.ext rfl
    fin_cases j
    · rfl
    · rfl
    · change m (integerRootAt 2) = -m (integerRootAt 0)
      rw [h₂, map_neg]
    · change m (integerRootAt 3) = -m (integerRootAt 1)
      rw [h₃, map_neg]
  apply archivedGaussianPrimeWeight_eq_trace_of_residue hp₂ hpD hpB
    (m (integerRootAt 0)) (m (integerRootAt 1)) (m integerI)
  · simpa only [map_pow, map_neg, map_one] using congrArg m hi
  · simpa only [map_pow, map_add, map_mul, map_neg, map_ofNat] using congrArg m ha
  · simpa only [map_pow, map_sub, map_mul, map_neg, map_ofNat] using congrArg m hb
  · intro j
    rw [← hAt, ← hAt, ← integerAction_on_root]
    exact arithmeticFrobenius_reading hp hP hσ (integerRootAt j)

#print axioms closurePrimeTrace_of_antipodal
#print axioms archivedGaussianPrimeWeight_eq_trace_of_residue
#print axioms archivedGaussianPrimeWeight_eq_arithmeticFrobenius

end
end GaussianQuarticClosure
end AlpogeSuperZeta
