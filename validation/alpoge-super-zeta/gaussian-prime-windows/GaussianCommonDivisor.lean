import GaussianRelativeDeterminant
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.FieldTheory.Finite.GaloisField

/-! The common divisor over starting values of the archived quadratic
coefficient. This file proves the exact residue-field criterion. -/

namespace AlpogeSuperZeta

open QuadraticAlgebra

private theorem quadraticCoefficient_zero_iff {F : Type*} [Field F] {s d : F}
    (ht : (2 : F) ≠ 0) (hs : s ^ 2 ≠ d) (n : ℕ) :
    ((⟨s, 1⟩ : QuadraticAlgebra F d 0) ^ n).im = 0 ↔ relativeRotation s d ^ n = 1 := by
  let z : QuadraticAlgebra F d 0 := ⟨s, 1⟩
  have hsub : star z = algebraMap F _ s - ω := by ext <;> simp [z]
  have hadd : z = algebraMap F _ s + ω := by ext <;> simp [z]
  have hmul : relativeRotation s d * star z = z := by
    rw [hsub, hadd]
    exact relativeRotation_cayley hs
  have hpows : (relativeRotation s d) ^ n * (star z) ^ n = z ^ n := by rw [← mul_pow, hmul]
  have he : (z ^ n).im = 0 ↔ z ^ n = star (z ^ n) := by
    constructor
    · intro hi
      ext <;> simp only [re_star, im_star, zero_mul, add_zero, hi, neg_zero]
    · intro heq
      have hz := congrArg QuadraticAlgebra.im heq
      rw [im_star] at hz
      have hm : 2 * (z ^ n).im = 0 := by linear_combination hz
      exact (mul_eq_zero.mp hm).resolve_left ht
  rw [he, star_pow]
  constructor
  · intro heq
    have heq' : relativeRotation s d ^ n * (star z) ^ n =
        1 * (star z) ^ n := by rw [hpows, one_mul, heq]
    -- The conjugate factor is a unit because its norm is nonzero.
    have hz : IsUnit (star z) := by
      rw [QuadraticAlgebra.isUnit_iff_norm_isUnit, QuadraticAlgebra.norm_star]
      apply isUnit_iff_ne_zero.mpr
      simpa [norm_def, pow_two, z] using sub_ne_zero.mpr hs
    exact (hz.pow n).mul_right_cancel heq'
  · intro h
    rw [h, one_mul] at hpows
    exact hpows.symm

private theorem relativeRotation_surjects_norm_one {F : Type*} [Field F] {d : F}
    (hd : d ≠ 0) (hns : ¬IsSquare d) (v : QuadraticAlgebra F d 0)
    (hnorm : v.norm = 1) (h1 : v ≠ 1) : ∃ s, relativeRotation s d = v := by
  have hn : v.re ^ 2 - d * v.im ^ 2 = 1 := by
    simpa [norm_def, pow_two, mul_assoc] using hnorm
  have hva : v.re - 1 ≠ 0 := by
    intro h
    have ha : v.re = 1 := sub_eq_zero.mp h
    have hb : d * v.im ^ 2 = 0 := by rw [ha] at hn; linear_combination -hn
    have hz : v.im = 0 :=
      (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp ((mul_eq_zero.mp hb).resolve_left hd)
    apply h1
    exact QuadraticAlgebra.ext ha hz
  let s : F := d * v.im / (v.re - 1)
  have hr : (v.re - 1) * s = d * v.im := by
    dsimp [s]
    field_simp
  have hi : s * v.im = v.re + 1 := by
    dsimp [s]
    field_simp
    linear_combination -hn
  have hnot : s ^ 2 ≠ d := fun h => hns ⟨s, by simpa [pow_two] using h.symm⟩
  refine ⟨s, ?_⟩
  have hs : IsUnit (algebraMap F (QuadraticAlgebra F d 0) s - ω) := by
    rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
    apply isUnit_iff_ne_zero.mpr
    simpa [norm_def, pow_two] using sub_ne_zero.mpr hnot
  apply hs.mul_left_inj.mp
  rw [relativeRotation_cayley hnot]
  ext
  · simp
    linear_combination -hr
  · simp
    linear_combination -hi

private theorem quadraticCoefficient_at_square {F : Type*} [Field F] {s d : F}
    (hs : d = s ^ 2) (n : ℕ) :
    ((⟨s, 1⟩ : QuadraticAlgebra F d 0) ^ (n + 1)).im = (2 * s) ^ n := by
  let z : QuadraticAlgebra F d 0 := ⟨s, 1⟩
  have hsq : z ^ 2 = algebraMap F _ (2 * s) * z := by
    ext <;> simp [z, hs, pow_two] <;> ring
  have hpow : z ^ (n + 1) = algebraMap F _ ((2 * s) ^ n) * z := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ z (n + 1), ih, mul_assoc, ← pow_two, hsq, ← mul_assoc, ← map_mul, ← pow_succ]
  change (z ^ (n + 1)).im = _
  simp only [hpow, QuadraticAlgebra.im_mul, QuadraticAlgebra.algebraMap_re,
    QuadraticAlgebra.algebraMap_im, z, mul_one, zero_mul, add_zero]

private theorem square_sub_one_factorization {q : ℕ} (hq : 1 ≤ q) :
    q ^ 2 - 1 = (q - 1) * (q + 1) := by
  have hmul : (q - 1) * (q + 1) + 1 = q ^ 2 := calc
    _ = (q - 1) * q + q := by rw [Nat.mul_add, Nat.mul_one]; omega
    _ = (q - 1) * q + 1 * q := by rw [Nat.one_mul]
    _ = _ := by rw [← Nat.add_mul, Nat.sub_add_cancel hq, pow_two]
  omega

private theorem quadraticNorm_pow_card_add_one {F : Type*} [Field F] [Fintype F] {d : F}
    (hns : ¬IsSquare d) (z : QuadraticAlgebra F d 0) :
    algebraMap F _ z.norm = z ^ (Fintype.card F + 1) := by
  have : Fact (∀ s : F, s ^ 2 ≠ d + 0 * s) :=
    ⟨fun s hs => hns ⟨s, by simpa [pow_two] using hs.symm⟩⟩
  let R := QuadraticAlgebra F d 0
  have : Finite R := Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd d 0).symm
  have hcard : Nat.card R = Fintype.card F ^ 2 := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd d 0), Nat.card_eq_fintype_card,
      Fintype.card_prod, pow_two]
  let q := Fintype.card F
  have hq : 1 < q := Fintype.one_lt_card
  have hfac := square_sub_one_factorization hq.le
  have hn : Algebra.norm F z = z.norm := by
    rw [Algebra.norm_apply]
    exact QuadraticAlgebra.det_toLinearMap_eq_norm z
  rw [← hn, FiniteField.algebraMap_norm_eq_pow, Nat.card_eq_fintype_card (α := F), hcard]
  change z ^ ((q ^ 2 - 1) / (q - 1)) = _
  rw [hfac, Nat.mul_div_cancel_left _ (by omega : 0 < q - 1)]

/-- At every odd finite residue field, common vanishing over all
starting values detects a nonsquare and the full norm-one order. -/
theorem quadratic_coefficient_all_values_zero_iff {F : Type*} [Field F] [Fintype F]
    (ht : (2 : F) ≠ 0) {d : F} (hd : d ≠ 0) {n : ℕ} (hn : 0 < n) :
    (∀ s : F, ((⟨s, 1⟩ : QuadraticAlgebra F d 0) ^ n).im = 0) ↔
      ¬IsSquare d ∧ Fintype.card F + 1 ∣ n := by
  classical
  rcases em (IsSquare d) with ⟨s, hs⟩ | hns
  · have hnz : s ≠ 0 := fun h => hd (by simp [hs, h])
    simp only [show IsSquare d from ⟨s, hs⟩, not_true_eq_false, false_and, iff_false]
    intro hall
    have he := hall s
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    rw [quadraticCoefficient_at_square (by simpa [pow_two] using hs)] at he
    exact (pow_ne_zero k (mul_ne_zero ht hnz)) he
  · have : Fact (∀ s : F, s ^ 2 ≠ d + 0 * s) :=
      ⟨fun s hs => hns ⟨s, by simpa [pow_two] using hs.symm⟩⟩
    let R := QuadraticAlgebra F d 0
    have : Finite R := Finite.of_equiv (F × F) (QuadraticAlgebra.equivProd d 0).symm
    let q := Fintype.card F
    have hq : 1 < q := Fintype.one_lt_card
    have hcard : Nat.card Rˣ = (q - 1) * (q + 1) := by
      rw [Nat.card_units, Nat.card_congr (QuadraticAlgebra.equivProd d 0),
        Nat.card_eq_fintype_card, Fintype.card_prod, ← pow_two]
      exact square_sub_one_factorization hq.le
    have hsn (s : F) : s ^ 2 ≠ d := fun h =>
      hns ⟨s, by simpa [pow_two] using h.symm⟩
    constructor
    · intro hall
      obtain ⟨g, hg⟩ := (isCyclic_iff_exists_orderOf_eq_natCard (α := Rˣ)).mp inferInstance
      let v : R := ↑(g ^ (q - 1))
      have horder : orderOf v = q + 1 := by
        rw [orderOf_units, orderOf_pow_of_dvd (by omega) (by rw [hg, hcard]; exact dvd_mul_right _ _),
          hg, hcard, Nat.mul_div_cancel_left _ (by omega : 0 < q - 1)]
      have hp : v ^ (q + 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [horder])
      have hvn : v.norm = 1 := by
        apply (algebraMap F R).injective
        rw [quadraticNorm_pow_card_add_one hns, map_one]
        exact hp
      have hv : v ≠ 1 := fun h => by rw [h, orderOf_one] at horder; omega
      obtain ⟨s, hs⟩ := relativeRotation_surjects_norm_one hd hns v hvn hv
      have hpow := (quadraticCoefficient_zero_iff ht (hsn s) n).mp (hall s)
      exact ⟨hns, by
        rw [hs, ← orderOf_dvd_iff_pow_eq_one, horder] at hpow
        exact hpow⟩
    · rintro ⟨_, k, rfl⟩ s
      apply (quadraticCoefficient_zero_iff ht (hsn s) _).mpr
      have hp := quadraticNorm_pow_card_add_one hns (relativeRotation s d)
      rw [relativeRotation_norm (hsn s), map_one] at hp
      rw [pow_mul, ← hp, one_pow]

#print axioms quadratic_coefficient_all_values_zero_iff

end AlpogeSuperZeta
