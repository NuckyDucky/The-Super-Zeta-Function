import GaussianConductorResidue
import Mathlib.Algebra.QuadraticAlgebra.Basic

/-! The two marked roots at a Gaussian prime are fixed or exchanged by
Frobenius according to the archived quadratic character. A single
norm-one element over the Gaussian base retains this action on reduction. -/

namespace AlpogeSuperZeta

open QuarticModel QuadraticAlgebra

theorem quadratic_frobenius_pow {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (d : ZMod p)
    (x : QuadraticAlgebra (ZMod p) d 0) (n : ℕ) :
    x ^ (p ^ n) = ⟨x.re, (quadraticChar (ZMod p) d : ZMod p) ^ n * x.im⟩ := by
  let R := QuadraticAlgebra (ZMod p) d 0
  let ι := algebraMap (ZMod p) R
  have : CharP R p := charP_of_injective_algebraMap
    (QuadraticAlgebra.algebraMap_injective (R := ZMod p) (a := d) (b := 0)) p
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hodd := ((Fact.out : p.Prime).mod_two_eq_one_iff_ne_two).mpr hp
  have hdegree : p / 2 * 2 + 1 = p := by omega
  have hω : (ω : R) ^ p = ι (quadraticChar (ZMod p) d) * ω := calc
    _ = (ω ^ 2) ^ (p / 2) * ω := by rw [← pow_mul, mul_comm 2, ← pow_succ, hdegree]
    _ = ι (d ^ (p / 2)) * ω := by
      rw [pow_two, omega_mul_omega_eq_algebraMap, map_zero, zero_mul, add_zero, map_pow]
    _ = _ := by rw [quadraticChar_eq_pow_of_char_ne_two' hchar, ZMod.card]
  have step (y : R) : y ^ p = ⟨y.re, (quadraticChar (ZMod p) d : ZMod p) * y.im⟩ := by
    have hform : y = ι y.re + ι y.im * ω := by
      conv_lhs => rw [← QuadraticAlgebra.mk_eta y]
      rw [mk_eq_add_smul_omega, Algebra.smul_def]
    calc
      _ = (ι y.re + ι y.im * ω) ^ p := congrArg (· ^ p) hform
      _ = ι y.re + ι y.im * (ι (quadraticChar (ZMod p) d) * ω) := by
        rw [add_pow_char _ _ p, mul_pow, hω, ← map_pow, ZMod.pow_card, ← map_pow, ZMod.pow_card]
      _ = ι y.re + ι ((quadraticChar (ZMod p) d : ZMod p) * y.im) * ω := by
        rw [map_mul]
        ac_rfl
      _ = _ := by rw [← Algebra.smul_def, ← mk_eq_add_smul_omega]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ p n, pow_mul, ih, step]
    ext <;> simp [pow_succ, mul_assoc, mul_left_comm]

/-- The quotient (s + ω)/(s - ω) expressed in the basis (1, ω).
Its coordinates are defined over the base field before reducing at a prime. -/
def relativeRotation {F : Type*} [Field F] (s d : F) : QuadraticAlgebra F d 0 :=
  ⟨(s ^ 2 + d) / (s ^ 2 - d), 2 * s / (s ^ 2 - d)⟩

theorem relativeRotation_cayley {F : Type*} [Field F] {s d : F} (h : s ^ 2 ≠ d) :
    relativeRotation s d * (algebraMap F _ s - ω) = algebraMap F _ s + ω := by
  ext <;> simp [relativeRotation] <;> field_simp [sub_ne_zero.mpr h] <;> ring

theorem relativeRotation_norm {F : Type*} [Field F] {s d : F} (h : s ^ 2 ≠ d) :
    (relativeRotation s d).norm = 1 := by
  simp [relativeRotation, norm_def]
  field_simp [sub_ne_zero.mpr h]
  ring

theorem relativeRotation_mul_star {F : Type*} [Field F] {s d : F} (h : s ^ 2 ≠ d) :
    relativeRotation s d * star (relativeRotation s d) = 1 := by
  rw [← algebraMap_norm_eq_mul_star, relativeRotation_norm h, map_one]

theorem relativeRotation_ne_star {F : Type*} [Field F] {s d : F}
    (ht : (2 : F) ≠ 0) (hs : s ≠ 0) (h : s ^ 2 ≠ d) :
    relativeRotation s d ≠ star (relativeRotation s d) := by
  intro he
  have hi := congrArg QuadraticAlgebra.im he
  simp only [relativeRotation, im_star] at hi
  have hz : 2 * (2 * s / (s ^ 2 - d)) = 0 := by linear_combination hi
  exact (mul_ne_zero ht (div_ne_zero (mul_ne_zero ht hs) (sub_ne_zero.mpr h))) hz

/-- The rotation uses the same Gaussian numerator and denominator at each
prime. The residue parameter still specifies the marked ideal. -/
def archivedRelativeRotation {p : ℕ} (r : ZMod p) [Fact p.Prime] :
    QuadraticAlgebra (ZMod p) ((-5045155 : ZMod p) + 1027708 * r) 0 :=
  relativeRotation (1 + r) _

theorem archived_relative_rotation_frobenius {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r ^ 2 = -1) (hI : gaussianPrimeAt r hr ∈ gaussianPrimesAbove p)
    (hd₀ : (-5045155 : ZMod p) + 1027708 * r ≠ 0)
    (hd₁ : (1 + r) ^ 2 ≠ (-5045155 : ZMod p) + 1027708 * r) (n : ℕ) :
    (archivedRelativeRotation r ^ (p ^ n) = star (archivedRelativeRotation r) ↔
      archivedIdealCharacter (gaussianPrimeAt r hr) = -1 ∧ Odd n) ∧
    (archivedRelativeRotation r ^ (p ^ n) = archivedRelativeRotation r ↔
      archivedIdealCharacter (gaussianPrimeAt r hr) = 1 ∨ Even n) := by
  let d := (-5045155 : ZMod p) + 1027708 * r
  let U := archivedRelativeRotation r
  have hchar : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  have hone := Ring.neg_one_ne_one_of_char_ne_two hchar
  have ht : (2 : ZMod p) ≠ 0 := by
    intro he
    apply hone
    linear_combination -he
  have hs : 1 + r ≠ 0 := by
    intro he
    have hr' : r = -1 := by linear_combination he
    exact hone.symm (by simpa [hr'] using hr)
  have hne : U ≠ star U := relativeRotation_ne_star ht hs hd₁
  rw [archivedIdealCharacter_at_root hp r hr hI]
  change (U ^ (p ^ n) = star U ↔ quadraticChar (ZMod p) d = -1 ∧ Odd n) ∧
    (U ^ (p ^ n) = U ↔ quadraticChar (ZMod p) d = 1 ∨ Even n)
  have hpow := quadratic_frobenius_pow hp d U n
  rcases quadraticChar_dichotomy (a := d) hd₀ with hpos | hneg
  · have he : U ^ (p ^ n) = U := by
      rw [hpow, hpos, Int.cast_one, one_pow, one_mul, QuadraticAlgebra.mk_eta]
    rw [he, hpos]
    simp [hne]
  · rcases Nat.even_or_odd n with hn | hn
    · have he : U ^ (p ^ n) = U := by
        rw [hpow, hneg, Int.cast_neg, Int.cast_one, hn.neg_pow, one_pow, one_mul,
          QuadraticAlgebra.mk_eta]
      rw [he, hneg]
      simp [hne, hn, Nat.not_odd_iff_even.mpr hn]
    · have he : U ^ (p ^ n) = star U := by
        rw [hpow, hneg, Int.cast_neg, Int.cast_one, hn.neg_pow, one_pow, neg_one_mul]
        ext <;> simp
      rw [he, hneg]
      simp [Ne.symm hne, hn, Nat.not_even_iff_odd.mpr hn]

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 73) := ⟨by decide⟩

theorem archived_relative_rotation_at_5_and_13 :
    archivedRelativeRotation (2 : ZMod 5) ^ 5 = archivedRelativeRotation (2 : ZMod 5) ∧
    archivedRelativeRotation (-2 : ZMod 5) ^ 5 = archivedRelativeRotation (-2 : ZMod 5) ∧
    archivedRelativeRotation (5 : ZMod 13) ^ 13 = star (archivedRelativeRotation (5 : ZMod 13)) ∧
    archivedRelativeRotation (-5 : ZMod 13) ^ 13 = star (archivedRelativeRotation (-5 : ZMod 13)) :=
  by decide +kernel

theorem archived_relative_rotation_at_73 :
    archivedRelativeRotation (27 : ZMod 73) ^ 73 = star (archivedRelativeRotation (27 : ZMod 73)) ∧
    archivedRelativeRotation (-27 : ZMod 73) ^ 73 = archivedRelativeRotation (-27 : ZMod 73) :=
  by decide +kernel

private theorem exactOrderOfSmallPower {M : Type*} [Monoid M] (u : M) (n : ℕ)
    (hn : 0 < n) (hpow : u ^ n = 1)
    (hmin : ∀ j : Fin n, 0 < j.val → u ^ j.val ≠ 1) : orderOf u = n :=
  (orderOf_eq_iff hn).mpr ⟨hpow, fun j hj => hmin ⟨j, hj⟩⟩

theorem archived_rotation_exact_orders_at_5 :
    orderOf (archivedRelativeRotation (2 : ZMod 5)) = 4 ∧
    orderOf (archivedRelativeRotation (-2 : ZMod 5)) = 4 := by
  constructor
  · exact exactOrderOfSmallPower _ 4 (by decide) (by decide +kernel) (by decide +kernel)
  · exact exactOrderOfSmallPower _ 4 (by decide) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 20000 in
theorem archived_rotation_exact_orders_at_73 :
    orderOf (archivedRelativeRotation (27 : ZMod 73)) = 74 ∧
    orderOf (archivedRelativeRotation (-27 : ZMod 73)) = 72 := by
  constructor
  · exact exactOrderOfSmallPower _ 74 (by decide) (by decide +kernel) (by decide +kernel)
  · exact exactOrderOfSmallPower _ 72 (by decide) (by decide +kernel) (by decide +kernel)

#print axioms quadratic_frobenius_pow
#print axioms relativeRotation_cayley
#print axioms relativeRotation_mul_star
#print axioms archived_relative_rotation_frobenius
#print axioms archived_relative_rotation_at_5_and_13
#print axioms archived_relative_rotation_at_73
#print axioms archived_rotation_exact_orders_at_5
#print axioms archived_rotation_exact_orders_at_73

end AlpogeSuperZeta
