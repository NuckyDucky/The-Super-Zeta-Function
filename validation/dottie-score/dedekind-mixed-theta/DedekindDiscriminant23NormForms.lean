import DedekindDiscriminant23Integers
import Discriminant23ThetaEnvelope
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic

namespace FieldTarget

open NumberField
open scoped NumberField

local notation "F" => (discriminant23QuadraticSubfield : Type)
local notation "ω" => discriminant23Omega
local notation "b" => discriminant23IntegersBasis

noncomputable section

private theorem omega_coordinates_mul (a j c k : ℤ) :
    ((a : 𝓞 F) + j * ω) * ((c : 𝓞 F) + k * ω) =
      ((a * c - 6 * j * k : ℤ) : 𝓞 F) + ((a * k + j * c + j * k : ℤ) : 𝓞 F) * ω := by
  push_cast
  linear_combination ((j : 𝓞 F) * k) * discriminant23Omega_sq

/-- Evaluation at a residue root of the quadratic integer polynomial. -/
def discriminant23ResidueHom {R : Type*} [CommRing R] (r : R) (hr : r ^ 2 - r + 6 = 0) :
    𝓞 F →+* R where
  toFun x := ((b).repr x 0 : R) + ((b).repr x 1 : R) * r
  map_zero' := by simp
  map_one' := by
    have h : (1 : 𝓞 F) = ((1 : ℤ) : 𝓞 F) + ((0 : ℤ) : 𝓞 F) * ω := by norm_num
    rw [h, discriminant23Integers_repr, discriminant23Integers_repr]
    norm_num
  map_add' x y := by
    simp only [map_add, Finsupp.add_apply, Int.cast_add]
    ring
  map_mul' x y := by
    have hx : ∃ a j : ℤ, x = (a : 𝓞 F) + j * ω := ⟨_, _, discriminant23Integers_coordinates x⟩
    have hy : ∃ c k : ℤ, y = (c : 𝓞 F) + k * ω := ⟨_, _, discriminant23Integers_coordinates y⟩
    obtain ⟨a, j, rfl⟩ := hx
    obtain ⟨c, k, rfl⟩ := hy
    rw [omega_coordinates_mul]
    simp only [discriminant23Integers_repr, Matrix.cons_val_zero, Matrix.cons_val_one]
    push_cast
    linear_combination -((j : R) * k) * hr

theorem discriminant23ResidueHom_apply {R : Type*} [CommRing R] {r : R}
    (hr : r ^ 2 - r + 6 = 0) (m n : ℤ) :
    discriminant23ResidueHom r hr ((m : 𝓞 F) + n * ω) = (m : R) + (n : R) * r := by
  change ((b).repr ((m : 𝓞 F) + n * ω) 0 : R) + ((b).repr ((m : 𝓞 F) + n * ω) 1 : R) * r = _
  rw [discriminant23Integers_repr, discriminant23Integers_repr]
  rfl

def discriminant23ResidueIdeal (p : ℕ) (r : ZMod p) (hr : r ^ 2 - r + 6 = 0) : Ideal (𝓞 F) :=
  RingHom.ker (discriminant23ResidueHom r hr)

theorem discriminant23ResidueIdeal_absNorm {p : ℕ} [NeZero p] (r : ZMod p)
    (hr : r ^ 2 - r + 6 = 0) : (discriminant23ResidueIdeal p r hr).absNorm = p := by
  have hsurj : Function.Surjective (discriminant23ResidueHom r hr) := by
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    exact ⟨(k : 𝓞 F), map_intCast _ _⟩
  have hcard := Nat.card_congr (RingHom.quotientKerEquivOfSurjective hsurj).toEquiv
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact hcard.trans (by rw [Nat.card_eq_fintype_card, ZMod.card])

theorem discriminant23ResidueIdeal_isPrime {p : ℕ} [Fact p.Prime] (r : ZMod p)
    (hr : r ^ 2 - r + 6 = 0) : (discriminant23ResidueIdeal p r hr).IsPrime :=
  RingHom.ker_isPrime _

private theorem zero_root_mod_two : (0 : ZMod 2) ^ 2 - 0 + 6 = 0 := by decide +kernel

/-- The ideal of norm two at the residue root `ω = 0`. -/
def discriminant23NormTwoIdeal : Ideal (𝓞 F) :=
  discriminant23ResidueIdeal 2 0 zero_root_mod_two

theorem discriminant23NormTwoIdeal_isPrime : discriminant23NormTwoIdeal.IsPrime := by
  let : Fact (Nat.Prime 2) := ⟨by decide +kernel⟩
  exact discriminant23ResidueIdeal_isPrime 0 zero_root_mod_two

theorem discriminant23NormTwoIdeal_absNorm : discriminant23NormTwoIdeal.absNorm = 2 :=
  discriminant23ResidueIdeal_absNorm 0 zero_root_mod_two

theorem discriminant23NormTwoIdeal_mem (m n : ℤ) :
    (m : 𝓞 F) + n * ω ∈ discriminant23NormTwoIdeal ↔ (2 : ℤ) ∣ m := by
  change discriminant23ResidueHom (0 : ZMod 2) zero_root_mod_two ((m : 𝓞 F) + n * ω) = 0 ↔ _
  rw [discriminant23ResidueHom_apply, mul_zero, add_zero]
  exact ZMod.intCast_zmod_eq_zero_iff_dvd m 2

theorem discriminant23NormTwoIdeal_coordinates (x : 𝓞 F) :
    x ∈ discriminant23NormTwoIdeal ↔ ∃ m n : ℤ, x = ((2 * m : ℤ) : 𝓞 F) + n * ω := by
  constructor
  · intro hx
    have he := discriminant23Integers_coordinates x
    have hmem : ((b).repr x 0 : 𝓞 F) + ((b).repr x 1 : 𝓞 F) * ω ∈ discriminant23NormTwoIdeal := he ▸ hx
    obtain ⟨m, hm⟩ := (discriminant23NormTwoIdeal_mem ((b).repr x 0) ((b).repr x 1)).mp hmem
    exact ⟨m, (b).repr x 1, he.trans (by rw [← hm])⟩
  · rintro ⟨m, n, rfl⟩
    exact (discriminant23NormTwoIdeal_mem (2 * m) n).mpr (dvd_mul_right 2 m)

theorem discriminant23_principal_norm_form (m n : ℤ) :
    Algebra.norm ℤ ((m : 𝓞 F) + n * ω) = discriminant23PrincipalForm m n :=
  discriminant23_quadratic_norm m n

theorem discriminant23_norm_two_form (m n : ℤ) :
    Algebra.norm ℤ (((2 * m : ℤ) : 𝓞 F) + n * ω) =
      (discriminant23NormTwoIdeal.absNorm : ℤ) * discriminant23OtherForm m n := by
  rw [discriminant23_quadratic_norm, discriminant23NormTwoIdeal_absNorm]
  unfold discriminant23OtherForm
  push_cast
  ring

/-- All generators of a principal ideal differ only by sign. -/
theorem discriminant23_units_eq_one_or_neg_one (u : (𝓞 F)ˣ) :
    (u : 𝓞 F) = 1 ∨ (u : 𝓞 F) = -1 := by
  obtain ⟨m, n, he⟩ : ∃ m n : ℤ, (u : 𝓞 F) = (m : 𝓞 F) + n * ω :=
    ⟨_, _, discriminant23Integers_coordinates u⟩
  have hNorm := (u.isUnit).map (Algebra.norm ℤ)
  rw [he, discriminant23_quadratic_norm] at hNorm
  have hg : m ^ 2 + m * n + 6 * n ^ 2 ≤ 1 := by
    rcases Int.isUnit_iff.mp hNorm with h | h <;> omega
  have hn : n = 0 := by
    by_contra hne
    have h1 : 1 ≤ n ^ 2 := by
      have h := sq_pos_of_ne_zero hne
      omega
    nlinarith only [h1, hg, sq_nonneg (2 * m + n)]
  subst n
  have hsq : m ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hNorm with h | h
    · simpa using h
    · norm_num at h
      nlinarith only [h, sq_nonneg m]
  have hp : (m - 1) * (m + 1) = 0 := by nlinarith only [hsq]
  rcases mul_eq_zero.mp hp with hp | hp
  · have hm : m = 1 := by omega
    simp [he, hm]
  · have hm : m = -1 := by omega
    simp [he, hm]

#check @discriminant23NormTwoIdeal_coordinates
#check @discriminant23_principal_norm_form
#check @discriminant23_norm_two_form
#print axioms discriminant23ResidueIdeal_absNorm
#print axioms discriminant23NormTwoIdeal_isPrime
#print axioms discriminant23NormTwoIdeal_coordinates
#print axioms discriminant23_principal_norm_form
#print axioms discriminant23_norm_two_form
#print axioms discriminant23_units_eq_one_or_neg_one

end
end FieldTarget
