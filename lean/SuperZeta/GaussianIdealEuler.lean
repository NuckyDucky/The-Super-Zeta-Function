import SuperZeta.FractionalTurnAt73
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Polynomial.SpecificDegree

/-! The local series for residue degrees 1,1,2 at 73.
An ideal supported on the three primes is specified by nonnegative exponents
(a,b,c); its norm is 73^(a+b+2c). We count those exponent triples here. -/

namespace SuperZeta.GaussianIdealEuler

open FractionalTurnAt73

private instance : Fact (Nat.Prime 73) := ⟨by decide⟩

/-- The minimal polynomial of the square root of the marked discriminant has
two linear factors and one quadratic factor modulo 73. -/
theorem quartic_mod_73 :
    ((Polynomial.X^4 + 10090310*Polynomial.X^2 + 26509772707289 : Polynomial ℤ).map
      (Int.castRingHom (ZMod 73))) =
      (Polynomial.X-9)*(Polynomial.X-64)*(Polynomial.X^2-34) := by
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat]
  have h : (73 : Polynomial (ZMod 73)) = 0 := by
    simpa only [map_ofNat, map_zero] using
      congrArg (Polynomial.C (R := ZMod 73)) (by decide : (73 : ZMod 73) = 0)
  linear_combination (Polynomial.X^3+138216*Polynomial.X^2-34*Polynomial.X+363147571601)*h

theorem quadratic_mod_73_irreducible :
    Irreducible (Polynomial.X^2-34 : Polynomial (ZMod 73)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · change (Polynomial.X^2-Polynomial.C (34 : ZMod 73)).natDegree ∈ Finset.Icc 1 3
    rw [Polynomial.natDegree_X_pow_sub_C]
    decide
  · intro x hx
    have h : ∀ x : ZMod 73, x^2 ≠ 34 := by decide
    apply h x
    simpa [Polynomial.IsRoot, sub_eq_zero] using hx

/-- The two ordinary degree-one factors and the signed Gaussian factor. -/
noncomputable def fieldSeries : PowerSeries ℚ := signedGeometric 1 ^ 2 * localSeries

theorem fieldSeries_denominator :
    fieldSeries * ((1 - PowerSeries.X)^2 * (1-PowerSeries.X^2)) = 1 := by
  have h := signedGeometric_denominator 1
  simp only [map_one, one_mul] at h
  calc
    _ = (signedGeometric 1 * (1-PowerSeries.X))^2 *
      (localSeries * (1-PowerSeries.X^2)) := by unfold fieldSeries; ring
    _ = 1 := by rw [h, localSeries_denominator]; norm_num

private theorem base_coeff (n : ℕ) :
    PowerSeries.coeff ℚ n (signedGeometric 1 ^ 2) = n + 1 := by
  rw [pow_two, PowerSeries.coeff_mul]
  simp [signedGeometric, Finset.Nat.card_antidiagonal]

private theorem strip_pair : fieldSeries - fieldSeries * PowerSeries.X^2 = signedGeometric 1^2 := by
  rw [← mul_one_sub]
  unfold fieldSeries
  rw [mul_assoc, localSeries_denominator, mul_one]

private theorem initial (n : ℕ) (h : n < 2) : PowerSeries.coeff ℚ n fieldSeries = n+1 := by
  have e := congrArg (PowerSeries.coeff ℚ n) strip_pair
  rw [map_sub, PowerSeries.coeff_mul_X_pow', if_neg (by omega), sub_zero, base_coeff] at e
  exact e

private theorem next (n : ℕ) : PowerSeries.coeff ℚ (n+2) fieldSeries =
    PowerSeries.coeff ℚ n fieldSeries + n + 3 := by
  have e := congrArg (PowerSeries.coeff ℚ (n+2)) strip_pair
  rw [map_sub, PowerSeries.coeff_mul_X_pow, base_coeff] at e
  push_cast at e
  linarith

/-- The coefficient of T^(2r) in the local field series. -/
theorem even_coeff (r : ℕ) :
    PowerSeries.coeff ℚ (2*r) fieldSeries = (r+1 : ℚ)^2 := by
  induction r with
  | zero => simpa using initial 0 (by decide)
  | succ r ih =>
    rw [show 2*(r+1) = 2*r+2 by omega, next, ih]
    push_cast
    ring

/-- The coefficient of T^(2r+1) in the local field series. -/
theorem odd_coeff (r : ℕ) :
    PowerSeries.coeff ℚ (2*r+1) fieldSeries = (r+1 : ℚ)*(r+2) := by
  induction r with
  | zero => convert initial 1 (by decide) using 1; norm_num
  | succ r ih =>
    rw [show 2*(r+1)+1 = (2*r+1)+2 by omega, next, ih]
    push_cast
    ring

/-- Every nonnegative exponent triple of weighted degree n is recovered from c
and the exponent a of the first degree-one prime. -/
noncomputable def exponentChoices (n : ℕ) :
    {t : ℕ × ℕ × ℕ // t.1 + t.2.1 + 2*t.2.2 = n} ≃
      (Σ c : Fin (n/2+1), Fin (n-2*c.val+1)) where
  toFun := fun ⟨⟨a,b,c⟩, h⟩ => ⟨⟨c, by dsimp at h; omega⟩, ⟨a, by dsimp at h ⊢; omega⟩⟩
  invFun := fun ⟨⟨c,hc⟩,⟨a,ha⟩⟩ => ⟨(a,n-2*c-a,c), by dsimp at *; omega⟩
  left_inv := by
    rintro ⟨⟨a,b,c⟩, h⟩
    change a+b+2*c = n at h
    apply Subtype.ext
    change (a,n-2*c-a,c) = (a,b,c)
    rw [show n-2*c-a = b by omega]
  right_inv := by rintro ⟨⟨c,hc⟩,⟨a,ha⟩⟩; rfl

private def choices (n : ℕ) : ℕ := ∑ c ∈ Finset.range (n/2+1), (n-2*c+1)

theorem count_exponents (n : ℕ) :
    Nat.card {t : ℕ × ℕ × ℕ // t.1 + t.2.1 + 2*t.2.2 = n} = choices n := by
  rw [Nat.card_congr (exponentChoices n), Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range (fun c => n-2*c+1) _

private theorem choices_next (n : ℕ) : choices (n+2) = choices n+n+3 := by
  unfold choices
  rw [show (n+2)/2+1 = (n/2+1)+1 by omega, Finset.sum_range_succ']
  simp only [show n+2-2*0+1 = n+3 by omega]
  have h (c : ℕ) : n+2-2*(c+1)+1 = n-2*c+1 := by omega
  simp only [h]
  omega

/-- The arithmetic series obtained from the quartic's signed local factor counts
exactly the exponent triples of degrees (1,1,2) for every prime power. -/
theorem coeff_eq_exponent_count (n : ℕ) :
    PowerSeries.coeff ℚ n fieldSeries =
      (Nat.card {t : ℕ × ℕ × ℕ // t.1 + t.2.1 + 2*t.2.2 = n} : ℚ) := by
  rw [count_exponents]
  induction n using Nat.twoStepInduction with
  | zero => norm_num [initial 0 (by decide), choices]
  | one => norm_num [initial 1 (by decide), choices]
  | more n h₀ _ =>
    rw [next, h₀, choices_next]
    push_cast
    ring

end SuperZeta.GaussianIdealEuler
