import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Data.Nat.Squarefree

/-! The integer norm calculation in the Dirichlet proof of Gaussian
quadratic reciprocity. It also applies to a squarefree composite norm. -/

namespace QuarticModel

private theorem jacobiSym_natAbs_left_of_one_mod_four (a : ℤ) {b : ℕ} (hb : b % 4 = 1) :
    jacobiSym a b = jacobiSym a.natAbs b := by
  have hbOdd : Odd b := Nat.odd_iff.mpr (by omega)
  rcases Int.natAbs_eq a with ha | ha
  · exact congrArg (fun k : ℤ => jacobiSym k b) ha
  · calc
      jacobiSym a b = jacobiSym (-(a.natAbs : ℤ)) b := congrArg (fun k : ℤ => jacobiSym k b) ha
      _ = jacobiSym a.natAbs b := by rw [jacobiSym.neg _ hbOdd, ZMod.χ₄_nat_one_mod_four hb, one_mul]

private theorem norm_coordinates_coprime {n : ℕ} {x y : ℤ}
    (hn : (n : ℤ) = x^2 + y^2) (hs : Squarefree n) : y.gcd x.natAbs = 1 := by
  change Nat.Coprime y.natAbs x.natAbs
  refine Nat.coprime_of_dvd ?_
  intro q hq hy hx
  have hy' : (q : ℤ) ∣ y := Int.dvd_natAbs.mp (by exact_mod_cast hy)
  have hx' : (q : ℤ) ∣ x := Int.dvd_natAbs.mp (by exact_mod_cast hx)
  have hqd : (q : ℤ)*(q : ℤ) ∣ (n : ℤ) := by
    rw [hn, pow_two, pow_two]
    exact dvd_add (mul_dvd_mul hx' hx') (mul_dvd_mul hy' hy')
  exact Nat.squarefree_iff_prime_squarefree.mp hs q hq (by exact_mod_cast hqd)

private theorem jacobiSym_norm_at_coordinate {n : ℕ} {x y : ℤ}
    (hn : (n : ℤ) = x^2 + y^2) (hs : Squarefree n) : jacobiSym n x.natAbs = 1 := by
  have hd : (x.natAbs : ℤ) ∣ x := Int.dvd_natAbs.mp dvd_rfl
  have hm : (n : ℤ) ≡ y^2 [ZMOD (x.natAbs : ℤ)] := by
    rw [hn]
    simpa only [zero_add] using
      (Int.modEq_zero_iff_dvd.mpr (hd.trans (dvd_pow_self _ two_ne_zero))).add_right (y^2)
  rw [jacobiSym.mod_left' hm, jacobiSym.sq_one' (norm_coordinates_coprime hn hs)]

/-- An odd coordinate of a squarefree sum-of-two-squares norm gives sign one. -/
theorem jacobiSym_coordinate_at_norm {n : ℕ} {x y : ℤ} (hn : (n : ℤ) = x^2 + y^2)
    (hs : Squarefree n) (h4 : n % 4 = 1) (hx : Odd x.natAbs) : jacobiSym x n = 1 := by
  rw [jacobiSym_natAbs_left_of_one_mod_four x h4, jacobiSym.quadratic_reciprocity_one_mod_four' hx h4]
  exact jacobiSym_norm_at_coordinate hn hs

/-- If a squarefree product is a sum of two squares, at an odd coordinate
the Jacobi signs of its two factors of residue one mod four agree. -/
theorem jacobiSym_coordinate_at_norm_factors {p d : ℕ} {x y : ℤ}
    (hn : ((p*d : ℕ) : ℤ) = x^2 + y^2) (hs : Squarefree (p*d))
    (hp : p % 4 = 1) (hd : d % 4 = 1) (hx : Odd x.natAbs) :
    jacobiSym x p = jacobiSym x d := by
  have : NeZero p := ⟨by omega⟩
  have : NeZero d := ⟨by omega⟩
  have hmod : (p*d) % 4 = 1 := by rw [Nat.mul_mod, hp, hd]
  have hprod := jacobiSym_coordinate_at_norm hn hs hmod hx
  rw [jacobiSym.mul_right] at hprod
  rcases jacobiSym.trichotomy x p with h | h | h <;> rw [h] at hprod ⊢ <;> omega

#print axioms jacobiSym_coordinate_at_norm
#print axioms jacobiSym_coordinate_at_norm_factors

end QuarticModel
