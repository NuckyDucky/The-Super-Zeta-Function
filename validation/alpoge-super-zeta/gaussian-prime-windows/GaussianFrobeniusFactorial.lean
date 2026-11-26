import GaussianFrobeniusOrdinaryJet
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.RingTheory.Coprime.Lemmas

/-! Removing the ordinary jet factorials preserves the full prime-power
divisibility at a prime larger than the orders of all columns. -/

namespace AlpogeSuperZeta

theorem ordinaryMonomialJet_eq_factorial_mul {R : Type*} [CommRing R]
    (r s j : ℕ) (x y : R) :
    ordinaryMonomialJet r s j x y = (j.factorial : R) * (monomialJet r j x * y ^ s) := by
  simp only [ordinaryMonomialJet, monomialJet, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, mul_assoc]

theorem ordinaryFrobeniusMinor_eq_factorial_mul {R Rows : Type*} [CommRing R]
    [Fintype Rows] [DecidableEq Rows] (degree : Rows → ℕ × ℕ) (order : Rows → ℕ)
    (x y : Rows → R) :
    (Matrix.of fun r c => ordinaryMonomialJet (degree r).1 (degree r).2 (order c) (x c) (y c)).det =
      (∏ c, ((order c).factorial : R)) *
        (Matrix.of fun r c => monomialJet (degree r).1 (order c) (x c) * y c ^ (degree r).2).det := by
  let A := Matrix.of fun r c => monomialJet (degree r).1 (order c) (x c) * y c ^ (degree r).2
  let d (c : Rows) : R := (order c).factorial
  have hEq :
      (Matrix.of fun r c => ordinaryMonomialJet (degree r).1 (degree r).2 (order c) (x c) (y c)) =
        A * Matrix.diagonal d := by
    ext r c
    rw [Matrix.mul_diagonal]
    change ordinaryMonomialJet (degree r).1 (degree r).2 (order c) (x c) (y c) = A r c * d c
    rw [ordinaryMonomialJet_eq_factorial_mul, mul_comm]
    rfl
  rw [hEq, Matrix.det_mul, Matrix.det_diagonal, mul_comm]

theorem ordinaryFrobeniusMinor_ne_zero_iff {R Rows : Type*} [CommRing R] [IsDomain R]
    [CharZero R] [Fintype Rows] [DecidableEq Rows] (degree : Rows → ℕ × ℕ) (order : Rows → ℕ)
    (x y : Rows → R) :
    (Matrix.of fun r c => ordinaryMonomialJet (degree r).1 (degree r).2 (order c) (x c) (y c)).det
        ≠ 0 ↔
      (Matrix.of fun r c => monomialJet (degree r).1 (order c) (x c) * y c ^ (degree r).2).det
        ≠ 0 := by
  rw [ordinaryFrobeniusMinor_eq_factorial_mul]
  have h : (∏ c, ((order c).factorial : R)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (by intro c _; exact_mod_cast Nat.factorial_ne_zero (order c))
  simp [h]

private theorem mem_idealPow_iff_factor_mul {R : Type*} [CommRing R]
    {a b p : R} (P : Ideal R) (hp : p ∈ P) (hC : IsCoprime b p) (n : ℕ) :
    b * a ∈ P ^ n ↔ a ∈ P ^ n := by
  refine ⟨fun h => ?_, (P ^ n).mul_mem_left b⟩
  obtain ⟨u, v, hBezout⟩ := hC.pow_right (n := n)
  have hP : p ^ n ∈ P ^ n := Ideal.pow_mem_pow hp n
  have hSum := (P ^ n).add_mem ((P ^ n).mul_mem_left u h) ((P ^ n).mul_mem_left (v * a) hP)
  have hEq : u * (b * a) + (v * a) * p ^ n = a := by
    calc
      _ = (u * b + v * p ^ n) * a := by ring
      _ = a := by rw [hBezout, one_mul]
  simpa only [hEq] using hSum

theorem ordinaryFrobeniusMinor_mem_idealPow_iff {R Rows : Type*} [CommRing R]
    [Fintype Rows] [DecidableEq Rows] (degree : Rows → ℕ × ℕ) (order : Rows → ℕ)
    (x y : Rows → R) (P : Ideal R) {p : ℕ} (hp : p.Prime) (hP : (p : R) ∈ P)
    (hOrder : ∀ c, order c < p) (n : ℕ) :
    (Matrix.of fun r c => ordinaryMonomialJet (degree r).1 (degree r).2 (order c) (x c) (y c)).det
        ∈ P ^ n ↔
      (Matrix.of fun r c => monomialJet (degree r).1 (order c) (x c) * y c ^ (degree r).2).det
        ∈ P ^ n := by
  rw [ordinaryFrobeniusMinor_eq_factorial_mul]
  refine mem_idealPow_iff_factor_mul P hP (IsCoprime.prod_left fun c _ => ?_) n
  exact (hp.coprime_iff_not_dvd.mpr (fun h => (Nat.not_le_of_lt (hOrder c)) (hp.dvd_factorial.mp h))).symm.cast

#print axioms ordinaryMonomialJet_eq_factorial_mul
#print axioms ordinaryFrobeniusMinor_eq_factorial_mul
#print axioms ordinaryFrobeniusMinor_ne_zero_iff
#print axioms ordinaryFrobeniusMinor_mem_idealPow_iff

end AlpogeSuperZeta
