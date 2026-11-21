import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Multiplicity
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.NatSqrt

namespace SuperZeta.FactorialPell

/-- Every factorial with fixed squarefree part has a prime divisor of that part
    in the upper half of the factorial's index. In fact q need not be squarefree. -/
theorem upper_half_prime {n q s : ℕ} (hn : 2 ≤ n) (h : n.factorial = q * s ^ 2) :
    ∃ p, p.Prime ∧ p ∣ q ∧ n < 2 * p ∧ p ≤ n := by
  obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  have hpN : p ≤ n := by omega
  have hN : n < 2 * p := by omega
  have hlog : Nat.log p n < 2 := Nat.log_lt_of_lt_pow (by omega)
    (lt_of_lt_of_le hN (by simpa [sq] using Nat.mul_le_mul_right p hp.two_le))
  have hnodvd : ¬ p ^ 2 ∣ n.factorial := by
    rw [hp.pow_dvd_factorial_iff hlog]
    have hi : Finset.Ico 1 (2 : ℕ) = {1} := by decide
    simpa [hi] using
      (not_le.mpr ((Nat.div_lt_iff_lt_mul hp.pos).2 hN) : ¬ 2 ≤ n / p)
  have hdvd : p ∣ q * s ^ 2 := h ▸ Nat.dvd_factorial hp.pos hpN
  refine ⟨p, hp, (hp.dvd_mul.mp hdvd).elim id (fun hs => ?_), hN, hpN⟩
  exact False.elim (hnodvd (h ▸ dvd_mul_of_dvd_right
    (pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow hs) 2) q))

theorem fixed_prime_bound {n q s P : ℕ} (hn : 2 ≤ n) (h : n.factorial = q * s ^ 2)
    (hP : P.Prime) (hPq : P ∣ q) (hmax : ∀ p, Nat.Prime p → p ∣ q → p ≤ P) :
    P ≤ n ∧ n < 2 * P := by
  obtain ⟨p, hp, hpq, hn', _⟩ := upper_half_prime hn h
  have := hmax p hp hpq
  refine ⟨hP.dvd_factorial.mp ?_, by omega⟩
  rw [h]
  exact dvd_mul_of_dvd_left hPq _

theorem squarefree_part_35 {n s : ℕ} (hn : 2 ≤ n) (h : n.factorial = 35 * s ^ 2) :
    n = 7 ∧ s = 12 := by
  have ⟨hlo, hhi⟩ := fixed_prime_bound (P := 7) hn h (by decide) (by decide) (by
    intro p hp hdvd
    have hm : p ∣ 5 * 7 := hdvd
    rcases hp.dvd_mul.mp hm with ha | hb
    · exact le_trans (Nat.le_of_dvd (by decide) ha) (by decide)
    · exact Nat.le_of_dvd (by decide) hb)
  have hs : (n.factorial / 35).sqrt = s := by simp [h, Nat.sqrt_eq']
  have key : n.factorial = 35 * (n.factorial / 35).sqrt ^ 2 := by simpa [hs] using h
  have hn7 : n = 7 := by
    interval_cases n <;> first | rfl | (exfalso; revert key; norm_num [Nat.factorial])
  subst n
  exact ⟨rfl, hs.symm.trans (by norm_num [Nat.factorial])⟩

/-- No factorial having squarefree part 70 is one less than an integer square. -/
theorem no_factorial_square_70 {n s m : ℕ} (hn : 2 ≤ n)
    (h : n.factorial = 70 * s ^ 2) (hm : n.factorial + 1 = m ^ 2) : False := by
  have ⟨hlo, hhi⟩ := fixed_prime_bound (P := 7) hn h (by decide) (by decide) (by
    intro p hp hdvd
    have hprod : p ∣ (2 * 5) * 7 := hdvd
    rcases hp.dvd_mul.mp hprod with hsmall | hseven
    · rcases hp.dvd_mul.mp hsmall with htwo | hfive
      · exact le_trans (Nat.le_of_dvd (by decide) htwo) (by decide)
      · exact le_trans (Nat.le_of_dvd (by decide) hfive) (by decide)
    · exact Nat.le_of_dvd (by decide) hseven)
  have hq : n.factorial = 70 * (n.factorial / 70).sqrt ^ 2 := by
    simp [h, Nat.sqrt_eq']
  have hsquare : n.factorial + 1 = (n.factorial + 1).sqrt ^ 2 := by
    simp [hm, Nat.sqrt_eq']
  interval_cases n <;> first
    | (revert hq; solve | norm_num [Nat.factorial])
    | (revert hsquare; solve | norm_num [Nat.factorial])

#print axioms upper_half_prime
#print axioms fixed_prime_bound
#print axioms squarefree_part_35
#print axioms no_factorial_square_70

end SuperZeta.FactorialPell
