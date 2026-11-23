import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic

/-! Check a prime certificate using a complete factor list for p−1 and
modular powers. The example is the first nonzero norm in the retained band. -/

namespace QuarticModel

set_option autoImplicit false

private theorem dottie_prime_dvd_list_prod {q : ℕ} (hq : q.Prime) (factors : List ℕ)
    (hp : ∀ p ∈ factors, p.Prime) (h : q ∣ factors.prod) : q ∈ factors := by
  induction factors with
  | nil =>
    simp only [List.prod_nil, Nat.dvd_one] at h
    exact (hq.ne_one h).elim
  | cons p ps ih =>
    rw [List.prod_cons, hq.dvd_mul] at h
    rcases h with hd | hd
    · have he := (Nat.prime_dvd_prime_iff_eq hq (hp p List.mem_cons_self)).mp hd
      subst q
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (fun r hr => hp r (List.mem_cons_of_mem _ hr)) hd)

/-- A Lucas proof from already checked prime factors. Modular powers are
proved by the verified repeated-squaring tactic on concrete residues. -/
theorem dottie_lucas_of_factor_list (p : ℕ) (g : ZMod p) (factors : List ℕ)
    (hprod : factors.prod = p-1) (hp : ∀ q ∈ factors, q.Prime)
    (hpow : g^(p-1) = 1) (hproper : ∀ q ∈ factors, g^((p-1)/q) ≠ 1) :
    p.Prime := by
  apply lucas_primality p g hpow
  intro q hq hd
  rw [← hprod] at hd
  exact hproper q (dottie_prime_dvd_list_prod hq factors hp hd)

private theorem prime_269 : Nat.Prime 269 := by
  apply dottie_lucas_of_factor_list 269 2 [2, 2, 67] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_439 : Nat.Prime 439 := by
  apply dottie_lucas_of_factor_list 439 15 [2, 3, 73] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals norm_num
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_128189 : Nat.Prime 128189 := by
  apply dottie_lucas_of_factor_list 128189 2 [2, 2, 73, 439] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_439 | norm_num
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_17784199 : Nat.Prime 17784199 := by
  apply dottie_lucas_of_factor_list 17784199 3 [2, 3, 3, 3, 3, 3, 23, 37, 43] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals norm_num
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_320115583 : Nat.Prime 320115583 := by
  apply dottie_lucas_of_factor_list 320115583 5 [2, 3, 3, 17784199] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    all_goals first | exact prime_17784199 | norm_num
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

private theorem prime_463616779508874727 : Nat.Prime 463616779508874727 := by
  apply dottie_lucas_of_factor_list 463616779508874727 6 [2, 3, 7, 269, 128189, 320115583] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact prime_269 | exact prime_128189 | exact prime_320115583 | norm_num
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

theorem dottie_first_nonzero_band_prime : Nat.Prime 1854467118035498909 := by
  apply dottie_lucas_of_factor_list 1854467118035498909 2 [2, 2, 463616779508874727] (by decide +kernel)
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    all_goals first | exact prime_463616779508874727 | norm_num
  · reduce_mod_char
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl <;> reduce_mod_char <;> decide +kernel

#print axioms dottie_lucas_of_factor_list
#print axioms dottie_first_nonzero_band_prime

end QuarticModel
