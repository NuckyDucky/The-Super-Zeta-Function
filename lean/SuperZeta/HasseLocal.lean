import SuperZeta.Hasse
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.Tactic.NormNum.Prime

/-! Hensel lifts at the nine primes in the archived discriminant factorization. -/
namespace SuperZeta.Hasse
open Polynomial

private theorem square_lift {p : ℕ} [Fact p.Prime] (m a : ℤ)
    (hn : ‖((a^2-m : ℤ):ℤ_[p])‖ < ‖((2*a : ℤ):ℤ_[p])‖^2) :
    ∃ y : ℤ_[p], y^2 = (m:ℤ_[p]) := by
  let F : Polynomial ℤ_[p] := X^2 - C (m:ℤ_[p])
  have hd : F.derivative.eval (a:ℤ_[p]) = ((2*a:ℤ):ℤ_[p]) := by
    simp [F, derivative_pow]
  have hh : ‖F.eval (a:ℤ_[p])‖ < ‖F.derivative.eval (a:ℤ_[p])‖^2 := by
    rw [hd]
    simpa [F] using hn
  obtain ⟨y,hy,_⟩ := hensels_lemma hh
  refine ⟨y, ?_⟩
  simpa [F, sub_eq_zero] using hy

theorem simple_square_lift {p : ℕ} [Fact p.Prime] (m a : ℤ)
    (hroot : (p:ℤ) ∣ a^2-m) (hunit : ¬(p:ℤ) ∣ 2*a) :
    ∃ y : ℤ_[p], y^2 = (m:ℤ_[p]) := by
  apply square_lift m a
  have he := (PadicInt.norm_int_lt_one_iff_dvd (p:=p) (a^2-m)).2 hroot
  have hu := mt (PadicInt.norm_int_lt_one_iff_dvd (p:=p) (2*a)).1 hunit
  rwa [le_antisymm (PadicInt.norm_le_one _) (le_of_not_gt hu), one_pow]

theorem two_square_lift : ∃ y : ℤ_[2], y^2 = (142145:ℤ_[2]) := by
  apply square_lift 142145 1
  have h := (@PadicInt.norm_int_le_pow_iff_dvd 2 _ (1^2-142145) 3).2 (by decide)
  have htwo : ‖(2:ℤ_[2])‖ = (2:ℝ)⁻¹ := PadicInt.norm_p
  norm_num only [Int.cast_mul, Int.cast_one, mul_one, Int.cast_ofNat]
  rw [htwo]
  apply lt_of_le_of_lt h
  norm_num

/-- The integral root in this projective chart also gives a point over ℚₚ. -/
theorem scaled_square_chart {p : ℕ} [Fact p.Prime] (x v k m : ℤ)
    (hf : quartic x v = k^2*m) (h : ∃ y : ℤ_[p], y^2 = (m:ℤ_[p])) :
    ∃ z : ℚ_[p], z^2 = quartic (x:ℚ_[p]) (v:ℚ_[p]) := by
  obtain ⟨y,hy⟩ := h
  refine ⟨(k:ℚ_[p])*(y:ℚ_[p]), ?_⟩
  have hq : ((y:ℚ_[p]))^2 = (m:ℚ_[p]) := congrArg ((↑) : ℤ_[p] → ℚ_[p]) hy
  have hf' : quartic (x:ℚ_[p]) (v:ℚ_[p]) = (k:ℚ_[p])^2*(m:ℚ_[p]) := by
    unfold quartic at hf ⊢
    exact_mod_cast hf
  rw [mul_pow, hq, hf']

def badPrimes : List ℕ := [2,5,11,23,31,41,457,486971,1414835497]

theorem bad_prime_is_prime (p : ℕ) (hp : p ∈ badPrimes) : p.Prime := by
  simp only [badPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num1

/-- At every listed bad prime the archived projective chart has a point
over the p-adic numbers. The proof lifts an explicit congruence in each case. -/
theorem bad_prime_local_point (p : ℕ) [Fact p.Prime] (hp : p ∈ badPrimes) :
    ∃ x v : ℤ, (x ≠ 0 ∨ v ≠ 0) ∧
      ∃ y : ℚ_[p], y^2 = quartic (x:ℚ_[p]) (v:ℚ_[p]) := by
  simp only [badPrimes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1,1,by decide, scaled_square_chart 1 1 2 142145 (by norm_num [quartic]) two_square_lift⟩
  · exact ⟨1,5,by decide, scaled_square_chart 1 5 5 46586324 (by norm_num [quartic])
      (simple_square_lift (p:=5) 46586324 3 (by decide) (by decide))⟩
  · exact ⟨1,1,by decide, scaled_square_chart 1 1 1 568580 (by norm_num [quartic])
      (simple_square_lift (p:=11) 568580 1 (by decide) (by decide))⟩
  · exact ⟨0,1,by decide, scaled_square_chart 0 1 1 1813853 (by norm_num [quartic])
      (simple_square_lift (p:=23) 1813853 2 (by decide) (by decide))⟩
  · exact ⟨1,0,by decide, scaled_square_chart 1 0 31 1000 (by norm_num [quartic])
      (simple_square_lift (p:=31) 1000 16 (by decide) (by decide))⟩
  · exact ⟨1,0,by decide, scaled_square_chart 1 0 1 961000 (by norm_num [quartic])
      (simple_square_lift (p:=41) 961000 1 (by decide) (by decide))⟩
  · exact ⟨1,1,by decide, scaled_square_chart 1 1 1 568580 (by norm_num [quartic])
      (simple_square_lift (p:=457) 568580 23 (by decide) (by decide))⟩
  · exact ⟨1,1,by decide, scaled_square_chart 1 1 1 568580 (by norm_num [quartic])
      (simple_square_lift (p:=486971) 568580 174263 (by decide) (by decide))⟩
  · exact ⟨2,1,by decide, scaled_square_chart 2 1 1 2917781 (by norm_num [quartic])
      (simple_square_lift (p:=1414835497) 2917781 1398833718 (by decide) (by decide))⟩

end SuperZeta.Hasse
