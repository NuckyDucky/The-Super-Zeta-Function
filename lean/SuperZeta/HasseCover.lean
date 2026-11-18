import SuperZeta.HasseLocal
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! An elementary all-prime local certificate using three rational charts.
Their squarefree parts are ab, ac, bc with a=5, b=41·101, c=1033.
At odd primes where all three are units at least one pair is a square. -/
namespace SuperZeta.Hasse

private theorem unit_prime_cast {p q : ℕ} [Fact p.Prime] (hq : q.Prime) (hpq : p ≠ q) :
    (q : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_zmod_eq_zero_iff_dvd, Nat.prime_dvd_prime_iff_eq Fact.out hq]
  exact hpq

private theorem square_pair {p : ℕ} [Fact p.Prime] (a b c : ℤ)
    (ha : (a:ZMod p) ≠ 0) (hb : (b:ZMod p) ≠ 0) (hc : (c:ZMod p) ≠ 0) :
    legendreSym p (a*b) = 1 ∨ legendreSym p (a*c) = 1 ∨ legendreSym p (b*c) = 1 := by
  rcases legendreSym.eq_one_or_neg_one p ha with ha' | ha' <;>
    rcases legendreSym.eq_one_or_neg_one p hb with hb' | hb' <;>
    rcases legendreSym.eq_one_or_neg_one p hc with hc' | hc' <;>
    norm_num [legendreSym.mul, ha', hb', hc']

private theorem lift_square_symbol {p : ℕ} [Fact p.Prime]
    (htwo : (2:ZMod p) ≠ 0) {m : ℤ} (hm : (m:ZMod p) ≠ 0)
    (h : legendreSym p m = 1) : ∃ z : ℤ_[p], z^2 = (m:ℤ_[p]) := by
  obtain ⟨r,hr⟩ := (legendreSym.eq_one_iff p hm).mp h
  have hrn : r ≠ 0 := by rintro rfl; simp_all
  apply simple_square_lift m (r.val:ℤ)
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1
    simp [ZMod.natCast_zmod_val, pow_two, hr]
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
      ZMod.natCast_zmod_val]
    exact mul_ne_zero htwo hrn

/-- Every 2-adic unit integer congruent to one modulo eight is a square.
The polynomial X²+X−2k has a simple zero modulo two. -/
private theorem two_square_one_mod_eight (k : ℤ) :
    ∃ y : ℤ_[2], y^2 = ((1+8*k:ℤ):ℤ_[2]) := by
  let F : Polynomial ℤ_[2] := Polynomial.X^2+Polynomial.X-Polynomial.C ((2*k:ℤ):ℤ_[2])
  have hd : F.derivative.eval 0 = 1 := by simp [F, Polynomial.derivative_pow]
  have hn := (PadicInt.norm_int_lt_one_iff_dvd (p:=2) (2*k)).2 (dvd_mul_right ..)
  have hh : ‖F.eval 0‖ < ‖F.derivative.eval 0‖^2 := by simpa [F,hd] using hn
  obtain ⟨z,hz,_⟩ := hensels_lemma hh
  simp [F] at hz
  refine ⟨2*z+1, ?_⟩
  push_cast
  linear_combination 4*hz

/-- The four rational abscissae are 51/26, 9/5, 2/3, and 2. -/
def localCharts : List (ℤ × ℤ) := [(51,26),(9,5),(2,3),(2,1)]

/-- Four fixed integer charts cover every p-adic field. All odd primes away
from the factors of the three squareclasses use one of the first three. -/
theorem four_charts_cover (p : ℕ) [Fact p.Prime] :
    ∃ c ∈ localCharts, ∃ y : ℚ_[p], y^2 = quartic (c.1:ℚ_[p]) (c.2:ℚ_[p]) := by
  by_cases h2 : p = 2
  · subst p
    exact ⟨(51,26),by decide, scaled_square_chart 51 26 7414 (1+8*2588) (by norm_num [quartic])
      (two_square_one_mod_eight 2588)⟩
  by_cases h5 : p = 5
  · subst p
    exact ⟨(2,1),by decide, scaled_square_chart 2 1 1 2917781 (by norm_num [quartic])
      (simple_square_lift (p:=5) 2917781 1 (by decide) (by decide))⟩
  by_cases h41 : p = 41
  · subst p
    exact ⟨(9,5),by decide, scaled_square_chart 9 5 370 5165 (by norm_num [quartic])
      (simple_square_lift (p:=41) 5165 9 (by decide) (by decide))⟩
  by_cases h101 : p = 101
  · subst p
    exact ⟨(9,5),by decide, scaled_square_chart 9 5 370 5165 (by norm_num [quartic])
      (simple_square_lift (p:=101) 5165 32 (by decide) (by decide))⟩
  by_cases h1033 : p = 1033
  · subst p
    exact ⟨(2,1),by decide, scaled_square_chart 2 1 1 2917781 (by norm_num [quartic])
      (simple_square_lift (p:=1033) 2917781 406 (by decide) (by decide))⟩
  have hTwo : (2:ZMod p) ≠ 0 := unit_prime_cast Nat.prime_two h2
  have hA : ((5:ℤ):ZMod p) ≠ 0 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using unit_prime_cast (q:=5) (by norm_num1) h5
  have hB : ((41*101:ℤ):ZMod p) ≠ 0 := by
    simpa only [Int.cast_mul, Int.cast_ofNat, Nat.cast_ofNat] using
      mul_ne_zero (unit_prime_cast (q:=41) (by norm_num1) h41)
      (unit_prime_cast (q:=101) (by norm_num1) h101)
  have hC : ((1033:ℤ):ZMod p) ≠ 0 := by
    simpa only [Int.cast_ofNat, Nat.cast_ofNat] using unit_prime_cast (q:=1033) (by norm_num1) h1033
  rcases square_pair 5 (41*101) 1033 hA hB hC with h | h | h
  · exact ⟨(51,26),by decide, scaled_square_chart 51 26 7414 (5*(41*101)) (by norm_num [quartic])
      (lift_square_symbol hTwo (by rw [Int.cast_mul]; exact mul_ne_zero hA hB) h)⟩
  · exact ⟨(9,5),by decide, scaled_square_chart 9 5 370 (5*1033) (by norm_num [quartic])
      (lift_square_symbol hTwo (by rw [Int.cast_mul]; exact mul_ne_zero hA hC) h)⟩
  · exact ⟨(2,3),by decide, scaled_square_chart 2 3 5 (41*101*1033) (by norm_num [quartic])
      (lift_square_symbol hTwo (by rw [Int.cast_mul]; exact mul_ne_zero hB hC) h)⟩

/-- In affine coordinates, each prime admits a local square above one of
the four rational numbers 51/26, 9/5, 2/3, or 2. -/
theorem every_prime_affine_point (p : ℕ) [Fact p.Prime] :
    ∃ t ∈ ([51/26,9/5,2/3,2] : List ℚ),
      ∃ y : ℚ_[p], y^2 = quartic (t:ℚ_[p]) 1 := by
  obtain ⟨⟨x,v⟩,hc,z,hz⟩ := four_charts_cover p
  have hx : (x:ℚ)/v ∈ ([51/26,9/5,2/3,2] : List ℚ) ∧ v ≠ 0 := by
    simp only [localCharts, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num
  refine ⟨(x:ℚ)/v, hx.1, z/(v:ℚ_[p])^2, ?_⟩
  have hv : (v:ℚ_[p]) ≠ 0 := Int.cast_ne_zero.mpr hx.2
  push_cast
  have he : quartic ((x:ℚ_[p])/v) 1 * v^4 = quartic (x:ℚ_[p]) (v:ℚ_[p]) := by
    unfold quartic
    field_simp [hv]
    ring
  rw [div_pow, ← pow_mul, show 2*2=4 by decide]
  exact (div_eq_iff (pow_ne_zero 4 hv)).2 (hz.trans he.symm)

end SuperZeta.Hasse
