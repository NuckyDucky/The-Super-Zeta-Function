import GaussianRawPrimeWindow

/-! The degree-one prime weights can be read over either quadratic
base. Over the real quadratic base the radicand is `2(a+√(a²+b²))`. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Finset QuarticModel

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Sum a reading over both roots available in the residue field. -/
def quadraticRootSum (q : F) (f : F → ℤ) : ℤ :=
  ∑ r ∈ univ.filter (fun r => r ^ 2 = q), f r

private theorem quadraticRootSum_of_root {q r : F} (h2 : (2 : F) ≠ 0)
    (hq : q ≠ 0) (hr : r ^ 2 = q) (f : F → ℤ) :
    quadraticRootSum q f = f r + f (-r) := by
  have hr₀ : r ≠ 0 := fun h => hq (by rw [← hr, h]; norm_num)
  have hd : r ≠ -r := by
    intro h
    exact mul_ne_zero h2 hr₀ (by linear_combination h)
  have H : univ.filter (fun x : F => x ^ 2 = q) = {r, -r} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    rw [← hr, (Commute.all x r).sq_eq_sq_iff_eq_or_eq_neg]
  rw [quadraticRootSum, H, sum_insert (by simpa only [mem_singleton] using hd), sum_singleton]

private theorem quadraticRootSum_of_no_root {q : F} (h : ¬∃ r : F, r ^ 2 = q)
    (f : F → ℤ) : quadraticRootSum q f = 0 := by
  apply sum_eq_zero
  intro r hr
  exact (h ⟨r, (mem_filter.mp hr).2⟩).elim

private theorem signedPair_sum_zero {u v : ℤ} (hu : u = 1 ∨ u = -1)
    (h : u * v = -1) : u + v = 0 := by
  rcases hu with rfl | rfl <;> linarith

omit [Fintype F] [DecidableEq F] in
private theorem not_isSquare_of_no_root {q : F} (h : ¬∃ r : F, r ^ 2 = q) :
    ¬ IsSquare q := by
  rintro ⟨r, hr⟩
  exact h ⟨r, by simpa only [pow_two] using hr.symm⟩

/-- The two quadratic bases give the same sum of the degree-one signs.
When both split, the identity is the square of `a + br + s`. If just one
base splits, its two signs have product `-1` and cancel. -/
private theorem quadraticRootSum_gaussian_real_eq_of_ne_zero (a b : F) (h2 : (2 : F) ≠ 0)
    (hb : b ≠ 0) (hD : a ^ 2 + b ^ 2 ≠ 0) :
    quadraticRootSum (-1 : F) (fun r => quadraticChar F (a + b * r)) =
      quadraticRootSum (a ^ 2 + b ^ 2) (fun s => quadraticChar F (2 * (a + s))) := by
  have hm : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hG {r : F} (hr : r ^ 2 = -1) :
      (a + b * r) * (a + b * -r) = a ^ 2 + b ^ 2 := by
    linear_combination -b ^ 2 * hr
  have hR {s : F} (hs : s ^ 2 = a ^ 2 + b ^ 2) :
      (2 * (a + s)) * (2 * (a + -s)) = -(2 * b) ^ 2 := by
    linear_combination -4 * hs
  have hG₀ {r : F} (hr : r ^ 2 = -1) : a + b * r ≠ 0 := by
    intro hz
    exact hD (by rw [← hG hr, hz, zero_mul])
  have hR₀ {s : F} (hs : s ^ 2 = a ^ 2 + b ^ 2) : 2 * (a + s) ≠ 0 := by
    intro hz
    exact neg_ne_zero.mpr (pow_ne_zero 2 (mul_ne_zero h2 hb)) (by rw [← hR hs, hz, zero_mul])
  have hSame {r s : F} (hr : r ^ 2 = -1) (hs : s ^ 2 = a ^ 2 + b ^ 2) :
      quadraticChar F (a + b * r) = quadraticChar F (2 * (a + s)) := by
    have he : (a + b * r + s) ^ 2 = (a + b * r) * (2 * (a + s)) := by
      linear_combination b ^ 2 * hr + hs
    have hn : a + b * r + s ≠ 0 := by
      intro hz
      exact mul_ne_zero (hG₀ hr) (hR₀ hs) (by rw [← he, hz]; norm_num)
    have h := congrArg (quadraticChar F) he
    rw [quadraticChar_sq_one' hn, map_mul] at h
    rcases quadraticChar_dichotomy (hG₀ hr) with hpos | hneg
    · rw [hpos, one_mul] at h
      exact hpos.trans h
    · rw [hneg, neg_one_mul] at h
      linarith
  by_cases hi : ∃ r : F, r ^ 2 = -1
  · obtain ⟨r, hr⟩ := hi
    rw [quadraticRootSum_of_root h2 hm hr]
    by_cases hd : ∃ s : F, s ^ 2 = a ^ 2 + b ^ 2
    · obtain ⟨s, hs⟩ := hd
      rw [quadraticRootSum_of_root h2 hD hs, hSame hr hs,
        hSame (by simpa only [neg_sq] using hr : (-r) ^ 2 = -1)
          (by simpa only [neg_sq] using hs : (-s) ^ 2 = a ^ 2 + b ^ 2)]
    · rw [quadraticRootSum_of_no_root hd]
      apply signedPair_sum_zero (quadraticChar_dichotomy (hG₀ hr))
      rw [← map_mul, hG hr, quadraticChar_neg_one_iff_not_isSquare]
      exact not_isSquare_of_no_root hd
  · rw [quadraticRootSum_of_no_root hi]
    by_cases hd : ∃ s : F, s ^ 2 = a ^ 2 + b ^ 2
    · obtain ⟨s, hs⟩ := hd
      rw [quadraticRootSum_of_root h2 hD hs, eq_comm]
      apply signedPair_sum_zero (quadraticChar_dichotomy (hR₀ hs))
      rw [← map_mul, hR hs, neg_eq_neg_one_mul, map_mul,
        quadraticChar_sq_one' (mul_ne_zero h2 hb), mul_one,
        quadraticChar_neg_one_iff_not_isSquare]
      exact not_isSquare_of_no_root hi
    · rw [quadraticRootSum_of_no_root hd]

/-- The two radicands at a norm root give the same square class over
the real quadratic base. Use the second if the first reduces to zero. -/
def realQuadraticRadicand (a s : F) : F :=
  if a + s = 0 then 2 * (s - a) else 2 * (a + s)

theorem quadraticRootSum_gaussian_real_eq (a b : F) (h2 : (2 : F) ≠ 0)
    (hD : a ^ 2 + b ^ 2 ≠ 0) :
    quadraticRootSum (-1 : F) (fun r => quadraticChar F (a + b * r)) =
      quadraticRootSum (a ^ 2 + b ^ 2) (fun s => quadraticChar F (realQuadraticRadicand a s)) := by
  by_cases hb : b = 0
  · subst b
    simp only [zero_mul, add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hD ⊢
    have ha : a ≠ 0 := fun h => hD (by rw [h]; norm_num)
    rw [quadraticRootSum_of_root h2 hD rfl]
    have hsum : a + a ≠ 0 := fun h => mul_ne_zero h2 ha (by linear_combination h)
    have hplus : realQuadraticRadicand a a = 2 ^ 2 * a := by
      rw [realQuadraticRadicand, if_neg hsum]
      ring
    have hminus : realQuadraticRadicand a (-a) = 2 ^ 2 * -a := by
      rw [realQuadraticRadicand, if_pos (add_neg_cancel a)]
      ring
    rw [hplus, hminus, map_mul, map_mul, quadraticChar_sq_one' h2, one_mul, one_mul,
      neg_eq_neg_one_mul (a := a), map_mul]
    by_cases hi : ∃ r : F, r ^ 2 = -1
    · obtain ⟨r, hr⟩ := hi
      rw [quadraticRootSum_of_root h2 (neg_ne_zero.mpr one_ne_zero) hr]
      have hr₀ : r ≠ 0 := by
        intro hh
        rw [hh] at hr
        norm_num at hr
      have hs : quadraticChar F (-1) = 1 := by rw [← hr, quadraticChar_sq_one' hr₀]
      rw [hs, one_mul]
    · rw [quadraticRootSum_of_no_root hi,
        quadraticChar_neg_one_iff_not_isSquare.mpr (not_isSquare_of_no_root hi), neg_one_mul,
        add_neg_cancel]
  · rw [quadraticRootSum_gaussian_real_eq_of_ne_zero a b h2 hb hD]
    apply sum_congr rfl
    intro s hs
    have hs' : s ^ 2 = a ^ 2 + b ^ 2 := (mem_filter.mp hs).2
    have he : (2 * (a + s)) * (2 * (a + -s)) = -(2 * b) ^ 2 := by
      linear_combination -4 * hs'
    have hn : a + s ≠ 0 := by
      intro hz
      exact neg_ne_zero.mpr (pow_ne_zero 2 (mul_ne_zero h2 hb)) (by
        rw [← he, hz, mul_zero, zero_mul])
    change quadraticChar F (2 * (a + s)) = quadraticChar F (realQuadraticRadicand a s)
    rw [realQuadraticRadicand, if_neg hn]

/-- The archived Gaussian prime coefficient is the sum from the
real quadratic base at every prime away from two and the conductor. -/
theorem archivedGaussianPrimeWeight_real_quadratic {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hD : p.Coprime 26509772707289) :
    archivedGaussianPrimeWeight p =
      (quadraticRootSum (26509772707289 : ZMod p)
        (fun s => quadraticChar (ZMod p) (realQuadraticRadicand (-5045155) s)) : ℝ) := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    simpa only [Nat.cast_ofNat] using (ZMod.natCast_eq_zero_iff 2 p).not.mpr
      ((Nat.dvd_prime_two_le Nat.prime_two (Fact.out : p.Prime).two_le).not.mpr hp)
  have hform : (-5045155 : ZMod p) ^ 2 + (1027708 : ZMod p) ^ 2 = 26509772707289 := by
    ring
  have hEq := quadraticRootSum_gaussian_real_eq (-5045155 : ZMod p) 1027708 h2
    (hform ▸ norm_discriminant_ne_zero hD)
  rw [hform] at hEq
  rw [← hEq]
  by_cases h₃ : p % 4 = 3
  · rw [archivedGaussianPrimeWeight_inert h₃, quadraticRootSum_of_no_root]
    · exact Int.cast_zero.symm
    · rintro ⟨r, hr⟩
      exact (ZMod.exists_sq_eq_neg_one_iff.mp ⟨r, by simpa only [pow_two] using hr.symm⟩) h₃
  · obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr h₃
    have hr' : r ^ 2 = -1 := by simpa only [pow_two] using hr.symm
    rw [archivedGaussianPrimeWeight_split hp r hr',
      quadraticRootSum_of_root h2 (neg_ne_zero.mpr one_ne_zero) hr', Int.cast_add]
    simp only [mul_neg, sub_eq_add_neg]

theorem archivedRealQuadratic_radicands_sign :
    0 < 2 * ((-5045155 : ℝ) + Real.sqrt 26509772707289) ∧
      2 * ((-5045155 : ℝ) - Real.sqrt 26509772707289) < 0 := by
  have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ (5045155 : ℝ) ^ 2)
    (by norm_num : (5045155 : ℝ) ^ 2 < 26509772707289)
  rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5045155)] at h
  constructor <;> linarith

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 11) := ⟨by decide⟩
local instance : Fact (Nat.Prime 13) := ⟨by decide⟩
local instance : Fact (Nat.Prime 73) := ⟨by decide⟩

theorem archivedRealQuadratic_readings :
    quadraticRootSum (26509772707289 : ZMod 5)
        (fun s => quadraticChar (ZMod 5) (realQuadraticRadicand (-5045155) s)) = 2 ∧
    quadraticRootSum (26509772707289 : ZMod 11)
        (fun s => quadraticChar (ZMod 11) (realQuadraticRadicand (-5045155) s)) = 0 ∧
    quadraticRootSum (26509772707289 : ZMod 13)
        (fun s => quadraticChar (ZMod 13) (realQuadraticRadicand (-5045155) s)) = -2 ∧
    quadraticRootSum (26509772707289 : ZMod 73)
        (fun s => quadraticChar (ZMod 73) (realQuadraticRadicand (-5045155) s)) = 0 := by
  decide +kernel

/-- Keep the archived coefficients at the finitely many excluded primes. -/
def archivedRealQuadraticPrimeWeight (p : ℕ) : ℝ :=
  if h : p.Prime ∧ p ≠ 2 ∧ p.Coprime 26509772707289 then
    letI : Fact p.Prime := ⟨h.1⟩
    (quadraticRootSum (26509772707289 : ZMod p)
      (fun s => quadraticChar (ZMod p) (realQuadraticRadicand (-5045155) s)) : ℝ)
  else archivedGaussianPrimeWeight p

theorem archivedRealQuadraticPrimeWeight_eq (p : ℕ) :
    archivedRealQuadraticPrimeWeight p = archivedGaussianPrimeWeight p := by
  unfold archivedRealQuadraticPrimeWeight
  split_ifs with h
  · let _ : Fact p.Prime := ⟨h.1⟩
    exact (archivedGaussianPrimeWeight_real_quadratic h.2.1 h.2.2).symm
  · rfl

theorem archivedGaussianPrimeHalfWindow_real_quadratic (x : ℝ) :
    archivedGaussianPrimeHalfWindow x =
      -(∑ n ∈ range (⌊x⌋₊ + 1),
        (vonMangoldt n * (if n.Prime then archivedRealQuadraticPrimeWeight n else 0)) *
          divisorWindowMultiplicity x n) -
      (x / 2) * ((logDeriv archivedGaussianFactor 1).re + gaussianHigherPrimeLinearCoefficient) := by
  simp only [archivedRealQuadraticPrimeWeight_eq, archivedGaussianPrimeHalfWindow]

#print axioms quadraticRootSum_gaussian_real_eq
#print axioms archivedGaussianPrimeWeight_real_quadratic
#print axioms archivedRealQuadratic_radicands_sign
#print axioms archivedRealQuadratic_readings
#print axioms archivedGaussianPrimeHalfWindow_real_quadratic

end
end AlpogeSuperZeta
