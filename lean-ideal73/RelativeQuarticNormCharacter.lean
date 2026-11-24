import RelativeQuarticSplitting
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-! The rational norm character determines the unordered pair of relative
signs when the two Gaussian primes have opposite signs. -/

namespace QuarticModel

local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

/-- The conjugate product of the archived three conductor symbols. -/
noncomputable def rationalNormSign (p : ℕ) : ℤ :=
  legendreSym 41 p * legendreSym 457 p * legendreSym 1414835497 p

theorem rationalNormSign_reciprocity (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 26509772707289 = rationalNormSign p := by
  unfold rationalNormSign
  have h41 : legendreSym p 41 = legendreSym 41 p := by
    simpa only [Nat.cast_ofNat] using
      (legendreSym.quadratic_reciprocity_one_mod_four (p := 41) (q := p) (by decide) hp)
  have h457 : legendreSym p 457 = legendreSym 457 p := by
    simpa only [Nat.cast_ofNat] using
      (legendreSym.quadratic_reciprocity_one_mod_four (p := 457) (q := p) (by decide) hp)
  have hbig : legendreSym p 1414835497 = legendreSym 1414835497 p := by
    simpa only [Nat.cast_ofNat] using
      (legendreSym.quadratic_reciprocity_one_mod_four (p := 1414835497) (q := p) (by decide) hp)
  rw [← show (41 : ℤ)*457*1414835497 = 26509772707289 by decide,
    legendreSym.mul, legendreSym.mul, h41, h457, hbig]

theorem discriminant_pair_product {p : ℕ} [Fact p.Prime] (r : ZMod p) (hr : r^2 = -1) :
    ((-5045155 : ZMod p)+1027708*r) * ((-5045155 : ZMod p)-1027708*r) =
      (26509772707289 : ZMod p) := by
  linear_combination -(1027708 : ZMod p)^2 * hr

theorem discriminant_pair_sign_product {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) :
    quadraticChar (ZMod p) ((-5045155 : ZMod p)+1027708*r) *
      quadraticChar (ZMod p) ((-5045155 : ZMod p)-1027708*r) = rationalNormSign p := by
  rw [← map_mul, discriminant_pair_product r hr]
  simpa only [legendreSym, Int.cast_ofNat] using rationalNormSign_reciprocity p hp

theorem discriminant_pair_opposite {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (r : ZMod p) (hr : r^2 = -1) (h : rationalNormSign p = -1) :
    (quadraticChar (ZMod p) ((-5045155 : ZMod p)+1027708*r),
      quadraticChar (ZMod p) ((-5045155 : ZMod p)-1027708*r)) ∈
        ({(1,-1), (-1,1)} : Set (ℤ × ℤ)) := by
  have hprod := (discriminant_pair_sign_product hp r hr).trans h
  have h₀ : (-5045155 : ZMod p)+1027708*r ≠ 0 := by
    intro hzero
    rw [hzero, quadraticChar_zero, zero_mul] at hprod
    norm_num at hprod
  rcases quadraticChar_dichotomy h₀ with hpos | hneg
  · rw [hpos, one_mul] at hprod
    simp [hpos, hprod]
  · rw [hneg, neg_one_mul, neg_inj] at hprod
    simp [hneg, hprod]

#print axioms rationalNormSign_reciprocity
#print axioms discriminant_pair_sign_product
#print axioms discriminant_pair_opposite

end QuarticModel
