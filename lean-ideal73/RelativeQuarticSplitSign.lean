import RelativeQuarticSplitEuler
import GaussianReciprocityNorm
import Mathlib.NumberTheory.SumTwoSquares

/-! The oriented split-prime sign via ordinary Jacobi reciprocity. The
projection is the real coordinate of `δ * conj z` and retains the sign of
the imaginary coordinate of the Gaussian generator `z`. -/

namespace QuarticModel

open scoped Classical

private abbrev A : ℤ := -5045155
private abbrev B : ℤ := 1027708
private abbrev D : ℕ := 26509772707289

local instance : Fact (Nat.Prime 41) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 457) := ⟨by norm_num⟩
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩

private theorem squarefree_D : Squarefree D := by
  rw [show D = 41*457*1414835497 by decide,
    Nat.squarefree_mul (by decide : (41*457).Coprime 1414835497),
    Nat.squarefree_mul (by decide : (41 : ℕ).Coprime 457)]
  exact ⟨⟨(Fact.out : Nat.Prime 41).squarefree, (Fact.out : Nat.Prime 457).squarefree⟩,
    (Fact.out : Nat.Prime 1414835497).squarefree⟩

private theorem quadraticChar_at_projection (p : ℕ) [Fact p.Prime]
    (r : ZMod p) (u v x y : ℤ) (hr : (u : ZMod p)*r = (v : ZMod p)) :
    jacobiSym (u*x+v*y) p = jacobiSym u p * quadraticChar (ZMod p) ((x : ZMod p)+(y : ZMod p)*r) := by
  have h : (((u*x+v*y : ℤ) : ZMod p)) = (u : ZMod p)*((x : ZMod p)+(y : ZMod p)*r) := by
    push_cast
    linear_combination -(y : ZMod p)*hr
  rw [← jacobiSym.legendreSym.to_jacobiSym p (u*x+v*y), legendreSym, h, map_mul]
  change legendreSym p u * _ = _
  rw [jacobiSym.legendreSym.to_jacobiSym]

private theorem jacobiSym_conductor_projection (q : ℕ) [Fact q.Prime]
    (t m n : ℤ) (ht : (A : ZMod q)*(t : ZMod q) = (B : ZMod q)) :
    jacobiSym (A*m+B*n) q = jacobiSym A q * jacobiSym (m+n*t) q := by
  rw [← jacobiSym.legendreSym.to_jacobiSym q (m+n*t), legendreSym]
  push_cast
  exact quadraticChar_at_projection q (t : ZMod q) A B m n ht

theorem archivedGaussianSign_eq_norm_projection (z : GaussianInt) :
    archivedGaussianSign z = jacobiSym (A*z.re+B*z.im) D := by
  unfold archivedGaussianSign
  have h₁ : jacobiSym A 41 = 1 := by norm_num [A]
  have h₂ : jacobiSym A 457 = -1 := by norm_num [A]
  have h₃ : jacobiSym A 1414835497 = -1 := by norm_num [A]
  rw [show D = 41*457*1414835497 by decide, jacobiSym.mul_right, jacobiSym.mul_right,
    jacobiSym_conductor_projection 41 32 z.re z.im (by decide),
    jacobiSym_conductor_projection 457 109 z.re z.im (by decide),
    jacobiSym_conductor_projection 1414835497 516876951 z.re z.im (by decide), h₁, h₂, h₃]
  ring

/-- Equality at the specific residue map where the chosen generator
vanishes. Its conjugate uses the opposite residue of `i`. -/
theorem archivedGaussianSign_at_split_root {p : ℕ} [Fact p.Prime]
    (hp : p % 4 = 1) (hcop : p.Coprime D)
    (r : ZMod p) (hr : r^2 = -1) (z : GaussianInt) (hzOdd : Odd z.re)
    (hzNorm : (p : ℤ) = z.re^2+z.im^2) (hz : gaussianResidue r hr z = 0) :
    quadraticChar (ZMod p) ((-5045155 : ZMod p)+1027708*r) = archivedGaussianSign z := by
  have hz₀ : (z.re : ZMod p) + (z.im : ZMod p)*r = 0 := hz
  have hproj : (z.re : ZMod p)*r = (z.im : ZMod p) := by
    linear_combination r*hz₀-(z.im : ZMod p)*hr
  have hRe : jacobiSym z.re p = 1 :=
    jacobiSym_coordinate_at_norm hzNorm (Fact.out : p.Prime).squarefree hp hzOdd.natAbs
  have he : ((p*D : ℕ) : ℤ) = (A*z.re+B*z.im)^2 + (B*z.re-A*z.im)^2 := by
    rw [Nat.cast_mul, hzNorm]
    unfold A B D
    ring
  have hsf : Squarefree (p*D) :=
    (Nat.squarefree_mul hcop).mpr ⟨(Fact.out : p.Prime).squarefree, squarefree_D⟩
  have hOdd : Odd (A*z.re+B*z.im).natAbs :=
    ((show Odd A by decide).mul hzOdd |>.add_even ((show Even B by decide).mul_right _)).natAbs
  have hχ := quadraticChar_at_projection p r z.re z.im A B hproj
  rw [hRe, one_mul, mul_comm z.re A, mul_comm z.im B] at hχ
  rw [archivedGaussianSign_eq_norm_projection, ← jacobiSym_coordinate_at_norm_factors he hsf hp (by decide) hOdd]
  simpa only [A, B, Int.cast_neg, Int.cast_ofNat] using hχ.symm

private theorem sums_of_two_squares_odd_first {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1) :
    ∃ m n : ℕ, Odd m ∧ m^2+n^2 = p := by
  obtain ⟨m, n, h⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  by_cases hm : Odd m
  · exact ⟨m, n, hm, h⟩
  · have hn : Odd n := by
      by_contra hNot
      have he := ((Nat.not_odd_iff_even.mp hm).pow_of_ne_zero two_ne_zero).add
        ((Nat.not_odd_iff_even.mp hNot).pow_of_ne_zero two_ne_zero)
      rw [h] at he
      exact (Nat.not_odd_iff_even.mpr he) (Nat.odd_iff.mpr (by omega))
    exact ⟨n, m, hn, (add_comm ..).trans h⟩

/-- For each marked root of `-1`, choose the norm-`p` Gaussian generator
vanishing at that root, with an odd real coordinate. -/
theorem gaussian_split_generator_at_root {p : ℕ} [Fact p.Prime] (hp : p % 4 = 1)
    (r : ZMod p) (hr : r^2 = -1) :
    ∃ m n : ℤ, Odd m ∧ (p : ℤ) = m^2+n^2 ∧ (m : ZMod p)+(n : ZMod p)*r = 0 := by
  obtain ⟨m, n, hm, hn⟩ := sums_of_two_squares_odd_first hp
  have he : ((m : ℤ)^2+(n : ℤ)^2) = (p : ℤ) := by exact_mod_cast hn
  have hz : ((m : ZMod p)^2+(n : ZMod p)^2) = 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, ← Nat.cast_add, hn, ZMod.natCast_self]
  have hmul : ((m : ZMod p)+(n : ZMod p)*r) * ((m : ZMod p)-(n : ZMod p)*r) = 0 := by
    linear_combination hz-(n : ZMod p)^2*hr
  rcases mul_eq_zero.mp hmul with h | h
  · exact ⟨m,n,by exact_mod_cast hm,he.symm,by simpa only [Int.cast_natCast] using h⟩
  · refine ⟨m,-(n : ℤ),by exact_mod_cast hm,by simpa only [neg_sq] using he.symm,?_⟩
    simpa only [Int.cast_natCast, Int.cast_neg, neg_mul, ← sub_eq_add_neg] using h

open FieldCoefficientTransfer in
/-- The two generators in this Euler identity are the conjugate pair of
norm `p`, with their individual residue maps explicitly identified. -/
theorem fieldLocalEulerSeries_mul_archived_split_coprime (p : ℕ) [Fact p.Prime]
    (hp : p % 4 = 1) (hcop : p.Coprime D) (r : ZMod p) (hr : r^2 = -1) :
    ∃ m n : ℤ, (p : ℤ) = m^2+n^2 ∧
      gaussianPrimeAt r hr = Ideal.span {(⟨m,n⟩ : GaussianInt)} ∧
      (∃ hn : (-r)^2 = -1, gaussianPrimeAt (-r) hn = Ideal.span {(⟨m,-n⟩ : GaussianInt)}) ∧
      let T := (PowerSeries.X : PowerSeries ℂ)
      fieldLocalEulerSeries K p * ((1-T)^2 *
        ((1-(archivedGaussianSign ⟨m,n⟩ : PowerSeries ℂ)*T)*
          (1-(archivedGaussianSign ⟨m,-n⟩ : PowerSeries ℂ)*T))) = 1 := by
  obtain ⟨m,n,hm,hn,hPos⟩ := gaussian_split_generator_at_root hp r hr
  have hnRoot : (-r)^2 = -1 := by simpa only [neg_sq] using hr
  have hNeg : (m : ZMod p)+((-n : ℤ) : ZMod p)*(-r) = 0 := by
    simpa only [Int.cast_neg, neg_mul_neg] using hPos
  have hNorm (x : ℤ) (hx : (p : ℤ) = m^2+x^2) :
      (⟨m,x⟩ : GaussianInt).norm.natAbs = p := by
    rw [← Int.natAbs_natCast p, hx]
    congr 1
    simp only [Zsqrtd.norm_def]
    ring
  have hcNeg : (p : ℤ) = m^2+(-n)^2 := by simpa only [neg_sq] using hn
  refine ⟨m,n,hn,gaussianPrimeAt_eq_span r hr _ (hNorm _ hn) hPos,
    ⟨hnRoot,gaussianPrimeAt_eq_span (-r) hnRoot _ (hNorm _ hcNeg) hNeg⟩,?_⟩
  exact fieldLocalEulerSeries_mul_archived_split_denominator p hp r hr _ _
    (archivedGaussianSign_at_split_root hp hcop r hr ⟨m,n⟩ hm hn hPos)
    (archivedGaussianSign_at_split_root hp hcop (-r) hnRoot ⟨m,-n⟩ hm hcNeg hNeg)

#print axioms archivedGaussianSign_eq_norm_projection
#print axioms archivedGaussianSign_at_split_root
#print axioms gaussian_split_generator_at_root
#print axioms fieldLocalEulerSeries_mul_archived_split_coprime

end QuarticModel
