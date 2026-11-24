import DottieRowSign

/-! A structurally recursive version of the archived sign. The fuel is the
reduced first argument, an upper bound on the strictly decreasing steps. -/

namespace QuarticModel

open private fastJacobiSym fastJacobiSymAux from Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

private def structuralJacobiAux : ℕ → ℕ → ℕ → Bool → ℤ
  | 0, _, _, _ => 0
  | fuel+1, a, b, flip =>
    if a % 4 = 0 then
      structuralJacobiAux fuel (a/4) b flip
    else if a % 2 = 0 then
      structuralJacobiAux fuel (a/2) b (xor (b % 8 = 3 ∨ b % 8 = 5) flip)
    else if a = 1 then
      if flip then -1 else 1
    else if b % a = 0 then
      0
    else
      structuralJacobiAux fuel (b%a) a (xor (a % 4 = 3 ∧ b % 4 = 3) flip)

private theorem structuralJacobiAux_eq (fuel a b : ℕ) (flip : Bool)
    (ha : 0 < a) (hFuel : a ≤ fuel) :
    structuralJacobiAux fuel a b flip = fastJacobiSymAux a b flip ha := by
  induction fuel generalizing a b flip with
  | zero => omega
  | succ fuel ih =>
    rw [structuralJacobiAux, fastJacobiSymAux.eq_def]
    split_ifs with h4 h2 h1 hmod
    · exact ih _ _ _
        (Nat.div_pos (Nat.le_of_dvd ha (Nat.dvd_of_mod_eq_zero h4)) (by decide))
        (by have := Nat.div_lt_self ha (by decide : 1 < 4); omega)
    · exact ih _ _ _
        (Nat.div_pos (Nat.le_of_dvd ha (Nat.dvd_of_mod_eq_zero h2)) (by decide))
        (by have := Nat.div_lt_self ha (by decide : 1 < 2); omega)
    · rfl
    · rfl
    · rfl
    · exact ih _ _ _ (by omega : 0 < b%a) (by have := Nat.mod_lt b ha; omega)

private def structuralJacobi (a : ℤ) (p : ℕ) : ℤ :=
  let r := (a % (p : ℤ)).natAbs
  structuralJacobiAux r r p false

private theorem structuralJacobi_eq (a : ℤ) (p : ℕ) (hp : 1 < p) (hOdd : p % 2 = 1) :
    structuralJacobi a p = fastJacobiSym a p := by
  rw [fastJacobiSym.eq_def]
  have hp0 : p ≠ 0 := by omega
  have hp1 : p ≠ 1 := by omega
  have hp2 : p % 2 ≠ 0 := by omega
  simp only [hp0, hp1, hp2, dite_false, ite_false]
  split_ifs with hr
  · simp [structuralJacobi, hr, structuralJacobiAux]
  · exact structuralJacobiAux_eq _ _ _ _ (Int.natAbs_pos.mpr hr) le_rfl

def dottieStructuralRowSign (a b : ℤ) : ℤ :=
  structuralJacobi (a + b*32) 41 * structuralJacobi (a + b*109) 457 *
    structuralJacobi (a + b*516876951) 1414835497

theorem dottieStructuralRowSign_eq (a b : ℤ) :
    dottieStructuralRowSign a b = dottieRowSign a b := by
  unfold dottieStructuralRowSign dottieRowSign
  rw [structuralJacobi_eq _ 41 (by decide) (by decide),
    structuralJacobi_eq _ 457 (by decide) (by decide),
    structuralJacobi_eq _ 1414835497 (by decide) (by decide)]

private def residueSign (mask r : ℕ) : ℤ :=
  if r = 0 then 0 else if mask.testBit r then 1 else -1

private def mask41 : ℕ := 1870503675702

private def mask457 : ℕ :=
  359909599818857142715147353490993586009213404814983778920603390482643578515362190085331272383107425747002172966654920655351325885897593822

private theorem verifiedMask41 : ∀ r : Fin 41,
    residueSign mask41 r.val = structuralJacobiAux r.val r.val 41 false := by
  decide +kernel

private theorem verifiedMask457 : ∀ r : Fin 457,
    residueSign mask457 r.val = structuralJacobiAux r.val r.val 457 false := by
  decide +kernel

private theorem emod_natAbs_lt (a : ℤ) {p : ℕ} (hp : 0 < p) :
    (a % (p : ℤ)).natAbs < p := by
  have hp' : 0 < (p : ℤ) := by exact_mod_cast hp
  have hr := Int.emod_lt_of_pos a hp'
  rw [← Int.natAbs_of_nonneg (Int.emod_nonneg a hp'.ne')] at hr
  exact_mod_cast hr

/-- Two checked residue masks replace the small-prime Jacobi recurrences. -/
def dottieLookupRowSign (a b : ℤ) : ℤ :=
  let x := residueSign mask41 ((a+b*32)%41).natAbs
  let y := residueSign mask457 ((a+b*109)%457).natAbs
  if x*y = 0 then 0 else x*y*structuralJacobi (a+b*516876951) 1414835497

theorem dottieLookupRowSign_eq (a b : ℤ) :
    dottieLookupRowSign a b = dottieRowSign a b := by
  have h41 := verifiedMask41 ⟨((a+b*32)%41).natAbs, emod_natAbs_lt _ (by decide : 0 < 41)⟩
  have h457 := verifiedMask457 ⟨((a+b*109)%457).natAbs, emod_natAbs_lt _ (by decide : 0 < 457)⟩
  change residueSign mask41 _ = structuralJacobi (a+b*32) 41 at h41
  change residueSign mask457 _ = structuralJacobi (a+b*109) 457 at h457
  rw [← dottieStructuralRowSign_eq, dottieLookupRowSign]
  rw [h41, h457, dottieStructuralRowSign]
  split_ifs with hz
  · simp only [hz, zero_mul]
  · rfl

#print axioms dottieStructuralRowSign_eq
#print axioms dottieLookupRowSign_eq

end QuarticModel
