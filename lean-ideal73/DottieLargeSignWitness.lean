import DottieStructuralJacobi

/-! Check a square-root witness for the largest conductor prime. The
low bit marks the nonsquare case, where multiplying by 5 gives a square. -/

namespace QuarticModel

private abbrev p : ℕ := 1414835497
set_option maxRecDepth 60000 in
local instance : Fact (Nat.Prime p) := ⟨by norm_num [p]⟩

open private structuralJacobi structuralJacobi_eq from DottieStructuralJacobi
open private fastJacobiSym.eq from Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

private theorem five_symbol : jacobiSym 5 p = -1 := by
  rw [fastJacobiSym.eq, ← structuralJacobi_eq 5 p (by decide) (by decide)]
  decide +kernel

def dottieLargeSignWitness (a code : ℕ) : Option ℤ :=
  let r := a % p
  if r = 0 then some 0
  else
    let square := ((code/2)^2) % p
    if code % 2 = 0 then
      if square = r then some 1 else none
    else
      if square = (5*r)%p then some (-1) else none

private theorem jacobi_one_of_square_remainder (a root : ℕ) (ha : a % p ≠ 0)
    (hroot : root^2 % p = a % p) : jacobiSym (a : ℤ) p = 1 := by
  have haz : (a : ZMod p) ≠ 0 := by
    intro h
    exact ha (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff a p).1 h))
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  apply (legendreSym.eq_one_iff' p haz).2
  refine ⟨(root : ZMod p), ?_⟩
  have h := congrArg (fun n : ℕ => (n : ZMod p)) hroot
  simpa only [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_mul, pow_two] using h.symm

theorem dottie_large_sign_of_witness {a code : ℕ} {s : ℤ}
    (h : dottieLargeSignWitness a code = some s) :
    jacobiSym (a : ℤ) p = s := by
  by_cases hr : a % p = 0
  · rw [dottieLargeSignWitness, if_pos hr] at h
    cases h
    rw [jacobiSym.mod_left, ← Int.natCast_mod, hr]
    exact jacobiSym.zero_left (by decide)
  by_cases hpos : code % 2 = 0
  · by_cases hsq : (code/2)^2%p = a%p
    · rw [dottieLargeSignWitness, if_neg hr, if_pos hpos, if_pos hsq] at h
      cases h
      exact jacobi_one_of_square_remainder a (code/2) hr hsq
    · rw [dottieLargeSignWitness, if_neg hr, if_pos hpos, if_neg hsq] at h
      contradiction
  · by_cases hsq : (code/2)^2%p = (5*(a%p))%p
    swap
    · rw [dottieLargeSignWitness, if_neg hr, if_neg hpos, if_neg hsq] at h
      contradiction
    rw [dottieLargeSignWitness, if_neg hr, if_neg hpos, if_pos hsq] at h
    cases h
    have hmod : (5*a)%p = (5*(a%p))%p :=
      (Nat.mul_mod 5 a p).trans (by rw [Nat.mul_mod 5 (a%p) p, Nat.mod_mod])
    have h5 : (5 : ZMod p) ≠ 0 := by decide +kernel
    have ha : (a : ZMod p) ≠ 0 := by
      intro he
      exact hr (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff a p).1 he))
    have hnonzero : (5*a)%p ≠ 0 := by
      intro he
      have hz := (ZMod.natCast_eq_zero_iff (5*a) p).2 (Nat.dvd_of_mod_eq_zero he)
      push_cast at hz
      exact mul_ne_zero h5 ha hz
    have hs := jacobi_one_of_square_remainder (5*a) (code/2) hnonzero (hsq.trans hmod.symm)
    rw [Nat.cast_mul, Nat.cast_ofNat, jacobiSym.mul_left, five_symbol] at hs
    linarith

#print axioms dottie_large_sign_of_witness

end QuarticModel
