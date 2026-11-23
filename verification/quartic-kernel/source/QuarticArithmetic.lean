import QuarticKernel

namespace QuarticKernel

/-- Binary exponentiation with remainder taken at every multiplication. The
exponent bound in the soundness lemma accounts for the finite bit count. -/
def modPower (p a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % p
  | k+1, e =>
    let half := modPower p (a*a % p) k (e/2)
    if e % 2 = 0 then half else a*half % p

private theorem modPower_lt {p : ℕ} (hp : 0 < p) (a k e : ℕ) :
    modPower p a k e < p := by
  induction k generalizing a e with
  | zero => exact Nat.mod_lt _ hp
  | succ k ih =>
    rw [modPower]
    split
    · exact ih _ _
    · exact Nat.mod_lt _ hp

private theorem modPower_correct (p a k e : ℕ) (he : e < 2^k) :
    (modPower p a k e : ZMod p) = (a : ZMod p)^e := by
  induction k generalizing a e with
  | zero =>
    have h : e = 0 := by simpa using he
    simp [modPower, h, ZMod.natCast_mod]
  | succ k ih =>
    have hh : e/2 < 2^k := by
      rw [pow_succ] at he
      omega
    rw [modPower]
    split
    next h =>
      rw [ih _ _ hh, ZMod.natCast_mod, Nat.cast_mul, ← pow_two, ← pow_mul]
      congr 1
      omega
    next h =>
      rw [ZMod.natCast_mod, Nat.cast_mul, ih _ _ hh,
        ZMod.natCast_mod, Nat.cast_mul, ← pow_two, ← pow_mul, ← pow_succ']
      congr 1
      omega

def evalLegendre (p a : ℕ) : ℤ :=
  let r := modPower p a 31 (p/2)
  if r = 0 then 0 else if r = 1 then 1 else -1

private theorem evalLegendre_eq (p a : ℕ) [Fact p.Prime] (hp : 2 < p)
    (hb : p/2 < 2^31) : evalLegendre p a = legendreSym p a := by
  let r := modPower p a 31 (p/2)
  have hr : r < p := modPower_lt (by omega) a 31 (p/2)
  have hcast : (r : ZMod p) = (legendreSym p a : ZMod p) := by
    rw [legendreSym.eq_pow, Int.cast_natCast]
    exact modPower_correct p a 31 (p/2) hb
  have hs : legendreSym p (a : ℤ) = 0 ∨ legendreSym p (a : ℤ) = 1 ∨
      legendreSym p (a : ℤ) = -1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym]
    exact jacobiSym.trichotomy _ _
  change (if r = 0 then 0 else if r = 1 then 1 else -1) = _
  rcases hs with hz | ho | hn
  · rw [hz, Int.cast_zero] at hcast
    have hr0 : r = 0 := by
      simpa only [ZMod.val_natCast_of_lt hr, ZMod.val_zero] using congrArg ZMod.val hcast
    simp [hr0, hz]
  · rw [ho, Int.cast_one] at hcast
    have hr1 : r = 1 := by
      have h := congrArg ZMod.val hcast
      rw [ZMod.val_natCast_of_lt hr, ← Nat.cast_one, ZMod.val_natCast_of_lt (by omega : 1 < p)] at h
      exact h
    simp [hr1, ho]
  · rw [hn, Int.cast_neg, Int.cast_one] at hcast
    have hvalue : (-1 : ZMod p).val = p-1 := by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
      simpa only [Nat.succ_sub_one] using ZMod.val_neg_one q
    have hr' := congrArg ZMod.val hcast
    rw [ZMod.val_natCast_of_lt hr, hvalue] at hr'
    have hr0 : r ≠ 0 := by omega
    have hr1 : r ≠ 1 := by omega
    simp [hr0, hr1, hn]

def evalMark (a b : ℕ) : ℤ :=
  evalLegendre 41 (a+32*b) * evalLegendre 457 (a+109*b) *
    evalLegendre 1414835497 (a+516876951*b)

theorem evalMark_eq (a b : ℕ) :
    evalMark a b = SuperZeta.FieldWeights.conductorReading a b := by
  have prime41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  have prime457 : Fact (Nat.Prime 457) := ⟨by norm_num⟩
  have prime1414835497 : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩
  unfold evalMark SuperZeta.FieldWeights.conductorReading
  rw [evalLegendre_eq 41 _ (by decide) (by decide),
      evalLegendre_eq 457 _ (by decide) (by decide),
      evalLegendre_eq 1414835497 _ (by decide) (by decide)]
  push_cast
  simp only [mul_comm (32 : ℤ), mul_comm (109 : ℤ), mul_comm (516876951 : ℤ)]

theorem evalLegendre_eq_jacobi (p a : ℕ) [Fact p.Prime] (hp : 2 < p)
    (hb : p/2 < 2^31) : evalLegendre p a = jacobiSym (a:ℤ) p := by
  rw [evalLegendre_eq p a hp hb, jacobiSym.legendreSym.to_jacobiSym]

def evalCoeff (n : ℕ) : ℤ := (Finset.range n.sqrt).sum (fun j =>
  let a := j+1
  let b := (n-a*a).sqrt
  if a*a+b*b = n then evalMark a b else 0)

theorem evalCoeff_eq (n : ℕ) : evalCoeff n = coeff n := by
  unfold evalCoeff coeff
  apply Finset.sum_congr rfl
  intro i _
  simp [row, evalMark_eq]

theorem coeff_seventy_three : coeff 73 = 0 := by
  rw [← evalCoeff_eq]
  decide

#print axioms evalMark_eq
#print axioms coeff_seventy_three

end QuarticKernel
