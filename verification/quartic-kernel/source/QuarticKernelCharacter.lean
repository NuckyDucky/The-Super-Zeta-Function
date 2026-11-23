import QuarticArithmetic

open NumberTheorySymbols jacobiSym

namespace QuarticKernel

/-- Expose a computed natural as a numeral before passing it to the
next step of a kernel reduction. -/
def forceNat {α : Type} (n : ℕ) (f : ℕ → α) : α :=
  match n with
  | 0 => f 0
  | k+1 => f (k+1)

@[simp] theorem forceNat_eq {α : Type} (n : ℕ) (f : ℕ → α) :
    forceNat n f = f n := by cases n <;> rfl

def forceInt {α : Type} (z : ℤ) (f : ℤ → α) : α :=
  match z with
  | .ofNat k => forceNat k (fun n => f (.ofNat n))
  | .negSucc k => forceNat k (fun n => f (.negSucc n))

@[simp] theorem forceInt_eq {α : Type} (z : ℤ) (f : ℤ → α) :
    forceInt z f = f z := by cases z <;> simp [forceInt]

/-- A structurally recursive Jacobi evaluator for kernel reduction.
The recurrence follows the fast Jacobi implementation in Mathlib. -/
private def jacobiSteps : ℕ → ℕ → ℕ → Bool → ℤ
  | 0, _, _, _ => 0
  | fuel+1, a, b, flip =>
    if a % 4 = 0 then forceNat (a/4) (fun d => jacobiSteps fuel d b flip)
    else if a % 2 = 0 then
      forceNat (a/2) (fun d => jacobiSteps fuel d b (xor (b % 8 = 3 ∨ b % 8 = 5) flip))
    else if a = 1 then (if flip then -1 else 1)
    else forceNat (b%a) (fun r =>
      if r = 0 then 0 else jacobiSteps fuel r a (xor (a % 4 = 3 ∧ b % 4 = 3) flip))

private theorem remainder_twice_le {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    2*(b%a) ≤ b := by
  by_cases h : 2*a ≤ b
  · have hm := Nat.mod_lt b ha
    omega
  · rw [Nat.mod_eq_sub_mod hab.le, Nat.mod_eq_of_lt (by omega)]
    omega

private theorem jacobiSteps_spec {fuel a b : ℕ} {flip : Bool} (hf : a*b < 2^fuel)
    (ha0 : 0 < a) (hab : a < b) (hb2 : b % 2 = 1) (hb1 : 1 < b) :
    jacobiSteps fuel a b flip = if flip then -J(a | b) else J(a | b) := by
  induction fuel generalizing a b flip with
  | zero =>
    have hh := Nat.mul_pos ha0 (Nat.zero_lt_of_lt hab)
    simp only [pow_zero] at hf
    omega
  | succ fuel ih =>
    rw [pow_succ] at hf
    unfold jacobiSteps
    simp only [forceNat_eq]
    split <;> rename_i ha4
    · have hlt := a.div_lt_self ha0 (by decide : 1 < 4)
      have hpos := Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha4)) (by decide : 0 < 4)
      have hp := Nat.mul_le_mul_right b (show 2*(a/4) ≤ a by omega)
      rw [mul_assoc] at hp
      rw [ih (by omega) hpos (hlt.trans hab) hb2 hb1]
      simp only [Int.natCast_ediv, Nat.cast_ofNat, div_four_left (a := a) (mod_cast ha4) hb2]
    split <;> rename_i ha2
    · have hlt := a.div_lt_self ha0 (by decide : 1 < 2)
      have hpos := Nat.div_pos (Nat.le_of_dvd ha0 (Nat.dvd_of_mod_eq_zero ha2)) (by decide : 0 < 2)
      have hp := Nat.mul_le_mul_right b (show 2*(a/2) ≤ a by omega)
      rw [mul_assoc] at hp
      rw [ih (by omega) hpos (hlt.trans hab) hb2 hb1]
      simp only [Int.natCast_ediv, Nat.cast_ofNat, ← even_odd (a := a) (mod_cast ha2) hb2]
      by_cases h : b % 8 = 3 ∨ b % 8 = 5 <;> simp [h]; cases flip <;> simp
    split <;> rename_i ha1
    · subst ha1
      simp
    split <;> rename_i hba
    · suffices J(a | b) = 0 by simp [this]
      refine eq_zero_iff.mpr ⟨fun h ↦ absurd (h ▸ hb1) (by decide), ?_⟩
      rwa [Int.gcd_natCast_natCast, Nat.gcd_eq_left (Nat.dvd_of_mod_eq_zero hba)]
    have hlt := b.mod_lt ha0
    have hp := Nat.mul_le_mul_right a (remainder_twice_le ha0 hab)
    rw [mul_assoc, mul_comm b a] at hp
    rw [ih (by omega) (Nat.pos_of_ne_zero hba) hlt (Nat.mod_two_ne_zero.mp ha2) (by omega)]
    simp only [Int.natCast_mod, ← mod_left]
    rw [← quadratic_reciprocity_if (Nat.mod_two_ne_zero.mp ha2) hb2]
    by_cases h : a % 4 = 3 ∧ b % 4 = 3 <;> simp [h]; cases flip <;> simp

private def jacobiReduce (a p : ℕ) : ℤ :=
  forceNat (a % p) fun r =>
    if r = 0 then 0 else jacobiSteps 64 r p false

private theorem jacobiReduce_spec (a p : ℕ) (hp : 1 < p) (ho : p % 2 = 1)
    (hmax : p ≤ 1414835497) :
    jacobiReduce a p = jacobiSym (a:ℤ) p := by
  rw [jacobiSym.mod_left (a:ℤ) p, ← Int.natCast_mod]
  simp only [jacobiReduce,forceNat_eq]
  split <;> rename_i h
  · rw [h, Nat.cast_zero, zero_left hp]
  · have hh := Nat.mod_lt a (by omega : 0 < p)
    have hprod := Nat.mul_le_mul (hh.le.trans hmax) hmax
    have hmax' : 1414835497*1414835497 < 2^64 := by decide
    rw [jacobiSteps_spec (hprod.trans_lt hmax') (Nat.pos_of_ne_zero h) hh ho hp]
    rfl

private def readDigit (word k : ℕ) : ℤ :=
  if word.testBit (2*k+1) then -1 else if word.testBit (2*k) then 1 else 0

private def word41 : ℕ :=
  1688936232098150237971860

private def word457 : ℕ :=
  46298491208118815962813641794942699716476799732405538217663837890354491262789605658115623791128131483789359157733415516165301095062003514019690073388246801797473295546743062688953774669866922016463560423657790370088999277794193427757011381794788743200853157322309794993101140

private def checkDigits (p word : ℕ) : Bool :=
  (List.range p).all fun k => decide (readDigit word k = evalLegendre p k)

set_option maxRecDepth 12000 in
private theorem word41_ok : checkDigits 41 word41 = true := by decide +kernel

set_option maxRecDepth 12000 in
private theorem word457_ok : checkDigits 457 word457 = true := by decide +kernel

private theorem readDigit_spec {p word : ℕ} [Fact p.Prime] (hp : 2 < p) (hf : p/2 < 2^31)
    (h : checkDigits p word = true) (a : ℕ) :
    readDigit word (a%p) = jacobiSym (a:ℤ) p := by
  have h₁ := (List.all_eq_true.mp h) (a%p) (List.mem_range.mpr (Nat.mod_lt _ (by omega)))
  have h₂ := of_decide_eq_true h₁
  rw [evalLegendre_eq_jacobi p _ hp hf, Int.natCast_mod, ← jacobiSym.mod_left] at h₂
  exact h₂

def kernelSmallReading (a b : ℕ) : ℤ :=
  readDigit word41 ((a+32*b) % 41) * readDigit word457 ((a+109*b) % 457)

theorem kernelSmallReading_eq (a b : ℕ) :
    kernelSmallReading a b = evalLegendre 41 (a+32*b) * evalLegendre 457 (a+109*b) := by
  have p₁ : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  have p₂ : Fact (Nat.Prime 457) := ⟨by norm_num⟩
  unfold kernelSmallReading
  rw [readDigit_spec (by decide) (by decide) word41_ok,
    readDigit_spec (by decide) (by decide) word457_ok,
    evalLegendre_eq_jacobi 41 _ (by decide) (by decide),
    evalLegendre_eq_jacobi 457 _ (by decide) (by decide)]

def kernelReading (a b : ℕ) : ℤ :=
  kernelSmallReading a b * jacobiReduce (a+516876951*b) 1414835497

theorem kernelReading_eq (a b : ℕ) : kernelReading a b = evalMark a b := by
  have p₃ : Fact (Nat.Prime 1414835497) := ⟨by norm_num⟩
  unfold kernelReading evalMark
  rw [kernelSmallReading_eq, jacobiReduce_spec _ _ (by decide) (by decide) (by decide),
    evalLegendre_eq_jacobi 1414835497 _ (by decide) (by decide)]

#print axioms kernelReading_eq
#print axioms kernelSmallReading_eq

end QuarticKernel
