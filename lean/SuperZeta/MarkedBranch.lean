import SuperZeta.FieldWeights
import SuperZeta.SignWords

/-! Algebra of the ordinary and fourth-harmonic readings on a two-ideal norm
shell. The arithmetic signs at 73 come from the original branch quadratic. -/

namespace SuperZeta.MarkedBranch

/-- The imaginary part of the Gaussian direction to the fourth power.
The polynomial formula uses the Gaussian unit-invariant fourth harmonic. -/
def sineFour (a b : ℚ) : ℚ :=
  4*a*b*(a^2-b^2)/(a^2+b^2)^2

/-- Link the rational implementation to the imaginary part of the fourth
power of the actual marked complex vector, normalized by its squared norm
squared. -/
theorem sineFour_complex (a b : ℚ) :
    (sineFour a b : ℝ) =
      (((a : ℂ) + (b : ℂ)*Complex.I)^4).im /
        ((a : ℝ)^2+(b : ℝ)^2)^2 := by
  unfold sineFour
  push_cast
  congr 1
  simp [pow_succ, Complex.mul_im, Complex.mul_re]
  ring

theorem sineFour_conj (a b : ℚ) : sineFour a (-b) = -sineFour a b := by
  unfold sineFour
  ring

theorem sineFour_unit (a b : ℚ) : sineFour (-b) a = sineFour a b := by
  unfold sineFour
  ring

/-- A vector off the axes and diagonals supplies a nonzero fourth harmonic. -/
theorem sineFour_ne_zero (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a^2 ≠ b^2) :
    sineFour a b ≠ 0 := by
  unfold sineFour
  apply div_ne_zero
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb) (sub_ne_zero.mpr hab)
  · have hp : 0 < a^2 := sq_pos_of_ne_zero ha
    positivity

/-- Ordinary coefficient and imaginary angular coefficient in a fixed frame. -/
def readPair (s left right : ℚ) : ℚ × ℚ := (left+right, (left-right)*s)

/-- Exchanging the arithmetic signs is equivalent to reversing orientation. -/
theorem swap_reading (s a b : ℚ) : readPair s b a = readPair (-s) a b := by
  apply Prod.ext <;> dsimp [readPair] <;> ring

/-- Forgetting which reading had positive orientation identifies both
branches, even if the two readings coincide and multiplicity is retained. -/
theorem unlabelled_readings (s a b : ℚ) :
    ([readPair s a b, readPair (-s) a b] : Multiset (ℚ × ℚ)) =
      ([readPair s b a, readPair (-s) b a] : Multiset (ℚ × ℚ)) := by
  rw [swap_reading s b a, swap_reading (-s) b a, neg_neg]
  exact Quot.sound (List.Perm.swap _ _ [])

/-- The same two readings recover both unknown local weights when the
angular harmonic is nonzero. -/
theorem recover (s left right : ℚ) (hs : s ≠ 0) :
    let v := readPair s left right
    ((v.1 + v.2/s)/2, (v.1-v.2/s)/2) = (left,right) := by
  dsimp [readPair]
  apply Prod.ext <;> field_simp

noncomputable def firstSign : ℚ := (FieldWeights.rootCount 73 27 : ℚ) - 1
noncomputable def secondSign : ℚ := (FieldWeights.rootCount 73 46 : ℚ) - 1

theorem original73 :
    readPair (sineFour 3 8) firstSign secondSign = (0,10560/5329) := by
  unfold readPair firstSign secondSign sineFour
  rw [FieldWeights.root_counts_73.1, FieldWeights.root_counts_73.2]
  norm_num

theorem conjugate73 :
    readPair (sineFour 3 8) secondSign firstSign = (0,-10560/5329) := by
  unfold readPair firstSign secondSign sineFour
  rw [FieldWeights.root_counts_73.1, FieldWeights.root_counts_73.2]
  norm_num

/-- The quadratic character's two unramified values become letters. Zero
and other rational inputs have no corresponding signed exponential stage. -/
def signOfWeight (q : ℚ) : Option SignWords.Sign :=
  if q = 1 then some .plus else if q = -1 then some .minus else none

def signWeight : SignWords.Sign → ℚ
  | .plus => 1
  | .minus => -1

@[simp] theorem signOfWeight_signWeight (s : SignWords.Sign) :
    signOfWeight (signWeight s) = some s := by
  cases s <;> norm_num [signWeight, signOfWeight]

/-- Read the specified ideal first and its complex conjugate second. -/
def shellWord (s : ℚ) (v : ℚ × ℚ) : Option (List SignWords.Sign) := do
  if s = 0 then none else
    let left ← signOfWeight ((v.1 + v.2 / s) / 2)
    let right ← signOfWeight ((v.1 - v.2 / s) / 2)
    return [left, right]

theorem recover_shellWord (s : ℚ) (hs : s ≠ 0) (a b : SignWords.Sign) :
    shellWord s (readPair s (signWeight a) (signWeight b)) = some [a, b] := by
  have pair := recover s (signWeight a) (signWeight b) hs
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj pair
  simp [shellWord, hs, h₁, h₂]

theorem shellWords73 :
    shellWord (sineFour 3 8) (readPair (sineFour 3 8) firstSign secondSign) =
        some [.minus, .plus] ∧
    shellWord (sineFour 3 8) (readPair (sineFour 3 8) secondSign firstSign) =
        some [.plus, .minus] := by
  rw [original73, conjugate73]
  norm_num [shellWord, sineFour, signOfWeight]

/-- Each shell specifies an orientation and two letters in the chosen ideal order. -/
structure UnramifiedShell where
  sine : ℚ
  nonzero : sine ≠ 0
  left : SignWords.Sign
  right : SignWords.Sign

def UnramifiedShell.reading (p : UnramifiedShell) : ℚ × (ℚ × ℚ) :=
  (p.sine, readPair p.sine (signWeight p.left) (signWeight p.right))

/-- Recover the chronological word of a list of measured shells, stopping if
a sine vanishes or a recovered weight fails to encode a sign. -/
def readingsToWord : List (ℚ × (ℚ × ℚ)) → Option (List SignWords.Sign)
  | [] => some []
  | (s, v) :: rest => do
    let pair ← shellWord s v
    let tail ← readingsToWord rest
    return pair ++ tail

theorem recover_phrase (shells : List UnramifiedShell) :
    readingsToWord (shells.map UnramifiedShell.reading) =
      some (shells.flatMap (fun p => [p.left, p.right])) := by
  induction shells with
  | nil => rfl
  | cons p ps ih =>
    simp [UnramifiedShell.reading, readingsToWord, recover_shellWord _ p.nonzero, ih]

/-- The recovered word can be evaluated at the original cap and read back
with one signed logarithm per letter. The order is supplied by the list. -/
theorem shell_cap_roundtrip {L : ℝ} (hL : 0 < L) (shells : List UnramifiedShell) :
    let word := shells.flatMap (fun p => [p.left, p.right])
    do { let w ← readingsToWord (shells.map UnramifiedShell.reading)
         SignWords.decodeReal L word.length (SignWords.eval (L : ℂ) w 1).re } =
      some word := by
  dsimp only
  rw [recover_phrase]
  exact SignWords.decodeReal_eval hL _ _ le_rfl

/-- Exact cap values at base 2 for the two signed words above 73. -/
theorem capValues73 :
    SignWords.eval (Real.log 2 : ℂ) [.minus, .plus] 1 = (Real.sqrt 2 : ℂ) ∧
    SignWords.eval (Real.log 2 : ℂ) [.plus, .minus] 1 = 1/4 := by
  have he : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have hn : Real.exp (-Real.log 2) = 1/2 := by rw [Real.exp_neg, he]; norm_num
  have hp : Real.exp (Real.log 2 * (1/2)) = Real.sqrt 2 := by
    rw [← div_eq_mul_one_div, Real.exp_half, he]
  have hm : Real.exp (-(Real.log 2) * 2) = 1/4 := by
    rw [mul_two, Real.exp_add, hn]; norm_num
  change (Complex.exp ((Real.log 2 : ℂ) * Complex.exp (-(Real.log 2 : ℂ) * 1)) = _) ∧
    Complex.exp (-(Real.log 2 : ℂ) * Complex.exp ((Real.log 2 : ℂ) * 1)) = _
  simp only [mul_one]
  push_cast [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  constructor
  · rw [hn, hp]
  · rw [he, hm]
    norm_num

theorem distinct_rooted_73_words {L : ℝ} (hL : 0 < L) :
    SignWords.eval (L : ℂ) [.minus, .plus] 1 ≠
      SignWords.eval (L : ℂ) [.plus, .minus] 1 := by
  intro h
  have hh : [SignWords.Sign.minus, .plus] = [.plus, .minus] :=
    SignWords.real_cap_injective hL h
  cases hh

end SuperZeta.MarkedBranch
