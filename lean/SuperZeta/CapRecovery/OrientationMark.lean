import SuperZeta.CapRecovery.DyadicWeights

/-! An independently attributed coefficient of an inert Euler factor can
distinguish a word from its simultaneous sign reversal. The index counts
chronological stages; the Euler exponent is the cumulative encoded exponent. -/
noncomputable section
namespace SuperZeta.OrientationMark

open SignWords DyadicWeights FieldWeights

/-- The prime-power coefficient read after the first j stages. -/
def reading (a : ℝ) (w : List Sign) (j : ℕ) : ℝ :=
  primePowerWeight a (-1) (exponent (w.take j))

theorem reading_eq (a : ℝ) (w : List Sign) (j : ℕ) :
    reading a w j = 1 + a * signProduct (w.take j) := by
  rw [reading, primePowerWeight, dyadic_parity]

theorem signProduct_flip (w : List Sign) :
    signProduct (w.map Sign.flip) = (-1 : ℝ)^w.length * signProduct w := by
  induction w with
  | nil => simp [signProduct]
  | cons s w ih =>
    have h (b : Sign) (v : List Sign) : signProduct (b :: v) = letter b * signProduct v := by
      simp [signProduct]
    simp only [List.map_cons, List.length_cons, h, ih, pow_succ]
    cases s <;> simp [Sign.flip, letter]

theorem reading_flip (a : ℝ) (w : List Sign) {j : ℕ} (hj : j ≤ w.length) :
    reading a (w.map Sign.flip) j =
      1 + a * ((-1 : ℝ)^j * signProduct (w.take j)) := by
  rw [reading_eq, ← List.map_take, signProduct_flip, List.length_take_of_le hj]

/-- An even-stage reading agrees for both orientations. -/
theorem even_reading (a : ℝ) (w : List Sign) {j : ℕ} (hj : j ≤ w.length)
    (he : Even j) : reading a (w.map Sign.flip) j = reading a w j := by
  rw [reading_flip _ _ hj, he.neg_one_pow, one_mul, reading_eq]

private theorem abs_product (w : List Sign) : |signProduct w| = 1 := by
  rw [← dyadic_parity, abs_pow]
  simp

/-- One independently attributed reading gives the magnitude of its weight. -/
theorem weight_magnitude (a : ℝ) (w : List Sign) (j : ℕ) :
    |reading a w j - 1| = |a| := by
  rw [reading_eq, add_sub_cancel_left, abs_mul, abs_product, mul_one]

/-- Once a prefix sign is known, the same reading gives the signed weight. -/
theorem recover_weight (a : ℝ) (w : List Sign) (j : ℕ) :
    (reading a w j - 1) * signProduct (w.take j) = a := by
  have hsq : signProduct (w.take j) ^ 2 = 1 := by
    rw [← sq_abs, abs_product]; norm_num
  rw [reading_eq, add_sub_cancel_left]
  linear_combination a * hsq

/-- The gap is exactly twice the weight magnitude at every actual odd stage. -/
theorem odd_gap (a : ℝ) (w : List Sign) {j : ℕ} (hj : j ≤ w.length)
    (ho : Odd j) : |reading a w j - reading a (w.map Sign.flip) j| = 2 * |a| := by
  rw [reading_flip _ _ hj, ho.neg_one_pow, reading_eq]
  have h (c : ℝ) : (1 + a*c) - (1 + a*(-1*c)) = 2 * a * c := by ring
  rw [h, abs_mul, abs_product, mul_one, abs_mul]
  norm_num

theorem odd_reading_ne {a : ℝ} (ha : a ≠ 0) (w : List Sign) {j : ℕ}
    (hj : j ≤ w.length) (ho : Odd j) : reading a w j ≠ reading a (w.map Sign.flip) j := by
  intro he
  have h := odd_gap a w hj ho
  rw [he, sub_self, abs_zero] at h
  exact (ne_of_gt (mul_pos (by norm_num) (abs_pos.mpr ha))) h.symm

/-- The even stages and a zero weight exhaust the equal-reading cases. -/
theorem same_reading_iff (a : ℝ) (w : List Sign) {j : ℕ} (hj : j ≤ w.length) :
    reading a w j = reading a (w.map Sign.flip) j ↔ a = 0 ∨ Even j := by
  constructor
  · intro h
    by_cases ha : a = 0
    · exact Or.inl ha
    · rcases Nat.even_or_odd j with he | ho
      · exact Or.inr he
      · exact (odd_reading_ne ha w hj ho h).elim
  · rintro (rfl | he)
    · simp [reading_eq]
    · exact (even_reading a w hj he).symm

/-- When the signed weight is unknown, reversing both the letters and the
weight preserves all odd-stage readings. -/
theorem odd_flip_neg_weight (a : ℝ) (w : List Sign) {j : ℕ} (hj : j ≤ w.length)
    (ho : Odd j) : reading (-a) (w.map Sign.flip) j = reading a w j := by
  rw [reading_flip _ _ hj, ho.neg_one_pow, reading_eq]
  ring

/-- An even stage calibrates the weight for both possible orientations.
An odd stage then distinguishes them unless the weight vanishes. In a word
of length at least two one may use the first and second stages. -/
theorem even_odd_calibration (a b : ℝ) (w : List Sign) {e o : ℕ}
    (he : e ≤ w.length) (ho : o ≤ w.length) (hep : Even e) (hop : Odd o) :
    (reading a w e = reading b (w.map Sign.flip) e ∧
     reading a w o = reading b (w.map Sign.flip) o) ↔ a = 0 ∧ b = 0 := by
  constructor
  · rintro ⟨heq, hoq⟩
    rw [even_reading _ _ he hep] at heq
    have hab : a = b := by
      rw [← recover_weight a w e, ← recover_weight b w e, heq]
    subst b
    have ha : a = 0 := by
      by_contra h
      exact odd_reading_ne h w ho hop hoq
    exact ⟨ha, ha⟩
  · rintro ⟨rfl, rfl⟩
    simp [reading_eq]

end SuperZeta.OrientationMark
