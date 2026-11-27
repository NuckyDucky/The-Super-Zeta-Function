import DedekindDiscriminant23AdaptivePhase

/-! Integer tests for choosing the parameters of the uniform phase approximation. -/

namespace FieldTarget

open Finset

def discriminant23NormCutoff (k : ℕ) : ℕ := (18 * k + 26) / 13

def discriminant23PhaseTermCount (N : ℕ) : ℕ :=
  (characterThetaTermsUpTo discriminant23PrincipalForm N).card +
    (characterThetaTermsUpTo discriminant23OtherForm N).card

private theorem nat_lt_two_pow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [pow_succ]
      omega

/-- Each integer test spends less than a third of the error target. -/
theorem discriminant23_phaseError_lt_of_integer_bounds {a b k L depth : ℕ} (hb : 0 < b)
    (hNorm : 45 * b * 3 ^ k < a * 11 ^ k)
    (hRadial : 378 * b < 5 * a * 2 ^ (2 ^ L))
    (hQuad : 12 * b * L * (L + 1) * discriminant23PhaseTermCount (discriminant23NormCutoff k) < a * 2 ^ depth)
    {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖discriminant23CharacterFold w -
      discriminant23PhaseTaylorUpTo (discriminant23NormCutoff k) L depth false w‖ < (a : ℝ) / b ∧
    ‖deriv discriminant23CharacterFold w -
      discriminant23PhaseTaylorUpTo (discriminant23NormCutoff k) L depth true w‖ < (a : ℝ) / b := by
  have hB : (0 : ℝ) < b := by exact_mod_cast hb
  have hp : 15 * (3 / 11 : ℝ) ^ k < (a : ℝ) / (3 * b) := by
    have h : (45 : ℝ) * b * (3 : ℝ) ^ k < (a : ℝ) * (11 : ℝ) ^ k := by exact_mod_cast hNorm
    rw [div_pow, ← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [h]
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
  have hEL : ((2 ^ L : ℕ) : ℝ) ≤ Real.exp (L : ℝ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, show (L : ℝ) = (L : ℝ) * 1 by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) he L
  have hExp : Real.exp (-(5 / 4 : ℝ) * Real.exp (L : ℝ)) ≤ (1 / 2 : ℝ) ^ ((2 : ℕ) ^ L) := by
    refine (Real.exp_le_exp.mpr (by linarith only [hEL, Real.exp_nonneg (L : ℝ)] :
      -(5 / 4 : ℝ) * Real.exp (L : ℝ) ≤ -((2 ^ L : ℕ) : ℝ))).trans ?_
    rw [show -((2 ^ L : ℕ) : ℝ) = ((2 ^ L : ℕ) : ℝ) * (-1) by ring, Real.exp_nat_mul]
    apply pow_le_pow_left₀ (Real.exp_nonneg _)
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (by norm_num) he
  have hr : (126 / 5 : ℝ) * Real.exp (-(5 / 4 : ℝ) * Real.exp (L : ℝ)) < (a : ℝ) / (3 * b) := by
    refine (mul_le_mul_of_nonneg_left hExp (by norm_num)).trans_lt ?_
    have h : (378 : ℝ) * b < 5 * (a : ℝ) * (2 : ℝ) ^ ((2 : ℕ) ^ L) := by exact_mod_cast hRadial
    rw [div_pow, one_pow, ← mul_div_assoc, mul_one, div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [h]
  let N := discriminant23NormCutoff k
  have hExact : discriminant23PhaseQuadratureError N L depth =
      4 * (L : ℝ) * ((L : ℝ) + 1) * (discriminant23PhaseTermCount N : ℝ) * (1 / 2) ^ depth := by
    unfold discriminant23PhaseQuadratureError discriminant23PhaseTermCount
    push_cast
    rfl
  have hq : discriminant23PhaseQuadratureError N L depth < (a : ℝ) / (3 * b) := by
    have h : (12 : ℝ) * b * L * ((L : ℝ) + 1) * (discriminant23PhaseTermCount N : ℝ) <
        (a : ℝ) * (2 : ℝ) ^ depth := by exact_mod_cast hQuad
    rw [hExact, div_pow, one_pow, ← mul_div_assoc, mul_one,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith only [h]
  have hBound := discriminant23_phaseTaylorUpTo_error (N := N) (L := L) (depth := depth) (order := k + 1)
    (by omega) (by unfold N discriminant23NormCutoff; omega) hlo hhi
  have hTotal : discriminant23CharacterModelError (k + 1) (Real.exp L) +
      discriminant23PhaseQuadratureError N L depth < (a : ℝ) / b := by
    unfold discriminant23CharacterModelError
    rw [Nat.add_sub_cancel]
    refine (add_lt_add (add_lt_add hp hr) hq).trans_eq ?_
    ring
  exact ⟨hBound.1.trans_lt hTotal, hBound.2.trans_lt hTotal⟩

/-- The three searches terminate for every positive rational tolerance. -/
theorem discriminant23_exists_integer_bounds (a b : ℕ) (ha : 0 < a) :
    ∃ k L depth : ℕ, 45 * b * 3 ^ k < a * 11 ^ k ∧
      378 * b < 5 * a * 2 ^ (2 ^ L) ∧
      12 * b * L * (L + 1) * discriminant23PhaseTermCount (discriminant23NormCutoff k) < a * 2 ^ depth := by
  let k := 45 * b
  let L := 378 * b
  let depth := 12 * b * L * (L + 1) * discriminant23PhaseTermCount (discriminant23NormCutoff k)
  refine ⟨k, L, depth, ?_, ?_, ?_⟩
  · change k * 3 ^ k < a * 11 ^ k
    calc
      _ < 2 ^ k * 3 ^ k := mul_lt_mul_of_pos_right (nat_lt_two_pow k) (by positivity)
      _ = (6 : ℕ) ^ k := by rw [← mul_pow]; norm_num
      _ ≤ 11 ^ k := pow_le_pow_left' (by decide) _
      _ ≤ _ := by simpa only [one_mul] using Nat.mul_le_mul_right (11 ^ k) (show 1 ≤ a by omega)
  · change L < 5 * a * 2 ^ (2 ^ L)
    exact ((nat_lt_two_pow L).trans (nat_lt_two_pow (2 ^ L))).trans_le
      (by simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ (2 ^ L)) (show 1 ≤ 5 * a by omega))
  · change depth < a * 2 ^ depth
    exact (nat_lt_two_pow depth).trans_le
      (by simpa only [one_mul] using Nat.mul_le_mul_right (2 ^ depth) (show 1 ≤ a by omega))

#check @discriminant23_phaseError_lt_of_integer_bounds
#print axioms discriminant23_phaseError_lt_of_integer_bounds
#print axioms discriminant23_exists_integer_bounds

end FieldTarget
