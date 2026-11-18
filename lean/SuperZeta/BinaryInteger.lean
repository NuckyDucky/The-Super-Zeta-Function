import SuperZeta.BinaryLaw

/-! Integer normalization of the positive-index determinant traces. -/
namespace SuperZeta.Binary

open SuperZeta.Spectrum

private noncomputable def integralRationals : Subring ℚ := (Int.castRingHom ℚ).range

private lemma nat_mem (m : ℕ) : (m : ℚ) ∈ integralRationals := ⟨(m:ℤ), by simp⟩

private theorem determinant_integral (n : ℕ) :
    ((2*n).factorial : ℚ) * determinantCoeff 1 n ∈ integralRationals := by
  rcases n with _ | n
  · change ∃ k : ℤ, (k:ℚ) = _
    exact ⟨1, by norm_num [determinantCoeff]⟩
  rcases n with _ | n
  · change ∃ k : ℤ, (k:ℚ) = _
    exact ⟨-4, by norm_num [determinantCoeff, Nat.factorial]⟩
  change ∃ k : ℤ, (k:ℚ) = _
  refine ⟨(-1:ℤ)^(n+2)*2^(2*n+3), ?_⟩
  have hn : n+2 ≠ 1 := by omega
  simp only [determinantCoeff, Nat.succ_ne_zero, if_false, hn, zero_add, sub_zero]
  push_cast
  rw [show (2:ℚ)^(2*(n+2)) = 2^(2*n+3)*2 by rw [← pow_succ]; congr 1]
  field_simp
  ring

/-- Multiplication by (2n)! clears every denominator of trace Sₙ. This
uses integer binomial coefficients and the Newton equation for the actual determinant. -/
theorem factorial_trace_integral (n : ℕ) :
    ∃ k : ℤ, (k:ℚ) = ((2*(n+1)).factorial : ℚ) * traceCoeff 1 n := by
  change ((2*(n+1)).factorial : ℚ) * traceCoeff 1 n ∈ integralRationals
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have eqn := newton_convolution 1 n
    rw [Finset.sum_range_succ'] at eqn
    have e₀ : determinantCoeff 1 0 = 1 := by norm_num [determinantCoeff]
    simp only [e₀, Nat.sub_zero, one_mul] at eqn
    have main_term : -(((2*(n+1)).factorial : ℚ)*determinantCoeff 1 (n+1))*((n:ℚ)+1)
        ∈ integralRationals := integralRationals.mul_mem
          (integralRationals.neg_mem (determinant_integral _))
          (integralRationals.add_mem (nat_mem n) integralRationals.one_mem)
    have lower : ∑ j ∈ Finset.range n, ((2*(n+1)).factorial : ℚ) *
        (determinantCoeff 1 (j+1) * traceCoeff 1 (n-(j+1))) ∈ integralRationals := by
      apply integralRationals.sum_mem
      intro j hj
      have hj' := Finset.mem_range.mp hj
      let i := n-(j+1)
      have hi : i<n := by dsimp [i]; omega
      have m : 2*(j+1) ≤ 2*(n+1) := by omega
      have hn : 2*(n+1)-2*(j+1) = 2*(i+1) := by dsimp [i]; omega
      have hc := Nat.choose_mul_factorial_mul_factorial m
      rw [hn] at hc
      change ((2*(n+1)).factorial : ℚ) * (determinantCoeff 1 (j+1) * traceCoeff 1 i)
        ∈ integralRationals
      rw [← hc]
      push_cast
      convert integralRationals.mul_mem
        (integralRationals.mul_mem (nat_mem ((2*(n+1)).choose (2*(j+1))))
          (determinant_integral (j+1))) (ih i hi) using 1
      ring
    convert integralRationals.sub_mem main_term lower using 1
    rw [← Finset.mul_sum]
    linear_combination ((2*(n+1)).factorial : ℚ) * eqn

private lemma doubled_factorial_value (n : ℕ) :
    (padicValNat 2 (2*n).factorial : ℤ) = 2*(n:ℤ)-binaryWeight n := by
  rw [padicValNat_factorial_mul]
  have h := sub_one_mul_padicValNat_factorial (p:=2) n
  have hle := Nat.digit_sum_le 2 n
  simp only [Nat.reduceSub, one_mul] at h
  unfold binaryWeight
  omega

/-- The normalized trace is an odd integer at every positive index n+1. -/
theorem odd_integer_trace (n : ℕ) :
    ∃ k : ℤ, Odd k ∧
      ((2*(n+1)).factorial : ℚ) * traceCoeff 1 n / 4^(n+1) = k := by
  obtain ⟨j,hj⟩ := factorial_trace_integral n
  have htrace : traceCoeff 1 n ≠ 0 := by
    intro h
    have hv := trace_digit_law n
    rw [h,padicValRat.zero] at hv
    have hpos := Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 (Nat.succ_ne_zero n))
    have hpos' : 0 < binaryWeight (n+1) :=
      lt_of_lt_of_le hpos (List.le_sum_of_mem (List.getLast_mem _))
    unfold binaryWeight at hv
    exact (Nat.ne_of_gt hpos') (by exact_mod_cast hv.symm)
  have vj : padicValInt 2 j = 2*(n+1) := by
    have h : (padicValInt 2 j : ℤ) = 2*((n:ℤ)+1) := by
      rw [← padicValRat.of_int, hj, padicValRat.mul (by positivity) htrace, padicValRat.of_nat,
        doubled_factorial_value, trace_digit_law]
      push_cast
      ring
    omega
  have hd : (2:ℤ)^(2*(n+1)) ∣ j := (padicValInt_dvd_iff _ _).2 (Or.inr vj.ge)
  obtain ⟨k,hk⟩ := hd
  have hkodd : Odd k := by
    rw [← Int.not_even_iff_odd, even_iff_two_dvd]
    rintro ⟨c,hc⟩
    have hd' : (2:ℤ)^(2*(n+1)+1) ∣ j := ⟨c, by rw [hk,hc,pow_succ]; ring⟩
    rcases (padicValInt_dvd_iff (p:=2) (2*(n+1)+1) j).1 hd' with hz | hle
    · simp [hz] at vj
    · rw [vj] at hle
      exact Nat.not_succ_le_self _ hle
  refine ⟨k,hkodd,?_⟩
  rw [← hj, hk]
  push_cast
  rw [pow_mul]
  norm_num

private lemma norm_integer_product {a b c : ℚ} (ha : padicNorm 2 a ≤ 1/2)
    (hb : padicNorm 2 b ≤ 1/2) (hc : padicNorm 2 c ≤ 1) :
    padicNorm 2 (a*b*c) ≤ 1/4 := by
  rw [padicNorm.mul, padicNorm.mul]
  apply le_trans (mul_le_mul (mul_le_mul ha hb (padicNorm.nonneg _) (by norm_num)) hc
    (padicNorm.nonneg _) (by norm_num))
  norm_num

/-- The rationalized convolution determines the first two binary digits of
the normalized trace directly from the sinc coefficient. -/
theorem normalized_trace_mod_four (n : ℕ) :
    padicNorm 2 (normalizedTrace (n+1) - sincCoeff (n+1)) ≤ 1/4 := by
  let L := ∑ j ∈ Finset.range (n+1), (Nat.choose (n+1) j : ℚ) *
    correctionCoeff (n+1-j) * normalizedTrace j
  have recn := recurrence_of_series normalizedTrace_series
  have hsum : padicNorm 2 L ≤ 1/2 := by
    apply padicNorm.sum_le' _ (by norm_num)
    intro j _
    have hu : padicNorm 2 (normalizedTrace j) ≤ 1 := by
      cases j with
      | zero => norm_num [normalizedTrace]
      | succ j => exact (rationalized_unit (P := normalizedTrace) rfl recn j).le
    rw [padicNorm.mul, padicNorm.mul]
    apply le_trans (mul_le_mul (mul_le_mul (padicNorm.of_nat _) (correction_small _)
      (padicNorm.nonneg _) zero_le_one) hu (padicNorm.nonneg _) (by norm_num))
    norm_num
  have hu : sincCoeff (n+2) * (2 * (n:ℚ) + 5) = -sincCoeff (n+1) := by
    rw [show (2*(n:ℚ)+5) = 2*((n+1:ℕ):ℚ)+3 by push_cast; ring]
    exact div_mul_cancel₀ _ (by positivity)
  have he : normalizedTrace (n+1) - sincCoeff (n+1) =
      -(4*((n:ℚ)+1)*sincCoeff (n+2)) + 3*sincCoeff (n+2)*fourPowerQuot (n+1) + 6*L := by
    dsimp only [L]
    linear_combination -3 * (recn n) + 2*hu
  have two : padicNorm 2 (2:ℚ) = 1/2 := by
    simpa [one_div] using (padicNorm.padicNorm_p (p:=2) (by decide))
  have qsmall : padicNorm 2 (fourPowerQuot (n+1)) ≤ 1/4 := by
    have hq : fourPowerQuot (n+1) ≠ 0 := by unfold fourPowerQuot; positivity
    rw [padicNorm.eq_zpow_of_nonzero hq, quot_val]
    have h := (padicValNat_le_nat_log (p:=2) (n+1+1)).trans_lt (Nat.log_lt_self 2 (by omega))
    calc
      _ ≤ (2:ℚ)^(-2:ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num; omega)
      _ = _ := by norm_num
  have three : padicNorm 2 (3:ℚ) ≤ 1 := padicNorm.of_nat 3
  rw [he]
  apply padicNorm.nonarchimedean.trans
  refine max_le (padicNorm.nonarchimedean.trans (max_le ?_ ?_)) ?_
  · rw [padicNorm.neg, padicNorm.mul, sinc_unit, mul_one,
      show (4:ℚ)*((n:ℚ)+1) = 2*2*((n+1:ℕ):ℚ) by push_cast; ring]
    exact norm_integer_product two.le two.le (padicNorm.of_nat _)
  · rw [padicNorm.mul, padicNorm.mul, sinc_unit, mul_one]
    simpa using mul_le_mul three qsmall (padicNorm.nonneg _) zero_le_one
  · rw [show 6*L = (2:ℚ)*L*3 by ring]
    exact norm_integer_product two.le hsum three

private theorem signed_odd_one_mod_four (n : ℕ) :
    ∃ a : ℤ, (-1:ℤ)^n*(2*(n:ℤ)+1) = 1+4*a := by
  rcases Nat.even_or_odd n with ⟨a,ha⟩ | ⟨a,ha⟩
  · subst n
    refine ⟨a, ?_⟩
    rw [pow_add, ← mul_pow]
    push_cast
    norm_num
    ring
  · subst n
    refine ⟨-(a:ℤ)-1, ?_⟩
    rw [pow_succ, two_mul a, pow_add, mul_right_comm, ← mul_pow]
    push_cast
    norm_num
    ring

private theorem sinc_trace_factor (n : ℕ) (k : ℤ)
    (hk : ((2*(n+1)).factorial : ℚ) * traceCoeff 1 n / 4^(n+1) = k) :
    normalizedTrace (n+1) = sincCoeff (n+1) *
      (((-1:ℤ)^(n+1)*(2*((n+1:ℕ):ℤ)+1)*k : ℤ) : ℚ) := by
  let m := n+1
  have hu := scaled_sinc m
  rw [Nat.factorial_succ (2*m)] at hu
  have h₁ : (m.factorial : ℚ) ≠ 0 := by positivity
  have h₂ : ((2*m).factorial : ℚ) ≠ 0 := by positivity
  have h₃ : ((2*m+1:ℕ) : ℚ) ≠ 0 := by positivity
  have h₄ : (2:ℚ)^m ≠ 0 := by positivity
  have htr : ((2*m).factorial:ℚ)*traceCoeff 1 n = k * (4:ℚ)^m :=
    (div_eq_iff (by positivity)).mp hk
  have hfour : (4:ℚ)^m = 2^m*2^m := by rw [← mul_pow]; norm_num
  have hS : sincCoeff m = ((-1:ℚ)^m * 2^m * m.factorial) /
      (((2*m+1:ℕ):ℚ) * ((2*m).factorial:ℚ)) := by
    rw [eq_div_iff (mul_ne_zero h₃ h₂)]
    push_cast at hu ⊢
    field_simp at hu
    linear_combination hu
  change (m.factorial:ℚ)*traceCoeff 1 n / 2^m =
    sincCoeff m * (((-1:ℤ)^m*(2*(m:ℤ)+1)*k : ℤ) : ℚ)
  rw [hS]
  rw [hfour] at htr
  push_cast
  have hs := neg_one_pow_eq_or ℚ m
  rcases hs with hs | hs <;> rw [hs] <;> field_simp <;>
    linear_combination (m.factorial:ℚ) * (2*(m:ℚ)+1) * htr

/-- Every positive-index integer trace equals one modulo four. -/
theorem integer_trace_one_mod_four (n : ℕ) :
    ∃ j : ℤ, ((2*(n+1)).factorial : ℚ) * traceCoeff 1 n / 4^(n+1) = 1+4*(j:ℚ) := by
  obtain ⟨k, _, hk⟩ := odd_integer_trace n
  let m := n+1
  let z := (-1:ℤ)^m*(2*(m:ℤ)+1)*k - 1
  have hz : normalizedTrace (n+1) - sincCoeff (n+1) = sincCoeff (n+1)*(z:ℚ) := by
    rw [sinc_trace_factor n k hk]
    dsimp only [z, m]
    push_cast
    ring
  have hn := normalized_trace_mod_four n
  rw [hz, padicNorm.mul, sinc_unit, one_mul] at hn
  have h4 : (4:ℤ) ∣ z := by
    apply (padicNorm.dvd_iff_norm_le (p:=2) (n:=2) (z:=z)).2
    norm_num
    exact hn
  obtain ⟨b, hb⟩ := h4
  obtain ⟨a, ha⟩ := signed_odd_one_mod_four m
  dsimp only [z] at hb
  rw [ha] at hb
  have hk' : k = 1+4*(b-a*k) := by linarith only [hb]
  refine ⟨b-a*k, hk.trans ?_⟩
  exact_mod_cast hk'

end SuperZeta.Binary
