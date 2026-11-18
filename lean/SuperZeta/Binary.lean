import SuperZeta.Spectrum
import Mathlib.NumberTheory.Padics.PadicNorm

/-! Binary arithmetic of the rational coefficients of the unit-coupling determinant. -/

namespace SuperZeta.Binary

open SuperZeta.Spectrum

def binaryWeight (n : ℕ) : ℕ := (Nat.digits 2 n).sum

private theorem weight_pos {n : ℕ} (h : 0 < n) : 0 < binaryWeight n := by
  exact lt_of_lt_of_le (Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 h.ne'))
    (List.le_sum_of_mem (List.getLast_mem _))

private theorem legendre_binary (n : ℕ) :
    (padicValNat 2 n.factorial : ℤ) = n - (binaryWeight n : ℤ) := by
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  have hle := Nat.digit_sum_le 2 n
  simp only [Nat.reduceSub, one_mul] at h
  unfold binaryWeight
  omega

private theorem val_two : padicValRat 2 (2 : ℚ) = 1 := padicValRat.self (by decide : 1 < 2)

/-- Exact valuation of each determinant coefficient from degree two onward. -/
theorem determinant_valuation {n : ℕ} (hn : 2 ≤ n) :
    padicValRat 2 (determinantCoeff 1 n) = (binaryWeight n : ℤ) - 1 := by
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have hfac : ((2 * n).factorial : ℚ) ≠ 0 := by positivity
  have h₂ : (2 : ℚ) ≠ 0 := by norm_num
  have hm : (-1 : ℚ) ≠ 0 := by norm_num
  have hpow := mul_ne_zero (pow_ne_zero n hm) (pow_ne_zero (2*n) h₂)
  simp only [determinantCoeff, if_neg hn0, if_neg hn1, zero_add, sub_zero]
  rw [padicValRat.div (div_ne_zero hpow hfac) h₂, padicValRat.div hpow hfac,
    padicValRat.mul (pow_ne_zero n hm) (pow_ne_zero (2*n) h₂), padicValRat.pow hm,
    padicValRat.pow h₂, padicValRat.of_nat, padicValNat_factorial_mul, val_two]
  simp only [padicValRat.neg, padicValRat.one, mul_zero, zero_add, mul_one, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, legendre_binary]
  ring

/-- The exact bridge between the normalized moments and the binary digit law.
The equivalence applies to every nonzero rational trace value. -/
theorem normalized_unit_iff (n : ℕ) {s : ℚ} (hs : s ≠ 0) :
    padicValRat 2 ((n.factorial : ℚ) * s / 2 ^ n) = 0 ↔
      padicValRat 2 s = (binaryWeight n : ℤ) := by
  have hfac : (n.factorial : ℚ) ≠ 0 := by positivity
  have h₂ : (2 : ℚ) ≠ 0 := by norm_num
  rw [padicValRat.div (mul_ne_zero hfac hs) (pow_ne_zero _ h₂),
    padicValRat.mul hfac hs, padicValRat.of_nat, legendre_binary, padicValRat.pow h₂,
    val_two, mul_one]
  omega

private theorem norm_le_one_of_val {a : ℚ} (h : 0 ≤ padicValRat 2 a) :
    padicNorm 2 a ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  rw [padicNorm.eq_zpow_of_nonzero ha]
  exact zpow_le_one_of_nonpos₀ (by norm_num) (by omega)

private theorem norm_le_half_of_val {a : ℚ} (h : 1 ≤ padicValRat 2 a) :
    padicNorm 2 a ≤ 1 / 2 := by
  by_cases ha : a = 0
  · norm_num [ha]
  rw [padicNorm.eq_zpow_of_nonzero ha]
  calc
    (2 : ℚ) ^ (-padicValRat 2 a) ≤ 2 ^ (-1 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 / 2 := by norm_num

private theorem determinant_norm_le (n : ℕ) : padicNorm 2 (determinantCoeff 1 n) ≤ 1 := by
  rcases n with _ | (_ | n)
  · norm_num [determinantCoeff, Nat.factorial]
  · norm_num [determinantCoeff, Nat.factorial, padicNorm.neg, padicNorm.padicNorm_p, val_two]
  apply norm_le_one_of_val
  rw [determinant_valuation (by omega)]
  change 0 ≤ (binaryWeight (n+2) : ℤ) - 1
  have h := weight_pos (n := n+2) (by omega)
  omega

private theorem determinant_derivative_norm (n : ℕ) :
    padicNorm 2 (determinantCoeff 1 (n+1) * ((n : ℚ) + 1)) ≤ 1/2 := by
  by_cases hn : n = 0
  · subst n
    norm_num [determinantCoeff, Nat.factorial, padicNorm.neg, padicNorm.padicNorm_p, val_two]
  by_cases he : 2 ∣ n+1
  · obtain ⟨k, hk⟩ := he
    have hcast : (n : ℚ) + 1 = 2 * k := by exact_mod_cast hk
    rw [hcast, padicNorm.mul, padicNorm.mul]
    have htwo : padicNorm 2 (2 : ℚ) = 1/2 := by
      simpa [one_div] using (padicNorm.padicNorm_p (p := 2) (by decide))
    rw [htwo]
    calc
      _ ≤ 1 * (1/2 * 1) := mul_le_mul (determinant_norm_le _)
        (mul_le_mul_of_nonneg_left (padicNorm.of_nat k) (by norm_num))
        (by positivity) (by norm_num)
      _ = _ := by norm_num
  · have hodd : (n+1)%2 = 1 := by omega
    have hbits : 2 ≤ binaryWeight (n+1) := by
      have ht := weight_pos (n := (n+1)/2) (by omega)
      unfold binaryWeight at *
      rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 2) (by omega : n+1 ≠ 0),
        List.sum_cons, hodd]
      omega
    have hc := norm_le_half_of_val (a := determinantCoeff 1 (n+1)) (by
      rw [determinant_valuation (by omega)]
      omega)
    rw [padicNorm.mul]
    have ht : padicNorm 2 ((n : ℚ)+1) ≤ 1 := by exact_mod_cast (padicNorm.of_nat (p:=2) (n+1))
    simpa only [mul_one] using mul_le_mul hc ht (padicNorm.nonneg _) (by norm_num : (0:ℚ) ≤ 1/2)

/-- Every rational trace of the unit-coupling determinant has even 2-adic
numerator (or is zero). This is an all-index statement about the actual
formal logarithmic derivative in Spectrum. -/
theorem trace_norm_le_half (n : ℕ) : padicNorm 2 (traceCoeff 1 n) ≤ 1/2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he := newton_convolution 1 n
    rw [Finset.sum_range_succ'] at he
    have h0 : determinantCoeff 1 0 = 1 := by norm_num [determinantCoeff]
    simp only [h0, Nat.sub_zero, one_mul] at he
    have hr : traceCoeff 1 n = -(determinantCoeff 1 (n+1) * ((n:ℚ)+1)) +
        -(∑ k ∈ Finset.range n, determinantCoeff 1 (k+1) * traceCoeff 1 (n-(k+1))) := by
      linarith only [he]
    rw [hr]
    apply padicNorm.nonarchimedean.trans
    rw [padicNorm.neg, padicNorm.neg]
    refine max_le (determinant_derivative_norm n) (padicNorm.sum_le' (fun k hk => ?_) (by norm_num))
    have hk' := Finset.mem_range.mp hk
    rw [padicNorm.mul]
    simpa only [one_mul] using mul_le_mul (determinant_norm_le (k+1))
      (ih _ (by omega : n-(k+1) < n)) (padicNorm.nonneg _) (by norm_num : (0:ℚ) ≤ 1)

/-- Exponential coefficients of sin(sqrt(2y))/sqrt(2y). -/
def sincCoeff : ℕ → ℚ
  | 0 => 1
  | n+1 => -sincCoeff n / (2*n+3)

private theorem sinc_unit (n : ℕ) : padicNorm 2 (sincCoeff n) = 1 := by
  induction n with
  | zero => simp [sincCoeff]
  | succ n ih =>
    have h₀ : (2 * (n : ℚ) + 3) ≠ 0 := by positivity
    have hv : padicValRat 2 (2 * (n : ℚ) + 3) = 0 := by
      exact_mod_cast (show padicValRat 2 ((2*n+3 : ℕ) : ℚ) = 0 by
        rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by omega), Nat.cast_zero])
    rw [sincCoeff, padicNorm.div, padicNorm.neg, ih, padicNorm.eq_zpow_of_nonzero h₀, hv]
    norm_num

def fourPowerQuot (n : ℕ) : ℚ := (2:ℚ) ^ (2*(n+1)) / (n+1)

/-- Exponential coefficients of (sinc²−1)/y. -/
def correctionCoeff (n : ℕ) : ℚ := sincCoeff (n+1) * (fourPowerQuot n / (n+2))

private theorem quot_val (n : ℕ) :
    padicValRat 2 (fourPowerQuot n) = 2*(n+1 : ℤ) - padicValNat 2 (n+1) := by
  unfold fourPowerQuot
  rw [padicValRat.div (by positivity) (by positivity), padicValRat.pow (by norm_num), val_two]
  have h : padicValRat 2 ((n:ℚ)+1) = padicValNat 2 (n+1) := by exact_mod_cast (padicValRat.of_nat (p:=2) (n:=n+1))
  rw [h]
  push_cast
  ring

private theorem vlt (n : ℕ) (h : n ≠ 0) : padicValNat 2 n < n :=
  (padicValNat_le_nat_log n).trans_lt (Nat.log_lt_self 2 h)

private theorem correction_small (n : ℕ) : padicNorm 2 (correctionCoeff n) ≤ 1/2 := by
  unfold correctionCoeff
  rw [padicNorm.mul, sinc_unit, one_mul]
  apply norm_le_half_of_val
  have hq : fourPowerQuot n ≠ 0 := by unfold fourPowerQuot; positivity
  have h₂ : padicValRat 2 ((n:ℚ)+2) = padicValNat 2 (n+2) := by exact_mod_cast (padicValRat.of_nat (p:=2) (n:=n+2))
  rw [padicValRat.div hq (by positivity), quot_val, h₂]
  have h₁ := vlt (n+1) (by omega)
  have h₂' := vlt (n+2) (by omega)
  omega

private theorem norm_two : padicNorm 2 (2:ℚ) = 1/2 := by
  simpa [one_div] using (padicNorm.padicNorm_p (p := 2) (by decide))

private theorem a_small (n : ℕ) :
    padicNorm 2 (-(sincCoeff (n+1) * (2 + fourPowerQuot n))) ≤ 1/2 := by
  rw [padicNorm.neg, padicNorm.mul, sinc_unit, one_mul]
  apply padicNorm.nonarchimedean.trans
  apply max_le norm_two.le
  apply norm_le_half_of_val
  rw [quot_val]
  have h := vlt (n+1) (by omega)
  omega

/-- The exact binomial convolution left by rationalizing the logarithmic
derivative with the conjugate cosine factor. The constant denominator is
1+2·(-2/3) = -1/3. This statement about the formal trace is the outstanding
power-series identity needed for the complete digit law. -/
def RationalizedRecurrence (P : ℕ → ℚ) : Prop :=
  ∀ n, (-1/3 : ℚ) * P (n+1) =
    -(sincCoeff (n+2) * (2 + fourPowerQuot (n+1))) - sincCoeff (n+1) -
    2 * ∑ j ∈ Finset.range (n+1), (Nat.choose (n+1) j : ℚ) * correctionCoeff (n+1-j) * P j

/-- The cancellation in the cosine rationalization, in any integral domain.
It can be applied before extracting coefficients in a formal series ring. -/
theorem rationalize_cosine {R : Type*} [CommRing R] [IsDomain R] {y c u v p : R}
    (hy : y ≠ 0) (hc : c ^ 2 + 2*y*u ^ 2 = 1) (hv : c*u = v)
    (hp : p*(1+c-y) = y*(1+u)) :
    p*(y+2*(u^2-1)) = 1-c+u-v-y*(1+u) := by
  have hf : (1+c-y)*(1-c-y) = y*(y+2*(u^2-1)) := by linear_combination -hc
  apply mul_left_cancel₀ hy
  calc
    y * (p * (y + 2 * (u ^ 2 - 1))) = p * ((1+c-y)*(1-c-y)) := by rw [hf]; ring
    _ = y*(1+u)*(1-c-y) := by rw [← hp]; ring
    _ = y*(1-c+u-v-y*(1+u)) := by rw [← hv]; ring

/-- The exact analytic normalization appearing in the manuscript. -/
theorem cosine_rationalized_at {z : ℝ} (hz : z ≠ 0)
    (hd : 1 + Real.cos z - z^2/2 ≠ 0) :
    let y := z^2/2
    let u := Real.sin z/z
    let v := Real.sin (2*z)/(2*z)
    let p := y*(1+u)/(1+Real.cos z-y)
    p*(y+2*(u^2-1)) = 1-Real.cos z+u-v-y*(1+u) := by
  dsimp only
  apply rationalize_cosine (by positivity)
  · field_simp [hz]
  · rw [Real.sin_two_mul]
    field_simp [hz]
    ring
  · exact div_mul_cancel₀ _ hd

/-- Multiplication under factorial normalization gives binomial convolution. -/
noncomputable def exponentialSeries (A : ℕ → ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => A k / (k.factorial : ℚ)

theorem exponential_product_coeff (A B : ℕ → ℚ) (n : ℕ) :
    (n.factorial : ℚ) * PowerSeries.coeff ℚ n (exponentialSeries A * exponentialSeries B) =
      ∑ j ∈ Finset.range (n+1), (n.choose j : ℚ) * A j * B (n-j) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h : j ≤ n := by have := Finset.mem_range.mp hj; omega
  have hfac : (n.choose j : ℚ) * (j.factorial : ℚ) * ((n-j).factorial : ℚ) = n.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
  simp only [exponentialSeries, PowerSeries.coeff_mk]
  field_simp
  linear_combination (A j * B (n-j)) * -hfac

def numeratorCoeff (n : ℕ) : ℚ :=
  -(sincCoeff (n+1) * (2 + fourPowerQuot n)) - sincCoeff n - (if n = 0 then 1 else 0)

private theorem exponential_coeff (A : ℕ → ℚ) (n : ℕ) :
    (n.factorial : ℚ) * PowerSeries.coeff ℚ n (exponentialSeries A) = A n := by
  rw [exponentialSeries, PowerSeries.coeff_mk, ← mul_div_assoc, mul_div_cancel_left₀ _ (by positivity)]

/-- The single rational power-series identity sufficient for the digit law.
Its two sides use explicit rational sequences and the original determinant traces. -/
def RationalizedSeries (P : ℕ → ℚ) : Prop :=
  exponentialSeries P + PowerSeries.C ℚ 2 * (exponentialSeries P * exponentialSeries correctionCoeff) =
    exponentialSeries numeratorCoeff

theorem recurrence_of_series {P : ℕ → ℚ} (hs : RationalizedSeries P) :
    RationalizedRecurrence P := by
  intro n
  have h := congrArg (fun S : PowerSeries ℚ => ((n+1).factorial : ℚ) * PowerSeries.coeff ℚ (n+1) S) hs
  dsimp only at h
  rw [map_add, PowerSeries.coeff_C_mul, mul_add, exponential_coeff, exponential_coeff,
    mul_left_comm, exponential_product_coeff, Finset.sum_range_succ] at h
  have w0 : correctionCoeff 0 = -2/3 := by norm_num [correctionCoeff, sincCoeff, fourPowerQuot]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self, w0, numeratorCoeff,
    Nat.succ_ne_zero, if_false, sub_zero] at h
  simp_rw [mul_right_comm _ (P _) (correctionCoeff _)] at h
  linarith only [h]

/-- The binomial convolution forces an odd normalized trace in every positive
degree. The proof uses only norm inequalities after the displayed recurrence. -/
theorem rationalized_unit {P : ℕ → ℚ} (h₀ : P 0 = 0) (hrec : RationalizedRecurrence P)
    (n : ℕ) : padicNorm 2 (P (n+1)) = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let a := -(sincCoeff (n+2) * (2 + fourPowerQuot (n+1)))
    let sum := ∑ j ∈ Finset.range (n+1), (Nat.choose (n+1) j : ℚ) * correctionCoeff (n+1-j) * P j
    have hs : padicNorm 2 sum ≤ 1 := by
      apply padicNorm.sum_le' _ (by norm_num)
      intro j hj
      have hpn : padicNorm 2 (P j) ≤ 1 := by
        rcases j with _ | j
        · simp [h₀]
        · exact (ih j (by have := Finset.mem_range.mp hj; omega)).le
      rw [padicNorm.mul, padicNorm.mul]
      have hw : padicNorm 2 (correctionCoeff (n+1-j)) ≤ 1 := (correction_small _).trans (by norm_num)
      apply le_trans (mul_le_mul (mul_le_mul (padicNorm.of_nat _) hw (padicNorm.nonneg _) zero_le_one)
        hpn (padicNorm.nonneg _) (by norm_num))
      norm_num
    have hb : padicNorm 2 (a - 2*sum) ≤ 1/2 := by
      apply padicNorm.sub.trans
      refine max_le (a_small _) ?_
      rw [padicNorm.mul, norm_two]
      linarith only [hs]
    have heq : (-1/3 : ℚ) * P (n+1) = -sincCoeff (n+1) + (a - 2*sum) := by
      change (-1/3 : ℚ) * P (n+1) = -sincCoeff (n+1) + (_ - _)
      rw [hrec n]
      dsimp [sum, a]
      ring
    have hfactor : padicNorm 2 (-1/3 : ℚ) = 1 := by
      rw [padicNorm.div, padicNorm.neg, padicNorm.one]
      have hthree : padicValRat 2 (3:ℚ) = 0 := by
        change padicValRat 2 ((3:ℕ):ℚ) = 0
        rw [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd (by decide), Nat.cast_zero]
      rw [padicNorm.eq_zpow_of_nonzero (by norm_num : (3:ℚ) ≠ 0), hthree]
      norm_num
    have hc := congrArg (padicNorm 2) heq
    rw [padicNorm.mul, hfactor, one_mul, padicNorm.add_eq_max_of_ne] at hc
    · rw [padicNorm.neg, sinc_unit, max_eq_left (by linarith only [hb])] at hc
      exact hc
    · rw [padicNorm.neg, sinc_unit]
      linarith only [hb]

/-- The n-th normalized exponential coefficient, with constant term zero. -/
noncomputable def normalizedTrace : ℕ → ℚ
  | 0 => 0
  | n+1 => ((n+1).factorial : ℚ) * traceCoeff 1 n / 2 ^ (n+1)

theorem trace_digit_law_of_rationalization (h : RationalizedRecurrence normalizedTrace) (n : ℕ) :
    padicValRat 2 (traceCoeff 1 n) = (binaryWeight (n+1) : ℤ) := by
  have hunit := rationalized_unit (P := normalizedTrace) rfl h n
  have hne : normalizedTrace (n+1) ≠ 0 := by
    intro hz
    rw [hz, padicNorm.zero] at hunit
    norm_num at hunit
  have ht : traceCoeff 1 n ≠ 0 := by
    intro hz
    apply hne
    simp [normalizedTrace, hz]
  apply (normalized_unit_iff _ ht).mp
  change padicValRat 2 (normalizedTrace (n+1)) = 0
  rw [padicNorm.eq_zpow_of_nonzero hne, zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)] at hunit
  omega

theorem trace_digit_law_of_series (h : RationalizedSeries normalizedTrace) (n : ℕ) :
    padicValRat 2 (traceCoeff 1 n) = (binaryWeight (n+1) : ℤ) :=
  trace_digit_law_of_rationalization (recurrence_of_series h) n

end SuperZeta.Binary
