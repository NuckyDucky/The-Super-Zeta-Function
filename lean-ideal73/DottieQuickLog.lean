import DottieNormLog

namespace QuarticModel

open private logPartial logHornerTicks_spec from DottieNormLog

private theorem residual_log_ticks (a b : ℕ) (hb : 0 < b) (hsmall : 64 * a ≤ b) :
    let r : ℝ := (a : ℝ) / b
    let ticks := logAtanhLowerTicks (2^96) a b 8
    (ticks : ℝ) ≤ (2:ℝ)^96 * Real.log ((1 + r) / (1 - r)) ∧
      (2:ℝ)^96 * Real.log ((1 + r) / (1 - r)) ≤ (ticks : ℝ) + 4 := by
  let r : ℝ := (a : ℝ) / b
  let value := Real.log ((1 + r) / (1 - r))
  let ticks := logAtanhLowerTicks (2^96) a b 8
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1/64 := by
    apply (div_le_iff₀ hb').2
    have h : (64:ℝ) * a ≤ b := by exact_mod_cast hsmall
    linarith
  have hr_lt : r < 1 := hr1.trans_lt (by norm_num)
  have hRound : (ticks : ℝ) ≤ 2 * (2:ℝ)^96 * logPartial r 8 0 ∧
      2 * (2:ℝ)^96 * logPartial r 8 0 ≤ (ticks : ℝ) + 3 := by
    have h := logHornerTicks_spec (2^96) a b hb (hr1.trans (by norm_num)) 8 0
    dsimp only at h
    simpa only [ticks, logAtanhLowerTicks, Nat.cast_pow, Nat.cast_ofNat] using h
  have hBelow : logPartial r 8 0 ≤ 1 / 2 * value := by
    simpa [logPartial, value] using Real.sum_range_le_log_div hr0 hr_lt 8
  have hAbove : 1 / 2 * value ≤ logPartial r 8 0 + r^17 / (1 - r^2) := by
    simpa [logPartial, value] using Real.log_div_le_sum_range_add hr0 hr_lt 8
  have htail : (2:ℝ)^96 * (2 * (r^17 / (1-r^2))) ≤ 1 := by
    have hsq := pow_le_pow_left₀ hr0 hr1 2
    have hden : (1:ℝ)/2 ≤ 1-r^2 := by linarith only [hsq]
    have hden_pos : 0 < 1-r^2 := lt_of_lt_of_le (by norm_num) hden
    have hpow := pow_le_pow_left₀ hr0 hr1 17
    have hdiv : r^17 / (1-r^2) ≤ (1/64:ℝ)^17 / (1/2) :=
      (div_le_div_of_nonneg_right hpow hden_pos.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by norm_num) hden)
    calc
      _ ≤ (2:ℝ)^96 * (2 * ((1/64:ℝ)^17 / (1/2))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiv (by norm_num)) (by positivity)
      _ ≤ 1 := by norm_num
  have hscale_pos : 0 ≤ 2 * (2:ℝ)^96 := by positivity
  change (ticks : ℝ) ≤ (2:ℝ)^96 * value ∧ (2:ℝ)^96 * value ≤ (ticks : ℝ) + 4
  constructor
  · nlinarith only [hRound.1, mul_le_mul_of_nonneg_left hBelow hscale_pos]
  · nlinarith only [hRound.2, htail, mul_le_mul_of_nonneg_left hAbove hscale_pos]

private theorem dyadic_mantissa_bounds (n : ℕ) (hn : 0 < n) :
    let k := n.log2 - 5
    let q : ℕ := 2^k
    let m := n / q
    let b := m*q
    0 < m ∧ m ≤ 63 ∧ b ≤ n ∧ 64*(n-b) ≤ n+b := by
  let k := n.log2 - 5
  let q : ℕ := 2^k
  let m := n / q
  let b := m*q
  have hq : 0 < q := by positivity
  have hnlo := Nat.log2_self_le hn.ne'
  have hq_le : q ≤ n := by
    apply le_trans _ hnlo
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).2 (Nat.sub_le ..)
  have hm : 0 < m := Nat.div_pos hq_le hq
  have hmhi : m ≤ 63 := by
    have hp : 2^(n.log2+1) ≤ 64*q := by
      change (2:ℕ)^(n.log2+1) ≤ 2^6 * 2^k
      rw [← pow_add]
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).2
      dsimp [k]
      omega
    have hh : m < 64 := (Nat.div_lt_iff_lt_mul hq).2 ((Nat.lt_log2_self (n := n)).trans_le hp)
    omega
  have hb : b ≤ n := Nat.div_mul_le_self n q
  refine ⟨hm, hmhi, hb, ?_⟩
  change 64*(n-b) ≤ n+b
  by_cases hk : k = 0
  · have hq1 : q = 1 := by simp [q, hk]
    have hb_eq : b = n := by simp only [b, m, hq1, Nat.div_one, Nat.mul_one]
    simp [hb_eq]
  · have hmlo : 32 ≤ m := by
      apply (Nat.le_div_iff_mul_le hq).2
      change (2:ℕ)^5 * 2^k ≤ n
      rw [← pow_add, show 5+k=n.log2 by dsimp [k] at hk ⊢; omega]
      exact hnlo
    have hmod : n % q + b = n := Nat.mod_add_div' n q
    have hrem : n - b < q := by
      have hh := Nat.mod_lt n hq
      omega
    have hbound : 32*q ≤ b := Nat.mul_le_mul_right q hmlo
    omega

private theorem log_split (n b : ℕ) (hn : 0 < n) (hb : 0 < b) (hbn : b ≤ n) :
    let r : ℝ := ((n - b : ℕ) : ℝ) / ((n + b : ℕ) : ℝ)
    Real.log n = Real.log b + Real.log ((1 + r) / (1 - r)) := by
  let r : ℝ := ((n - b : ℕ) : ℝ) / ((n + b : ℕ) : ℝ)
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hr : r = ((n : ℝ) - b) / ((n : ℝ) + b) := by simp [r, Nat.cast_sub hbn]
  have hRatio : (1 + r) / (1 - r) = (n : ℝ) / b := by
    rw [hr]
    have hs := add_pos hn' hb'
    have hpos : 0 < (1 : ℝ) - ((n : ℝ) - b) / ((n : ℝ) + b) := by
      apply sub_pos.mpr
      apply (div_lt_iff₀ hs).2
      linarith
    field_simp [hb'.ne', hs.ne', hpos.ne']
    ring
  change Real.log n = Real.log b + Real.log ((1 + r) / (1 - r))
  rw [hRatio, Real.log_div hn'.ne' hb'.ne']
  ring

private theorem standard_log_error : logAtanhErrorTicks (2^96) 31 = 4 := by decide +kernel

private theorem mantissa_log_ticks (m : ℕ) (hm : 0 < m) (hcap : m ≤ 63) :
    let ticks := (normLogBounds (2^96) 31 m).1
    (ticks : ℝ) ≤ (2:ℝ)^96 * Real.log m ∧ (2:ℝ)^96 * Real.log m ≤ (ticks : ℝ) + 24 := by
  have hlog2 : m.log2 ≤ 5 := by
    have hp := Nat.log2_self_le hm.ne'
    by_contra! h
    have hpow : (2:ℕ)^6 ≤ 2^m.log2 :=
      (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).2 (by omega)
    omega
  have hw : (normLogBounds (2^96) 31 m).2 ≤ (normLogBounds (2^96) 31 m).1 + 24 := by
    simp only [normLogBounds, standard_log_error]
    omega
  have hw' : ((normLogBounds (2^96) 31 m).2 : ℝ) ≤ (normLogBounds (2^96) 31 m).1 + 24 := by
    exact_mod_cast hw
  have hEnds := normLogBounds_spec (2^96) 31 m (by decide +kernel) hm
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hEnds
  have hs : (0:ℝ) < 2^96 := by positivity
  constructor
  · simpa only [mul_comm] using (div_le_iff₀ hs).1 hEnds.1
  · exact (by simpa only [mul_comm] using (le_div_iff₀ hs).1 hEnds.2 :
      (2:ℝ)^96 * Real.log m ≤ ((normLogBounds (2^96) 31 m).2 : ℝ)).trans hw'

private theorem log_two_ticks :
    let ticks := logAtanhLowerTicks (2^96) 1 3 31
    (ticks : ℝ) ≤ (2:ℝ)^96 * Real.log 2 ∧ (2:ℝ)^96 * Real.log 2 ≤ (ticks : ℝ) + 4 := by
  have hr : ((1+(1:ℝ)/3) / (1-(1:ℝ)/3)) = 2 := by norm_num
  have h := logAtanhLowerTicks_spec (2^96) 1 3 31 (by decide) (by decide)
  dsimp only at h
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one, hr, standard_log_error] using h

/-- A lower endpoint for `log n` in units of `1 / 2^96`.
The mantissa keeps six leading bits and the remaining ratio uses eight Horner terms. -/
def dottieQuickLogLowerTicks (n : ℕ) : ℕ :=
  let k := n.log2 - 5
  let q : ℕ := 2^k
  let m := n / q
  let b := m*q
  (normLogBounds (2^96) 31 m).1 + k * logAtanhLowerTicks (2^96) 1 3 31 +
    logAtanhLowerTicks (2^96) (n-b) (n+b) 8

/-- The error accumulates four ticks for each binary exponent step, plus
the fixed mantissa and residual errors. -/
theorem dottieQuickLogLowerTicks_spec_of_exponent (n : ℕ) (hn : 0 < n) (steps : ℕ)
    (hk : n.log2 - 5 ≤ steps) :
    (dottieQuickLogLowerTicks n : ℝ) ≤ (2:ℝ)^96 * Real.log n ∧
      (2:ℝ)^96 * Real.log n ≤ (dottieQuickLogLowerTicks n : ℝ) + (28+4*(steps:ℝ)) := by
  let k := n.log2 - 5
  let q : ℕ := 2^k
  let m := n / q
  let b := m*q
  obtain ⟨hm, hmhi, hb, hsmall⟩ := dyadic_mantissa_bounds n hn
  have hm' : 0 < m := hm
  have hq : 0 < q := by positivity
  have hb' : 0 < b := Nat.mul_pos hm' hq
  let r : ℝ := ((n-b : ℕ) : ℝ) / ((n+b : ℕ) : ℝ)
  have hLogB : Real.log b = Real.log m + k * Real.log 2 := by
    change Real.log ((m*q:ℕ) : ℝ) = _
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast hm'.ne') (by exact_mod_cast hq.ne')]
    simp [q, Real.log_pow]
  have hLog : Real.log n = Real.log m + k * Real.log 2 + Real.log ((1+r)/(1-r)) := by
    have h := log_split n b hn hb' hb
    change Real.log n = Real.log b + Real.log ((1+r)/(1-r)) at h
    exact h.trans (by rw [hLogB])
  have hM := mantissa_log_ticks m hm' hmhi
  have hR := residual_log_ticks (n-b) (n+b) (Nat.add_pos_left hn b) hsmall
  have hk' : (k : ℝ) ≤ (steps:ℝ) := by exact_mod_cast (show k ≤ steps from hk)
  have hTwoLower := mul_le_mul_of_nonneg_left log_two_ticks.1 (Nat.cast_nonneg k)
  have hTwoUpper := mul_le_mul_of_nonneg_left log_two_ticks.2 (Nat.cast_nonneg k)
  change (((normLogBounds (2^96) 31 m).1 + k * logAtanhLowerTicks (2^96) 1 3 31 +
      logAtanhLowerTicks (2^96) (n-b) (n+b) 8 : ℕ) : ℝ) ≤ (2:ℝ)^96 * Real.log n ∧
    (2:ℝ)^96 * Real.log n ≤ (((normLogBounds (2^96) 31 m).1 +
      k * logAtanhLowerTicks (2^96) 1 3 31 +
      logAtanhLowerTicks (2^96) (n-b) (n+b) 8 : ℕ) : ℝ) + (28+4*(steps:ℝ))
  rw [hLog]
  simp only [Nat.cast_add, Nat.cast_mul]
  have hsum : (2:ℝ)^96 * (Real.log m + k * Real.log 2 + Real.log ((1+r)/(1-r))) =
      (2:ℝ)^96 * Real.log m + k * ((2:ℝ)^96 * Real.log 2) +
        (2:ℝ)^96 * Real.log ((1+r)/(1-r)) := by ring
  rw [hsum]
  constructor
  · exact add_le_add (add_le_add hM.1 hTwoLower) hR.1
  · exact (add_le_add (add_le_add hM.2 hTwoUpper) hR.2).trans (by nlinarith only [hk'])

private theorem dottie_log2_below {n k : ℕ} (hn : 0 < n) (hcap : n < 2^(k+1)) : n.log2 ≤ k := by
  have hp := Nat.log2_self_le hn.ne'
  by_contra! h
  have hpow : (2:ℕ)^(k+1) ≤ 2^n.log2 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).2 (by omega)
  exact (not_le_of_gt hcap) (hpow.trans hp)

/-- The original 120-tick enclosure through the reference cutoff. -/
theorem dottieQuickLogLowerTicks_spec (n : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064) :
    (dottieQuickLogLowerTicks n : ℝ) ≤ (2:ℝ)^96 * Real.log n ∧
      (2:ℝ)^96 * Real.log n ≤ (dottieQuickLogLowerTicks n : ℝ) + 120 := by
  have hk := dottie_log2_below (k := 28) hn (hcap.trans_lt (by decide +kernel))
  simpa only [Nat.cast_ofNat,show 28+4*(23:ℝ)=120 by norm_num] using
    dottieQuickLogLowerTicks_spec_of_exponent n hn 23 (by omega)

/-- The same executable logarithm through the full sharp moment cutoff. -/
theorem dottieQuickLogLowerTicks_sharp_spec (n : ℕ) (hn : 0 < n) (hcap : n ≤ 1442840576) :
    (dottieQuickLogLowerTicks n : ℝ) ≤ (2:ℝ)^96 * Real.log n ∧
      (2:ℝ)^96 * Real.log n ≤ (dottieQuickLogLowerTicks n : ℝ) + 128 := by
  have hk := dottie_log2_below (k := 30) hn (hcap.trans_lt (by decide +kernel))
  simpa only [Nat.cast_ofNat,show 28+4*(25:ℝ)=128 by norm_num] using
    dottieQuickLogLowerTicks_spec_of_exponent n hn 25 (by omega)

#print axioms residual_log_ticks
#print axioms dottieQuickLogLowerTicks_spec
#print axioms dottieQuickLogLowerTicks_sharp_spec

end QuarticModel
