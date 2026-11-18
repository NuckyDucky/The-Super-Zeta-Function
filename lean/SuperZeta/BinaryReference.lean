import SuperZeta.BinaryLaw

/-! The binary law for the unperturbed cosine determinant. -/
namespace SuperZeta.Binary
open PowerSeries SuperZeta.Spectrum
noncomputable section

/-- Factorial-normalized coefficients of twice the half-scaled reference trace. -/
def twiceReference : ℕ → ℚ
  | 0 => 0
  | n+1 => ((n+1).factorial:ℚ) * (2*traceCoeff 0 n) / 2^(n+1)

private lemma ref_det : determinant 0 = determinant 1 + X := by
  ext n
  simp only [determinant, coeff_mk, map_add, coeff_X, determinantCoeff]
  split_ifs <;> ring

private lemma ref_scale :
    exponentialSeries twiceReference = X * halfScale (traceSeries 0) := by
  ext n
  cases n with
  | zero => simp [exponentialSeries, twiceReference]
  | succ n =>
    rw [coeff_succ_X_mul, halfScale, coeff_rescale, exponentialSeries, coeff_mk,
      twiceReference, traceCoeff, one_div_pow, pow_succ]
    field_simp
    ring

theorem reference_cosine_equation :
    exponentialSeries twiceReference * (1+cosineSeries) = 2*X*sincSeries := by
  have hh : C ℚ (1/2) * 2 = (1 : PowerSeries ℚ) := by
    rw [← map_ofNat (C ℚ) 2, ← map_mul]
    norm_num
  have hd : 2 * halfScale (determinant 0) = 1+cosineSeries := by
    rw [ref_det, map_add]
    have hx : halfScale X = C ℚ (1/2)*X := rescale_X _
    rw [hx]
    linear_combination determinant_half_scale + X*hh
  have hs : halfScale (-(determinant 0).derivativeFun) = sincSeries := by
    have hx : (X : PowerSeries ℚ).derivativeFun = 1 := derivative_X
    rw [ref_det, derivativeFun_add, hx, neg_add, map_add,
      derivative_half_scale, map_neg, map_one]
    ring
  rw [← hd, ← hs, ← determinant_mul_traceSeries, map_mul, ref_scale]
  ring

/-- An identity of actual reference determinant traces, before reduction mod 2. -/
theorem reference_convolution :
    exponentialSeries twiceReference * sincSeries = 1-cosineSeries := by
  have h₀ : 1 + cosineSeries ≠ 0 := by
    intro h
    have hc := congrArg (coeff ℚ 0) h
    norm_num [cosineSeries, exponentialSeries, sincCoeff] at hc
  apply mul_right_cancel₀ h₀
  linear_combination sincSeries * reference_cosine_equation + BinaryTrig.trig_circle

private def Small (a : ℚ) : Prop := padicNorm 2 a ≤ 1/2

private lemma small_add {a b : ℚ} (ha : Small a) (hb : Small b) : Small (a+b) :=
  padicNorm.nonarchimedean.trans (max_le ha hb)

private lemma small_neg {a : ℚ} (ha : Small a) : Small (-a) := by
  simpa [Small, padicNorm.neg] using ha

private lemma small_mul {a b : ℚ} (ha : Small a) (hb : padicNorm 2 b ≤ 1) :
    Small (a*b) := by
  unfold Small at *
  rw [padicNorm.mul]
  simpa only [mul_one] using mul_le_mul ha hb (padicNorm.nonneg _) (by norm_num : (0:ℚ)≤1/2)

private lemma two_small : Small 2 := by
  unfold Small
  rw [show padicNorm 2 (2:ℚ)=1/2 by
    simpa [one_div] using (padicNorm.padicNorm_p (p:=2) (by decide))]

private lemma sinc_close (n : ℕ) : Small (sincCoeff n - 1) := by
  induction n with
  | zero => norm_num [sincCoeff, Small, padicNorm.zero]
  | succ n ih =>
    have hd : padicNorm 2 (2*(n:ℚ)+3) = 1 := by
      exact_mod_cast (padicNorm.nat_eq_one_iff (p:=2) (m:=2*n+3)).2 (by omega)
    have hs := small_neg (small_add ih (small_mul two_small
      (b := ((n+2:ℕ):ℚ)) (padicNorm.of_nat _)))
    unfold Small at *
    rw [sincCoeff, show -sincCoeff n/(2*(n:ℚ)+3)-1 =
      -((sincCoeff n-1)+2*((n+2:ℕ):ℚ))/(2*n+3) by push_cast; field_simp; ring,
      padicNorm.div, hd, div_one]
    exact hs

private lemma sinc_bounded (n : ℕ) : padicNorm 2 (sincCoeff n) ≤ 1 := by
  have he := sinc_close n
  unfold Small at he
  calc
    padicNorm 2 (sincCoeff n) = padicNorm 2 ((sincCoeff n-1)+1) := by ring_nf
    _ ≤ _ := padicNorm.nonarchimedean
    _ ≤ 1 := max_le (by linarith) padicNorm.one.le

private lemma cosine_close (n : ℕ) : Small ((2*(n:ℚ)+1)*sincCoeff n - 1) := by
  rw [show (2*(n:ℚ)+1)*sincCoeff n-1 = (sincCoeff n-1) + (2*n)*sincCoeff n by ring]
  exact small_add (sinc_close n) (small_mul (small_mul two_small (padicNorm.of_nat _)) (sinc_bounded n))

private lemma reference_relation (n : ℕ) :
    (∑ j ∈ Finset.range n, ((n+1).choose (j+1):ℚ)*twiceReference (j+1)*sincCoeff ((n+1)-(j+1))) +
      twiceReference (n+1) = -((2*((n+1:ℕ):ℚ)+1)*sincCoeff (n+1)) := by
  have he := (exponential_product_coeff twiceReference sincCoeff (n+1)).symm
  rw [← show sincSeries = exponentialSeries sincCoeff from rfl, reference_convolution] at he
  rw [map_sub, coeff_one, cosineSeries, exponentialSeries, coeff_mk,
    Finset.sum_range_succ, Finset.sum_range_succ'] at he
  push_cast at he ⊢
  simp only [Nat.succ_ne_zero, if_false, zero_sub, Nat.choose_self, Nat.cast_one, one_mul,
    Nat.sub_self, show twiceReference 0 = 0 from rfl, show sincCoeff 0 = 1 from rfl, mul_one, Nat.choose_zero_right, mul_zero,
    zero_mul, add_zero] at he
  convert he using 1
  field_simp
  ring

private lemma middle_choose (n : ℕ) :
    (∑ j ∈ Finset.range n, ((n+1).choose (j+1):ℚ))+2 = 2^(n+1) := by
  have hs := Nat.sum_range_choose (n+1)
  rw [Finset.sum_range_succ, Finset.sum_range_succ'] at hs
  simp only [Nat.choose_self, Nat.choose_zero_right] at hs
  exact_mod_cast (show (∑ j ∈ Finset.range n, (n+1).choose (j+1))+2 = 2^(n+1) by omega)

private theorem reference_close (n : ℕ) : Small (twiceReference (n+1)-1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let b (j : ℕ) : ℚ := (n+1).choose (j+1)
    let term (j : ℕ) := twiceReference (j+1)*sincCoeff ((n+1)-(j+1))
    have hterms : Small (∑ j ∈ Finset.range n, b j*(term j-1)) := by
      apply padicNorm.sum_le' _ (by norm_num)
      intro j hj
      have hsmall := ih j (Finset.mem_range.mp hj)
      have hr : Small (term j-1) := by
        dsimp [term]
        rw [show twiceReference (j+1)*sincCoeff ((n+1)-(j+1))-1 =
          (twiceReference (j+1)-1)*sincCoeff ((n+1)-(j+1)) + (sincCoeff ((n+1)-(j+1))-1) by ring]
        exact small_add (small_mul hsmall (sinc_bounded _)) (sinc_close _)
      rw [mul_comm]
      exact small_mul hr (padicNorm.of_nat _)
    have hpow : Small ((2:ℚ)^(n+1)) := by
      rw [pow_succ, mul_comm]
      exact small_mul two_small (by exact_mod_cast padicNorm.of_nat (p:=2) (2^n))
    have h := reference_relation n
    have hsum : (∑ j ∈ Finset.range n, b j*(term j-1)) =
      (∑ j ∈ Finset.range n, b j*term j) - ∑ j ∈ Finset.range n, b j := by
      simp [mul_sub, Finset.sum_sub_distrib]
    have h' : (∑ j ∈ Finset.range n, b j*term j) + twiceReference (n+1) =
        -((2*((n+1:ℕ):ℚ)+1)*sincCoeff (n+1)) := by
      simpa [b, term, mul_assoc] using h
    have he : twiceReference (n+1)-1 =
      -(((2*((n+1:ℕ):ℚ)+1)*sincCoeff (n+1)-1) +
        ((∑ j ∈ Finset.range n, b j*(term j-1)) + (2:ℚ)^(n+1))) := by
      have hc : (∑ j ∈ Finset.range n, b j) + 2 = (2:ℚ)^(n+1) := middle_choose n
      linarith only [hsum, h', hc]
    rw [he]
    exact small_neg (small_add (cosine_close (n+1)) (small_add hterms hpow))

theorem twice_reference_unit (n : ℕ) : padicNorm 2 (twiceReference (n+1)) = 1 := by
  have h := reference_close n
  unfold Small at h
  have he : padicNorm 2 (twiceReference (n+1)-1) < padicNorm 2 1 := by
    rw [padicNorm.one]
    linarith
  calc
    _ = padicNorm 2 ((twiceReference (n+1)-1)+1) := by ring_nf
    _ = _ := padicNorm.add_eq_max_of_ne he.ne
    _ = _ := (max_eq_right he.le).trans padicNorm.one

private theorem reference_ne_zero (n : ℕ) : traceCoeff 0 n ≠ 0 := by
  intro h
  have he := twice_reference_unit n
  norm_num [twiceReference, h, padicNorm.zero] at he

/-- The reference trace has one fewer factor of 2 than the coupled trace. -/
theorem reference_digit_law (n : ℕ) :
    padicValRat 2 (traceCoeff 0 n) = (binaryWeight (n+1):ℤ)-1 := by
  have h := twice_reference_unit n
  have hn : twiceReference (n+1) ≠ 0 := by
    intro e
    norm_num [e, padicNorm.zero] at h
  rw [padicNorm.eq_zpow_of_nonzero hn, zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)] at h
  have h' : padicValRat 2 (twiceReference (n+1)) = 0 := by omega
  have hval := (normalized_unit_iff (n+1) (mul_ne_zero (by norm_num : (2:ℚ) ≠ 0)
    (reference_ne_zero n))).mp h'
  rw [padicValRat.mul (by norm_num) (reference_ne_zero n),
    show padicValRat 2 (2:ℚ)=1 from padicValRat.self (by decide)] at hval
  omega

/-- The difference of the actual and reference determinant traces inherits
the smaller valuation, degree by degree. -/
theorem correction_digit_law (n : ℕ) :
    padicValRat 2 (traceCoeff 1 n-traceCoeff 0 n) = (binaryWeight (n+1):ℤ)-1 := by
  have h := trace_digit_law n
  have h' := reference_digit_law n
  have hn : traceCoeff 1 n ≠ 0 := by
    intro e
    rw [e, padicValRat.zero] at h
    have hp : 0 < binaryWeight (n+1) := by
      unfold binaryWeight
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 (by omega : n+1≠0)))
        (List.le_sum_of_mem (List.getLast_mem _))
    omega
  have hd : traceCoeff 1 n - traceCoeff 0 n ≠ 0 := by
    intro e
    rw [sub_eq_zero.mp e] at h
    omega
  have hv : padicValRat 2 (traceCoeff 1 n) ≠ padicValRat 2 (-traceCoeff 0 n) := by
    rw [padicValRat.neg]
    omega
  rw [sub_eq_add_neg] at hd ⊢
  rw [padicValRat.add_eq_min hd hn (neg_ne_zero.mpr (reference_ne_zero n)) hv,
    padicValRat.neg, h, h', min_eq_right (by omega)]

end
end SuperZeta.Binary
