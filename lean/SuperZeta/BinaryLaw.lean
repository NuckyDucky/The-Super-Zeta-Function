import SuperZeta.BinaryTrig

/-! Recover the rationalized series from the original determinant at unit
coupling. The coefficient at degree n of the normalized trace is Sₙ/2ⁿ. -/
namespace SuperZeta.Binary
open PowerSeries SuperZeta.Spectrum
noncomputable section

theorem scaled_sinc (n : ℕ) :
    sincCoeff n / n.factorial = (-1:ℚ)^n * 2^n / (2*n+1).factorial := by
  induction n with
  | zero => norm_num [sincCoeff]
  | succ n ih =>
    rw [sincCoeff, Nat.factorial_succ, show 2*(n+1)+1= (2*n+1)+1+1 by omega,
      Nat.factorial_succ ((2*n+1)+1), Nat.factorial_succ (2*n+1)]
    push_cast
    rw [pow_succ, pow_succ]
    have hf : (0:ℚ) < (n.factorial : ℚ) := by positivity
    have hg : (0:ℚ) < ((2*n+1).factorial : ℚ) := by positivity
    field_simp at ih ⊢
    linear_combination 2*(2*(n:ℚ)+3)*(n+1)*ih

private theorem scaled_cos (n : ℕ) :
    ((2*(n:ℚ)+1)*sincCoeff n)/n.factorial = (-1:ℚ)^n*2^n/(2*n).factorial := by
  rw [mul_div_assoc, scaled_sinc, Nat.factorial_succ]
  push_cast
  field_simp
  ring

def halfScale := rescale (1/2:ℚ)

theorem determinant_half_scale :
    2 * halfScale (determinant 1) = 1 + cosineSeries - X := by
  ext n
  rw [two_mul, map_add, halfScale, coeff_rescale, determinant, coeff_mk, map_sub, map_add,
    coeff_one, coeff_X, cosineSeries, exponentialSeries, coeff_mk, scaled_cos]
  rcases n with _ | n
  · norm_num [determinantCoeff]
  rcases n with _ | n
  · norm_num [determinantCoeff]
  simp only [determinantCoeff, Nat.add_one_ne_zero, Nat.succ.injEq, if_false,
    zero_add, sub_zero, Nat.reduceEqDiff]
  rw [pow_mul, one_div_pow]
  field_simp
  ring_nf
  rw [show (4:ℚ)^n=2^(n*2) by rw [Nat.mul_comm n 2, pow_mul]; norm_num]

theorem derivative_half_scale :
    halfScale (-(determinant 1).derivativeFun) = 1 + sincSeries := by
  ext n
  rw [halfScale, coeff_rescale, map_neg, coeff_derivativeFun, determinant, coeff_mk,
    map_add, coeff_one, sincSeries, exponentialSeries, coeff_mk, scaled_sinc]
  rcases n with _ | n
  · norm_num [determinantCoeff]
  simp only [determinantCoeff, Nat.add_one_ne_zero, Nat.succ.injEq, if_false, zero_add, sub_zero]
  rw [show 2*(n+1+1) = (2*(n+1)+1)+1 by omega, Nat.factorial_succ, one_div_pow,
    pow_succ (-1:ℚ) (n+1), pow_succ (2:ℚ) (2*(n+1)+1), pow_succ (2:ℚ) (2*(n+1)), pow_mul]
  push_cast
  field_simp
  ring_nf
  rw [show (4:ℚ)^n=2^(n*2) by rw [Nat.mul_comm n 2, pow_mul]; norm_num]

theorem trace_half_scale :
    exponentialSeries normalizedTrace = X * (C ℚ (1/2) * halfScale (traceSeries 1)) := by
  ext n
  cases n with
  | zero => simp [exponentialSeries, normalizedTrace]
  | succ n =>
    rw [coeff_succ_X_mul, coeff_C_mul, halfScale, coeff_rescale, exponentialSeries, coeff_mk,
      normalizedTrace, traceCoeff, one_div_pow, pow_succ]
    field_simp
    ring

theorem trace_cosine_equation :
    exponentialSeries normalizedTrace * (1+cosineSeries-X) = X * (1+sincSeries) := by
  rw [← determinant_half_scale, ← derivative_half_scale, ← determinant_mul_traceSeries,
    trace_half_scale, map_mul]
  have hh : C ℚ (1/2) * 2 = (1 : PowerSeries ℚ) := by
    rw [← map_ofNat (C ℚ) 2, ← map_mul]
    norm_num
  linear_combination X * halfScale (determinant 1) * halfScale (traceSeries 1) * hh

/-- The numerator and denominator are those of the actual normalized trace. -/
theorem normalizedTrace_series : RationalizedSeries normalizedTrace := by
  have hc := correction_identity BinaryTrig.trig_double_cosine
  have h := rationalize_cosine (X_ne_zero (R := ℚ)) BinaryTrig.trig_circle
    BinaryTrig.trig_double trace_cosine_equation
  rw [← hc, numerator_identity] at h
  unfold RationalizedSeries
  apply mul_left_cancel₀ (X_ne_zero (R := ℚ))
  rw [map_ofNat (C ℚ) 2]
  linear_combination h

/-- The valuation of the n+1 trace counts the ones in its binary expansion. -/
theorem trace_digit_law (n : ℕ) :
    padicValRat 2 (traceCoeff 1 n) = (binaryWeight (n+1) : ℤ) :=
  trace_digit_law_of_series normalizedTrace_series n

end
end SuperZeta.Binary
