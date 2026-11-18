import SuperZeta.Binary

/-! Coefficient identities for the rationalized cosine determinant, in the
variable y with z²=2y. The power series have rational coefficients. -/
namespace SuperZeta.Binary

noncomputable def cosineSeries := exponentialSeries (fun n => (2*(n:ℚ)+1)*sincCoeff n)
noncomputable def sincSeries := exponentialSeries sincCoeff
noncomputable def doubleSincSeries := exponentialSeries (fun n => (4:ℚ)^n*sincCoeff n)
noncomputable def doubleCosineSeries := exponentialSeries (fun n => (4:ℚ)^n*((2*(n:ℚ)+1)*sincCoeff n))

open PowerSeries

private theorem coeff_X_series (f : PowerSeries ℚ) (n : ℕ) :
    coeff ℚ (n+1) (X*f) = coeff ℚ n f := by
  simpa only [pow_one] using coeff_X_pow_mul f 1 n

private theorem quot_four (n : ℕ) : fourPowerQuot n = (4:ℚ)^(n+1)/(n+1) := by
  unfold fourPowerQuot
  rw [pow_mul]
  norm_num

theorem numerator_identity :
    1 - cosineSeries + sincSeries - doubleSincSeries - X*(1+sincSeries) =
    X*exponentialSeries numeratorCoeff := by
  ext n
  cases n with
  | zero =>
    norm_num [cosineSeries, sincSeries, doubleSincSeries, exponentialSeries, sincCoeff]
  | succ n =>
    simp only [map_add, map_sub, coeff_one, coeff_X_series, cosineSeries, sincSeries,
      doubleSincSeries, exponentialSeries, coeff_mk, numeratorCoeff, quot_four,
      Nat.succ_ne_zero, if_false, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    by_cases h : n = 0
    · subst n
      norm_num [sincCoeff]
    · simp only [if_neg h, sub_zero, zero_add]
      field_simp
      ring

/-- Identify the correction sequence with the second divided difference of
the doubled cosine, before using the trigonometric double-angle theorem. -/
theorem double_cosine_correction :
    1-doubleCosineSeries = (4:PowerSeries ℚ)*(X*(1+X*exponentialSeries correctionCoeff)) := by
  have hfour : (4:PowerSeries ℚ) = C ℚ 4 := (map_ofNat (C ℚ) 4).symm
  rw [hfour]
  ext n
  cases n with
  | zero => norm_num [doubleCosineSeries, exponentialSeries, sincCoeff]
  | succ n =>
    cases n with
    | zero =>
      norm_num [doubleCosineSeries, exponentialSeries, sincCoeff, coeff_X_series]
    | succ n =>
      simp only [map_sub, coeff_one, Nat.succ_ne_zero, if_false, doubleCosineSeries,
        exponentialSeries, coeff_mk, coeff_C_mul, coeff_X_series, map_add, zero_add,
        correctionCoeff, quot_four, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [show sincCoeff (n+1+1) = -sincCoeff (n+1) / (2*((n:ℚ)+1)+3) by
        rw [sincCoeff]; push_cast; rfl]
      simp only [pow_succ]
      field_simp
      ring

theorem correction_identity
    (h : 4*(X : PowerSeries ℚ)*sincSeries^2 = 1-doubleCosineSeries) :
    X*exponentialSeries correctionCoeff = sincSeries^2-1 := by
  rw [double_cosine_correction] at h
  have h4 : (4:PowerSeries ℚ) ≠ 0 := by
    intro e
    have h₀ := congrArg (PowerSeries.constantCoeff ℚ) e
    norm_num [map_ofNat] at h₀
  rw [mul_assoc] at h
  have hx := mul_left_cancel₀ (X_ne_zero (R := ℚ)) (mul_left_cancel₀ h4 h)
  linear_combination -hx

end SuperZeta.Binary
