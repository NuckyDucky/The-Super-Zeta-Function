import SuperZeta.CapRecovery.DyadicCap

/-! Reweighting the nontrivial sign character. The offset 1 is the
trivial-character contribution to the logarithmic Euler coefficients. -/

noncomputable section
namespace SuperZeta.GeneralWeights

open FieldWeights SignWords DyadicWeights CapJets

/-- One coefficient at a nontrivial order-two prime reads the signed product
of the prefix. The real weight and the baseline are known to the decoder. -/
theorem recover_prefix (w : List Sign) (b : ℝ) (hb : b ≠ 0) :
    (primePowerWeight b (-1) (exponent w) - 1) / b = signProduct w := by
  unfold primePowerWeight
  rw [dyadic_parity]
  field_simp

/-- A fixed scaling of the prime reading can be removed throughout the finite
derivative polynomial, evaluated at the actual signed stages at the cap. -/
theorem cap_ratio_weight (w : List Sign) (b : ℝ) (hb : b ≠ 0) :
    deriv (deriv (eval lift w)) 1 / deriv (eval lift w) 1 =
    lift * ∑ j ∈ Finset.range w.length,
      (((primePowerWeight b (-1) (exponent (w.take (j+1))) - 1) / b : ℝ) : ℂ) *
        (-lift)^j := by
  rw [jet_ratio, (DyadicCap.jet_prefixes w).2]
  unfold DyadicCap.polynomial
  simp_rw [recover_prefix _ b hb]

/-- The trivial local character value is constant under all powers. -/
theorem trivial_character_weight (b : ℝ) (k : ℕ) :
    primePowerWeight b 1 k = 1+b := by simp [primePowerWeight]

/-- A ramified local character is zero at every positive power, so the
combined weight consists of the trivial-character part. -/
theorem ramified_weight (b : ℝ) (k : ℕ) :
    primePowerWeight b 0 (k+1) = 1 := by simp [primePowerWeight]

/-- Zero scaling erases every mark even at a nontrivial local character. -/
theorem same_when_weight_zero (c : ℝ) (k : ℕ) :
    primePowerWeight 0 c k = 1 := by simp [primePowerWeight]

/-- Two consecutive positive powers suffice to calibrate the nontrivial
local reading; their difference is twice the weight, including its sign. -/
theorem opposite_readings (b : ℝ) (k : ℕ) :
    primePowerWeight b (-1) (2*k+2) - primePowerWeight b (-1) (2*k+1) = 2*b := by
  norm_num [primePowerWeight, pow_add, pow_mul]
  ring

/-- An external uncentered endpoint coefficient and the first cap derivative
determine even an unknown real weight, with no prior sign or nonvanishing
assumption on the weight itself. -/
theorem calibrate_weight (w : List Sign) (b : ℝ) :
    ((primePowerWeight b (-1) (exponent w) - 1 : ℝ) : ℂ) *
        (-lift)^w.length / deriv (eval lift w) 1 = (b : ℂ) := by
  have hn : deriv (eval lift w) 1 ≠ 0 := (jet_correct w).1.symm ▸ first_ne_zero w
  apply (div_eq_iff hn).mpr
  rw [(jet_correct w).1, (DyadicCap.jet_prefixes w).1]
  simp [primePowerWeight, dyadic_parity]
  ring

end SuperZeta.GeneralWeights
