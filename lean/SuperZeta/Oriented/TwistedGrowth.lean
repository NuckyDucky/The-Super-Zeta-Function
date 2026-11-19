import SuperZeta.Oriented.TraceRecovery

/-!
# Global growth and simple zeros of the positive-stage determinant

The only phase restriction is the nonzero normalizing factor `cos φ`.
-/

namespace DottieOriented.TraceRecovery

noncomputable section

private theorem hasDerivAt_characteristic (φ : ℝ) (z : ℂ) :
    HasDerivAt (signedCharacteristic 1 φ) (1 + Complex.sin (z - (φ : ℂ))) z := by
  unfold signedCharacteristic
  simpa [sub_eq_add_neg] using
    ((hasDerivAt_id' z).sub (((hasDerivAt_id' z).sub_const (φ : ℂ)).ccos))

private theorem characteristic_slope_ne_zero {φ : ℝ} (hφ : Real.cos φ ≠ 0) {z : ℂ}
    (hz : signedCharacteristic 1 φ z = 0) : 1 + Complex.sin (z - (φ : ℂ)) ≠ 0 := by
  have he : z = Complex.cos (z - (φ : ℂ)) := by
    simpa [signedCharacteristic, sub_eq_zero] using hz
  intro hs
  have hsin : Complex.sin (z - (φ : ℂ)) = -1 := by linear_combination hs
  have hsq := Complex.cos_sq_add_sin_sq (z - (φ : ℂ))
  rw [← he, hsin] at hsq
  have hzero : z ^ 2 = 0 := by linear_combination hsq
  have hcos := he.symm.trans (pow_eq_zero hzero)
  have hcz : Complex.cos (φ : ℂ) = 0 := by
    simpa [pow_eq_zero hzero, Complex.cos_neg] using hcos
  exact hφ (by exact_mod_cast hcz)

/-- A characteristic root and its antipode cannot both belong to the positive stage. -/
private theorem opposite_characteristic_ne_zero {φ : ℝ} (hφ : Real.cos φ ≠ 0) {z : ℂ}
    (hz : signedCharacteristic 1 φ z = 0) : signedCharacteristic 1 φ (-z) ≠ 0 := by
  intro hn
  simp only [signedCharacteristic, Complex.ofReal_one, one_mul, sub_eq_zero, Complex.cos_sub,
    Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hz hn
  have hφC : (Real.cos φ : ℂ) ≠ 0 := by exact_mod_cast hφ
  have hp : Complex.cos z * (Real.cos φ : ℂ) = 0 := by
    linear_combination -(hz + hn) / 2
  have hcz : Complex.cos z = 0 := (mul_eq_zero.mp hp).resolve_right hφC
  have hsq := Complex.cos_sq_add_sin_sq z
  simp only [hcz, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_add] at hsq
  have hz' : z = Complex.sin z * (Real.sin φ : ℂ) := by simpa [hcz] using hz
  have hreal : ∃ x : ℝ, z = (x : ℂ) ∧ |x| ≤ 1 := by
    have hs : |Real.sin φ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin φ, Real.sin_le_one φ⟩
    rcases sq_eq_one_iff.mp hsq with h | h
    · exact ⟨Real.sin φ, by simpa [h] using hz', hs⟩
    · exact ⟨-Real.sin φ, by simpa [h] using hz', by simpa using hs⟩
  obtain ⟨x, hx, hbound⟩ := hreal
  have hpos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [(abs_le.mp hbound).1, Real.pi_gt_three],
     by linarith [(abs_le.mp hbound).2, Real.pi_gt_three]⟩
  rw [hx] at hcz
  exact hpos.ne' (by exact_mod_cast hcz)

private theorem deriv_signedDet_ne_zero_of_characteristic_zero {φ : ℝ} (hφ : Real.cos φ ≠ 0)
    {z : ℂ} (hz : signedCharacteristic 1 φ z = 0) : deriv (signedDet 1 φ) (z ^ 2) ≠ 0 := by
  intro hzero
  have hdet := (signedDet_analytic 1 φ (z ^ 2)).differentiableAt.hasDerivAt.comp z
    ((hasDerivAt_id' z).pow 2)
  rw [hzero, zero_mul] at hdet
  have hneg := (hasDerivAt_characteristic φ (-z)).comp z (hasDerivAt_id' z).neg
  have hprod := ((hasDerivAt_characteristic φ z).mul hneg).div_const ((Real.cos φ : ℂ) ^ 2)
  have hd : HasDerivAt (fun w : ℂ => signedDet 1 φ (w ^ 2))
      ((1 + Complex.sin (z - (φ : ℂ))) * signedCharacteristic 1 φ (-z) /
        (Real.cos φ : ℂ) ^ 2) z := by
    have he : (fun w : ℂ => signedDet 1 φ (w ^ 2)) =
        (fun w => signedCharacteristic 1 φ w * signedCharacteristic 1 φ (-w) /
          (Real.cos φ : ℂ) ^ 2) :=
      funext (signedDet_sq (by norm_num : (1 : ℝ) ^ 2 = 1) φ)
    rw [he]
    simpa only [Function.comp_def, id_eq, hz, zero_mul, add_zero, zero_add] using hprod
  have hne : (Real.cos φ : ℂ) ≠ 0 := by exact_mod_cast hφ
  exact (div_ne_zero (mul_ne_zero (characteristic_slope_ne_zero hφ hz)
    (opposite_characteristic_ne_zero hφ hz)) (pow_ne_zero _ hne)) (hd.unique hdet)

theorem signedDet_simple {φ : ℝ} (hφ : Real.cos φ ≠ 0) {v : ℂ}
    (hv : signedDet 1 φ v = 0) : deriv (signedDet 1 φ) v ≠ 0 := by
  obtain ⟨z, rfl⟩ : ∃ z : ℂ, z ^ 2 = v :=
    ⟨_, Complex.cpow_nat_inv_pow v (n := 2) (by decide)⟩
  rcases (signedDet_zero_iff (by norm_num : (1 : ℝ) ^ 2 = 1) hφ z).mp hv with h | h
  · exact deriv_signedDet_ne_zero_of_characteristic_zero hφ h
  · simpa only [neg_sq] using deriv_signedDet_ne_zero_of_characteristic_zero hφ h

private theorem norm_cos_le_exp (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp ‖z‖ := by
  have he (w : ℂ) : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp ‖w‖ := by
    simpa [norm_mul] using Complex.norm_exp_le_exp_norm (w * Complex.I)
  rw [Complex.cos, norm_div]
  have h := (norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))).trans
    (add_le_add (he z) (he (-z)))
  simp only [norm_neg, Complex.norm_ofNat] at *
  linarith

private theorem norm_characteristic_le (φ : ℝ) (z : ℂ) :
    ‖signedCharacteristic 1 φ z‖ ≤ 2 * Real.exp (‖z‖ + |φ|) := by
  have hc : ‖Complex.cos (z - (φ : ℂ))‖ ≤ Real.exp (‖z‖ + |φ|) :=
    (norm_cos_le_exp _).trans (Real.exp_le_exp.mpr (by simpa using norm_sub_le z (φ : ℂ)))
  have he : Real.exp ‖z‖ ≤ Real.exp (‖z‖ + |φ|) :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_right (abs_nonneg _))
  simp only [signedCharacteristic, Complex.ofReal_one, one_mul]
  exact (norm_sub_le _ _).trans (by linarith [Real.add_one_le_exp ‖z‖])

/-- A global order-one-half growth bound in the squared spectral variable. -/
theorem signedDet_growth_prefactor {φ : ℝ} (hφ : Real.cos φ ≠ 0) (v : ℂ) :
    ‖signedDet 1 φ v‖ ≤
      (4 * Real.exp (2 * |φ|) / |Real.cos φ| ^ 2) * Real.exp (2 * Real.sqrt ‖v‖) := by
  obtain ⟨z, rfl⟩ : ∃ z : ℂ, z ^ 2 = v :=
    ⟨_, Complex.cpow_nat_inv_pow v (n := 2) (by decide)⟩
  rw [signedDet_sq (by norm_num : (1 : ℝ) ^ 2 = 1), norm_div, norm_mul, norm_pow,
    Complex.norm_real, norm_pow, Real.sqrt_sq (norm_nonneg _)]
  have hp := norm_characteristic_le φ z
  have hm : ‖signedCharacteristic 1 φ (-z)‖ ≤ 2 * Real.exp (‖z‖ + |φ|) := by
    simpa only [norm_neg] using norm_characteristic_le φ (-z)
  calc
    _ ≤ (2 * Real.exp (‖z‖ + |φ|)) ^ 2 / |Real.cos φ| ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      rw [sq]
      exact mul_le_mul hp hm (norm_nonneg _) (by positivity)
    _ = _ := by
      field_simp [abs_ne_zero.mpr hφ]
      simp only [two_mul, Real.exp_add]
      ring

/-- The constant in the exponential bound may depend on the phase. -/
theorem signedDet_growth {φ : ℝ} (hφ : Real.cos φ ≠ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ v : ℂ, ‖signedDet 1 φ v‖ ≤ Real.exp (K * (Real.sqrt ‖v‖ + 1)) := by
  let C := 4 * Real.exp (2 * |φ|) / |Real.cos φ| ^ 2
  have hC : 0 < C := by
    have hc : 0 < |Real.cos φ| := abs_pos.mpr hφ
    dsimp [C]
    positivity
  refine ⟨2 + |Real.log C|, by positivity, fun v => ?_⟩
  calc
    _ ≤ C * Real.exp (2 * Real.sqrt ‖v‖) := signedDet_growth_prefactor hφ v
    _ = Real.exp (Real.log C + 2 * Real.sqrt ‖v‖) := by rw [Real.exp_add, Real.exp_log hC]
    _ ≤ Real.exp ((2 + |Real.log C|) * (Real.sqrt ‖v‖ + 1)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [le_abs_self (Real.log C), mul_nonneg (abs_nonneg (Real.log C)) (Real.sqrt_nonneg ‖v‖)]

end

end DottieOriented.TraceRecovery
