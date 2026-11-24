import SuperZeta.Reference

/-! The first Taylor subtraction for the relative determinant on its Mellin ray. -/
noncomputable section
namespace SuperZeta.Reference
open Complex Asymptotics Filter
open scoped Topology

/-- A pointwise error bound for extracting the linear term from the real logarithm. -/
theorem log_first_error {y : ℝ} (hy : 0 ≤ y) :
    0 ≤ y - Real.log (1+y) ∧ y - Real.log (1+y) ≤ y^2 := by
  have hp : 0 < 1+y := by linarith
  have hupper := Real.log_le_sub_one_of_pos hp
  have hlower := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hlower
  have hl : y/(1+y) ≤ Real.log (1+y) := by
    have h : y/(1+y) = 1-(1+y)⁻¹ := by
      field_simp
      ring
    linarith [h]
  refine ⟨by linarith, ?_⟩
  calc y - Real.log (1+y) ≤ y - y/(1+y) := by linarith
       _ = y^2/(1+y) := by field_simp; ring
       _ ≤ y^2 := div_le_self (sq_nonneg _) (by linarith)

/-- At x=√t, subtracting q*x² leaves an O(x⁴) error, uniformly near zero
for each fixed nonnegative inverse squared coupling q. -/
theorem kernel_remainder_at_zero {q : ℝ} (hq : 0 ≤ q) :
    (fun x : ℝ => logKernel q x - ((q*x^2 : ℝ):ℂ)) =O[𝓝[>] 0]
      (fun x : ℝ => x ^ (-(-4 : ℝ))) := by
  have hs : Real.sinh =O[𝓝 0] (fun x : ℝ => x) := by
    simpa using (Real.hasDerivAt_sinh 0).isBigO_sub
  obtain ⟨c, hc, hbound⟩ := hs.exists_pos
  refine isBigO_iff.mpr ⟨q*c^2+q^2, ?_⟩
  filter_upwards [hbound.bound.filter_mono nhdsWithin_le_nhds] with x hx
  let y := q*(x/Real.cosh x)^2
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hyx : y ≤ q*x^2 := by
    dsimp [y]
    rw [div_pow]
    exact mul_le_mul_of_nonneg_left (div_le_self (sq_nonneg x) (one_le_pow₀ (Real.one_le_cosh x))) hq
  have hid : q*x^2 = y + y*(Real.sinh x)^2 := by
    dsimp [y]
    rw [div_pow]
    field_simp [(Real.cosh_pos x).ne']
    nlinarith only [Real.cosh_sq_sub_sinh_sq x, mul_self_nonneg x,
      congrArg (fun z : ℝ => q*x^2*z) (Real.cosh_sq_sub_sinh_sq x)]
  have hsq : (Real.sinh x)^2 ≤ c^2*x^2 := by
    rw [← mul_pow, ← sq_abs (Real.sinh x), ← sq_abs (c*x), abs_mul, abs_of_pos hc]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have hy2 := pow_le_pow_left₀ hy hyx 2
  have herr := log_first_error hy
  have hsub : Real.log (1+y) ≤ q*x^2 := by linarith
  have hb := mul_le_mul hyx hsq (sq_nonneg _) (mul_nonneg hq (sq_nonneg x))
  change ‖((Real.log (1+y) : ℝ):ℂ)-((q*x^2:ℝ):ℂ)‖ ≤ _
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hsub)]
  have hr : x ^ (-(-4:ℝ)) = x^(4:ℕ) := by
    rw [neg_neg]
    exact Real.rpow_natCast x 4
  rw [hr, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ x^(4:ℕ))]
  nlinarith only [herr.2, hid, hb, hy2]

end SuperZeta.Reference
