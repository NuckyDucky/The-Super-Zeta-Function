import DedekindDiskTaylorError
import DedekindTaylorCoefficientError
import Mathlib.Analysis.Calculus.Deriv.ZPow

/-! Exact finite Mellin integrals for the coefficients used by the field's
polynomial disk certificate, with the poles evaluated separately. -/

namespace FieldTarget

open Complex Metric
open DedekindZetaZeroFree.AbelianQuotient
open scoped NNReal Interval Topology

noncomputable section

theorem iteratedDeriv_mixedThetaPole_eq (a : ℂ) (n : ℕ) {c : ℂ}
    (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    iteratedDeriv n (fun w : ℂ ↦ a / (w * (1 - w))) c =
      a * (n.factorial : ℂ) * ((-1 : ℂ) ^ n / c ^ (n + 1) + 1 / (1 - c) ^ (n + 1)) := by
  have h0 : {w : ℂ | w ≠ 0} ∈ 𝓝 c := isOpen_ne.mem_nhds hc0
  have h1 : {w : ℂ | w ≠ 1} ∈ 𝓝 c := isOpen_ne.mem_nhds hc1
  have hEq : (fun w : ℂ ↦ a / (w * (1 - w))) =ᶠ[𝓝 c]
      (fun w : ℂ ↦ a * (w⁻¹ + (1 - w)⁻¹)) := by
    filter_upwards [h0, h1] with w hw0 hw1
    change w ≠ 1 at hw1
    field_simp [hw0, sub_ne_zero.mpr hw1.symm]
    ring
  have hSub : ContDiff ℂ n (fun w : ℂ ↦ 1 - w) := contDiff_const.sub contDiff_id
  have hLeft : ContDiffAt ℂ n (fun w : ℂ ↦ w⁻¹) c := contDiff_id.contDiffAt.inv hc0
  have hRight : ContDiffAt ℂ n (fun w : ℂ ↦ (1 - w)⁻¹) c :=
    hSub.contDiffAt.inv (sub_ne_zero.mpr hc1.symm)
  have hZ (z : ℂ) : z ^ (-1 - (n : ℤ)) = (z ^ (n + 1))⁻¹ := by
    rw [show -1 - (n : ℤ) = -((n + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast]
  have hL : iteratedDeriv n (fun w : ℂ ↦ w⁻¹) c =
      (-1 : ℂ) ^ n * (n.factorial : ℂ) * (c ^ (n + 1))⁻¹ := by
    rw [iteratedDeriv_eq_iterate]
    simpa only [hZ] using iter_deriv_inv n c
  have hR : iteratedDeriv n (fun w : ℂ ↦ (1 - w)⁻¹) c =
      (n.factorial : ℂ) * ((1 - c) ^ (n + 1))⁻¹ := by
    have hArg : (fun w : ℂ ↦ ((-1 : ℂ) * w + 1)⁻¹) =
        (fun w : ℂ ↦ (1 - w)⁻¹) := by
      funext w
      congr 1
      ring
    have hEval : (-1 : ℂ) * c + 1 = 1 - c := by ring
    have hSign : (-1 : ℂ) ^ n * (n.factorial : ℂ) * (-1) ^ n = (n.factorial : ℂ) := by
      calc
        _ = (((-1 : ℂ) ^ n) * (-1) ^ n) * (n.factorial : ℂ) := by ac_rfl
        _ = _ := by rw [← mul_pow]; simp
    rw [iteratedDeriv_eq_iterate, ← hArg]
    simpa only [hEval, hZ, hSign] using congrFun (iter_deriv_inv_linear n (-1 : ℂ) 1) c
  rw [hEq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field]
  change a * iteratedDeriv n ((fun w : ℂ ↦ w⁻¹) + fun w : ℂ ↦ (1 - w)⁻¹) c = _
  rw [iteratedDeriv_add hLeft hRight, hL, hR]
  simp only [div_eq_mul_inv, one_mul]
  ring

/-- A finite folded Mellin moment, divided by the factorial, minus the exact
two contributions from the poles at zero and one. -/
def mixedThetaCompletedMomentCoeff (K : Type) [Field K] [NumberField K]
    (cut : ℝ) (c : ℂ) (n : ℕ) : ℂ :=
  (∫ x in (1 : ℝ)..cut, foldedMellinLogWeight n c x *
      ((Theta.mixedThetaPair K).f x - (Theta.mixedThetaPair K).f₀)) / (n.factorial : ℂ) -
    (Theta.mixedThetaPair K).f₀ *
      ((-1 : ℂ) ^ n / c ^ (n + 1) + 1 / (1 - c) ^ (n + 1))

theorem mixedTheta_completed_taylorCoeff_eq_moment (K : Type) [Field K] [NumberField K]
    {cut : ℝ} {ρ : ℝ≥0} {c : ℂ} (hcut : 1 ≤ cut) (hρ : 0 < ρ)
    (hLeft : (ρ : ℝ) < c.re) (hRight : (ρ : ℝ) < 1 - c.re) (n : ℕ) :
    contourTaylorCoeff (mixedThetaCompletedTruncation K cut) c ρ n =
      mixedThetaCompletedMomentCoeff K cut c n := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (not_lt_of_ge ρ.coe_nonneg) (by simpa only [zero_re] using hLeft)
  have hc1 : c ≠ 1 := by
    rintro rfl
    exact (not_lt_of_ge ρ.coe_nonneg) (by simpa only [one_re, sub_self] using hRight)
  have hDen : ContDiff ℂ n (fun w : ℂ ↦ w * (1 - w)) :=
    contDiff_id.mul (contDiff_const.sub contDiff_id)
  have hPole : ContDiffAt ℂ n (fun w : ℂ ↦ (Theta.mixedThetaPair K).f₀ / (w * (1 - w))) c :=
    contDiff_const.contDiffAt.div hDen.contDiffAt (mul_ne_zero hc0 (sub_ne_zero.mpr hc1.symm))
  have hTrunc : ContDiffAt ℂ n (mixedThetaTruncation K cut) c :=
    (mixedThetaTruncation_differentiable K hcut).contDiff.contDiffAt
  rw [contourTaylorCoeff_eq_iteratedDeriv_div_factorial hρ
    (mixedThetaCompletedTruncation_differentiableOn_disk K hcut hLeft hRight) n]
  change iteratedDeriv n
    (mixedThetaTruncation K cut - (fun w ↦ (Theta.mixedThetaPair K).f₀ / (w * (1 - w)))) c /
      (n.factorial : ℂ) = _
  rw [iteratedDeriv_sub hTrunc hPole,
    mixedThetaTruncation_iteratedDeriv_eq_integral K hcut, iteratedDeriv_mixedThetaPole_eq _ n hc0 hc1,
    mixedThetaCompletedMomentCoeff, sub_div]
  have hFact : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [mul_right_comm _ (n.factorial : ℂ), mul_div_cancel_right₀ _ hFact]

theorem mixedTheta_completed_disk_moment_error_le (K : Type) [Field K] [NumberField K]
    {cut r : ℝ} {ρ : ℝ≥0} {c z : ℂ} (hcut : 1 ≤ cut)
    (hLeft : (ρ : ℝ) < c.re) (hRight : (ρ : ℝ) < 1 - c.re)
    (hr : r < (ρ : ℝ)) (hz : ‖z‖ ≤ r) (n : ℕ) :
    ‖mixedThetaCompletedReading K (c + z) -
      ∑ k ∈ Finset.range n, mixedThetaCompletedMomentCoeff K cut c k * z ^ k‖ ≤
        mixedThetaCompletedTaylorAllowance K cut c ρ r n := by
  have hρ : 0 < ρ := by
    exact_mod_cast lt_of_le_of_lt ((norm_nonneg z).trans hz) hr
  simpa only [mixedTheta_completed_taylorCoeff_eq_moment K hcut hρ hLeft hRight] using
    mixedTheta_completed_disk_taylor_error_le K hcut hLeft hRight hr hz n

#print axioms iteratedDeriv_mixedThetaPole_eq
#print axioms mixedTheta_completed_taylorCoeff_eq_moment
#print axioms mixedTheta_completed_disk_moment_error_le

end
end FieldTarget
