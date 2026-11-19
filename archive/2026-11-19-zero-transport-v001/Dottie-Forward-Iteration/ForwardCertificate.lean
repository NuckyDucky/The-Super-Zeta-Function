import ReferenceReset
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! Certification rules for the actual bilateral Hurwitz reference. -/
namespace DottieOriented.ForwardCertificate
open Complex Set Metric Function DottieOriented.LiuConnection
open scoped NNReal
noncomputable section

/-- No positive-real-part hypothesis is needed for the endpoint dichotomy. -/
theorem endpoint_dichotomy {w : ℂ} (hw : w ≠ 1) :
    reference (1/4 : ℝ) w = 0 ↔ (2 : ℂ)^w = 1 ∨ riemannZeta w = 0 := by
  have hp : (Real.pi : ℂ)^(-w) ≠ 0 :=
    cpow_ne_zero_iff.mpr (.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have htwo : (2 : ℂ)^w ≠ 0 := cpow_ne_zero_iff.mpr (.inl (by norm_num))
  simp only [reference, show (1-1/4 : ℝ) = 3/4 by norm_num, FlankReferences.quarter_pair hw,
    mul_eq_zero, hp, htwo, false_or, sub_eq_zero]

/-- An Euler-factor endpoint must have real part exactly zero. -/
theorem elementary_endpoint_on_axis {w : ℂ} (h : (2 : ℂ)^w = 1) : w.re = 0 := by
  apply (Real.rpow_right_inj (by norm_num : (0:ℝ)<2) (by norm_num)).mp
  calc (2:ℝ)^w.re = ‖(2:ℂ)^w‖ := (norm_natCast_cpow_of_pos (n:=2) (by decide) w).symm
       _ = (2:ℝ)^(0:ℝ) := by simp [h]

/-- The full dyadic lattice in the Riemann variable. -/
def dyadic (k : ℤ) : ℂ := k * (2 * (Real.pi:ℂ) * I) / (Real.log 2:ℝ)

private theorem log_two_ne : (Real.log 2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))

theorem dyadic_iff {w : ℂ} : (2:ℂ)^w = 1 ↔ ∃ k : ℤ, w = dyadic k := by
  rw [cpow_def_of_ne_zero (by norm_num : (2:ℂ)≠0), exp_eq_one_iff]
  have hlog : (Real.log 2 : ℂ) = Complex.log 2 := by
    simp
  rw [← hlog]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k, (eq_div_iff log_two_ne).mpr ((mul_comm _ _).trans hk)⟩
  · rintro ⟨k,rfl⟩
    refine ⟨k, ?_⟩
    unfold dyadic
    rw [mul_comm]
    exact div_mul_cancel₀ _ log_two_ne

/-- Ordinary zeta has no zeros on the imaginary axis. Transfer any such
zero by its functional equation to the classical zero-free line Re=1. -/
theorem zeta_ne_zero_on_imaginary_axis {w : ℂ} (hr : w.re = 0) : riemannZeta w ≠ 0 := by
  by_cases hw : w = 0
  · rw [hw, riemannZeta_zero]
    norm_num
  have hi : w.im ≠ 0 := fun h => hw (Complex.ext hr h)
  have hnat : ∀ n : ℕ, w ≠ -(n:ℂ) := by
    intro n h
    apply hi
    simpa using congrArg Complex.im h
  have h1 : w ≠ 1 := by
    intro h
    apply hi
    simp [h]
  have hline : 1 ≤ (1-w).re := by simp [Complex.sub_re, hr]
  intro hz
  apply riemannZeta_ne_zero_of_one_le_re hline
  rw [riemannZeta_one_sub hnat h1, hz, mul_zero]

/-- Every elementary endpoint is a zero at both anchors and is disjoint
from the ordinary Riemann zero set, including the origin. -/
theorem dyadic_both_anchors_nonriemann (k : ℤ) :
    reference (1/4 : ℝ) (dyadic k) = 0 ∧
    reference (1/6 : ℝ) (dyadic k) = 0 ∧ riemannZeta (dyadic k) ≠ 0 := by
  have hpow := (dyadic_iff (w:=dyadic k)).mpr ⟨k, rfl⟩
  have haxis := elementary_endpoint_on_axis hpow
  have h1 : dyadic k ≠ 1 := by
    intro h
    simp [h] at haxis
  have hquart := (endpoint_dichotomy h1).mpr (Or.inl hpow)
  exact ⟨hquart, ReferenceReset.endpoint_reenters h1 hquart,
    zeta_ne_zero_on_imaginary_axis haxis⟩

theorem endpoint_partition {w : ℂ} (hw : w ≠ 1) :
    reference (1/4 : ℝ) w = 0 ↔ (∃ k : ℤ, w = dyadic k) ∨ riemannZeta w = 0 := by
  rw [endpoint_dichotomy hw, dyadic_iff]

end
end DottieOriented.ForwardCertificate
