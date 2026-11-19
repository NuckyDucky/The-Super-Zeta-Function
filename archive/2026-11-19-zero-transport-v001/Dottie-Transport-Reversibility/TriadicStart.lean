import ForwardCertificate
import Mathlib.Data.Nat.Prime.Basic

/-! Starting zeros on the triadic lattice, unavailable by any finite reset. -/
noncomputable section
namespace DottieOriented.TriadicStart
open Complex DottieOriented.LiuConnection DottieOriented.ForwardCertificate

def triadic (k : ℤ) : ℂ := k * (2 * (Real.pi : ℂ) * I) / (Real.log 3 : ℝ)

private theorem prime_logs {k m : ℤ} (hk : k ≠ 0) :
    (k : ℝ) * Real.log 2 ≠ (m : ℝ) * Real.log 3 := by
  intro h
  have htwo := Real.log_pos (by norm_num : 1 < (2:ℝ))
  have hthree := Real.log_pos (by norm_num : 1 < (3:ℝ))
  have h' := congrArg abs h
  simp only [abs_mul, abs_of_pos htwo, abs_of_pos hthree] at h'
  have ha (n : ℤ) : (n.natAbs : ℝ) = |(n:ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [← ha k, ← ha m, ← Real.log_pow, ← Real.log_pow] at h'
  have hp : (2:ℝ)^k.natAbs = 3^m.natAbs :=
    Real.log_injOn_pos (pow_pos (by norm_num : (0:ℝ)<2) k.natAbs)
      (pow_pos (by norm_num : (0:ℝ)<3) m.natAbs) h'
  have hp' : (2:ℕ)^k.natAbs = 3^m.natAbs := by exact_mod_cast hp
  have dk : (2:ℕ) ∣ 2^k.natAbs := dvd_pow_self _ (by simpa using hk)
  rw [hp'] at dk
  have bad := Nat.prime_two.dvd_of_dvd_pow dk
  norm_num at bad

theorem triadic_ne_dyadic (k m : ℤ) (hk : k ≠ 0) : triadic k ≠ dyadic m := by
  intro h
  have h₂ : (Real.log 2 : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have h₃ : (Real.log 3 : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  have x := (div_eq_div_iff h₃ h₂).mp h
  have hcommon : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hx : ((k:ℂ) * (Real.log 2:ℝ)) * (2 * (Real.pi:ℂ) * I) =
      ((m:ℂ) * (Real.log 3:ℝ)) * (2 * (Real.pi:ℂ) * I) := by
    linear_combination x
  have home := mul_right_cancel₀ hcommon hx
  apply prime_logs hk (m:=m)
  exact_mod_cast home

theorem triadic_pow (k : ℤ) : (3 : ℂ)^(triadic k) = 1 := by
  rw [cpow_def_of_ne_zero (by norm_num : (3:ℂ)≠0), exp_eq_one_iff]
  refine ⟨k, ?_⟩
  have hlog : (Real.log 3 : ℂ) = Complex.log 3 := by simp
  have h₃ : (Real.log 3 : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by norm_num)))
  rw [← hlog, mul_comm]
  exact div_mul_cancel₀ _ h₃

theorem start_only (k : ℤ) (hk : k ≠ 0) :
    reference (1/6 : ℝ) (triadic k) = 0 ∧ reference (1/4 : ℝ) (triadic k) ≠ 0 := by
  have hpow := triadic_pow k
  have haxis : (triadic k).re = 0 := by
    apply (Real.rpow_right_inj (by norm_num : (0:ℝ)<3) (by norm_num)).mp
    calc (3:ℝ)^(triadic k).re = ‖(3:ℂ)^(triadic k)‖ :=
             (norm_natCast_cpow_of_pos (n:=3) (by decide) _).symm
         _ = (3:ℝ)^(0:ℝ) := by simp [hpow]
  have h1 : triadic k ≠ 1 := by intro h; simp [h] at haxis
  refine ⟨(ReferenceReset.starting_zero_iff h1).mpr (Or.inl hpow), ?_⟩
  intro hend
  rcases (endpoint_partition h1).mp hend with ⟨m,hm⟩ | hζ
  · exact triadic_ne_dyadic k m hk hm
  · exact zeta_ne_zero_on_imaginary_axis haxis hζ

#print axioms triadic_ne_dyadic
#print axioms start_only
end DottieOriented.TriadicStart
