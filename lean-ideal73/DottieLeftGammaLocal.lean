import DottieHighGammaLocal

/-! The Gamma factor on the finite left contour is obtained from the
checked right contour estimate by fourteen exact recurrence steps. -/

namespace QuarticModel

open Complex Set SuperZeta.StirlingCorrection
set_option autoImplicit false

theorem dottie_gamma_norm_recurrence (s : ℂ) (hs : s.im ≠ 0) (m : ℕ) :
    |s.im|^m * ‖Gamma s‖ ≤ ‖Gamma (s+(m : ℂ))‖ := by
  induction m with
  | zero => simp
  | succ m hm =>
    have hz : s+(m : ℂ) ≠ 0 := by
      intro he
      exact hs (by simpa only [add_im, natCast_im, zero_im, add_zero] using congrArg Complex.im he)
    have hn : |s.im| ≤ ‖s+(m : ℂ)‖ := by
      simpa only [add_im, natCast_im, add_zero] using Complex.abs_im_le_norm (s+(m : ℂ))
    calc
      _ = |s.im| * (|s.im|^m*‖Gamma s‖) := by rw [pow_succ]; ring
      _ ≤ |s.im| * ‖Gamma (s+(m : ℂ))‖ := mul_le_mul_of_nonneg_left hm (abs_nonneg _)
      _ ≤ ‖s+(m : ℂ)‖ * ‖Gamma (s+(m : ℂ))‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = _ := by rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hz, norm_mul]

theorem dottie_gamma_left_tilted_norm_ratio {σ t u : ℝ}
    (hσ : σ ∈ Icc (1/2-63/2048 : ℝ) (1/2+63/2048))
    (ht : |t-dottieHeight| ≤ 35/2048) (hu : |u| ≤ 20) :
    (‖Gamma (⟨σ-7,t+u⟩ : ℂ)‖ / ‖Gamma (2+(dottieHeight : ℂ)*I)‖) *
      Real.exp (Real.pi*u/2) ≤
        dottieHeight^(σ-9)*Real.exp (35*Real.pi/4096+2/10^10) := by
  let T := dottieHeight
  let v := t+u
  let s : ℂ := ⟨σ-7,v⟩
  let G := ‖Gamma (2+(dottieHeight : ℂ)*I)‖
  let E := Real.exp (Real.pi*u/2)
  have hT : 4*10^12 < T := by dsimp [T]; linarith only [dottieHeight_enclosure.1]
  have hT₀ : 0 < T := by linarith
  have hvDiff : |v-T| ≤ 21 := by
    dsimp only [v,T]
    rw [show t+u-dottieHeight = (t-dottieHeight)+u by ring]
    exact (abs_add_le _ _).trans (by linarith only [ht,hu])
  have hvBig : 3*10^12 < v := by linarith only [hT,(abs_le.mp hvDiff).1]
  have hv : 0 < v := by linarith
  have hG : 0 < G := norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by norm_num))
  have hs : s.im ≠ 0 := hv.ne'
  have hn := dottie_gamma_norm_recurrence s hs 14
  have he : s+(14 : ℕ) = (⟨σ+7,t+u⟩ : ℂ) := by
    apply Complex.ext
    · change σ-7+14 = σ+7
      ring
    · simp [s,v]
  rw [he, show s.im = v from rfl, abs_of_pos hv] at hn
  have hn' : ‖Gamma s‖ ≤ ‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖ / v^14 := by
    apply (le_div_iff₀ (pow_pos hv _)).2
    rw [mul_comm]
    exact hn
  have hright := dottie_gamma_k7_local_tilted_norm_ratio hσ ht hu
  change (‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖/G)*E ≤
    T^(σ+5)*Real.exp (35*Real.pi/4096+1/10^10) at hright
  have hratio : T/v ≤ 1+21/v := by
    apply (div_le_iff₀ hv).2
    have he' : (1+21/v)*v = v+21 := by field_simp [hv.ne']
    rw [he']
    linarith only [(abs_le.mp hvDiff).1]
  have hp : (T/v)^14 ≤ Real.exp (1/10^10) := by
    calc
      _ ≤ (1+21/v)^14 := pow_le_pow_left₀ (div_nonneg hT₀.le hv.le) hratio _
      _ ≤ (Real.exp (21/v))^14 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [Real.add_one_le_exp (21/v)]) _
      _ = Real.exp (294/v) := by
        rw [← Real.exp_nat_mul, show ((14 : ℕ) : ℝ)*(21/v) = 294/v by push_cast; ring]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        exact (div_le_iff₀ hv).2 (by linarith only [hvBig])
  change (‖Gamma s‖/G)*E ≤ T^(σ-9)*Real.exp (35*Real.pi/4096+2/10^10)
  calc
    _ ≤ ((‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖/G)*E)/v^14 := by
      have hE : 0 ≤ E := (Real.exp_pos _).le
      have h := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn' hG.le) hE
      have hEq :
          ‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖/v^14/G*E =
            (‖Gamma (⟨σ+7,t+u⟩ : ℂ)‖/G*E)/v^14 := by ring
      exact h.trans_eq hEq
    _ ≤ (T^(σ+5)*Real.exp (35*Real.pi/4096+1/10^10))/v^14 :=
      div_le_div_of_nonneg_right hright (pow_nonneg hv.le _)
    _ = T^(σ-9)*Real.exp (35*Real.pi/4096+1/10^10)*(T/v)^14 := by
      have hpowT : T^(14 : ℝ) = T^(14 : ℕ) := by
        simpa only [Nat.cast_ofNat] using (Real.rpow_natCast T 14)
      rw [show σ+5 = (σ-9)+14 by ring, Real.rpow_add hT₀, hpowT, div_pow]
      ring
    _ ≤ _ := by
      refine (mul_le_mul_of_nonneg_left hp (by positivity)).trans_eq ?_
      rw [mul_assoc, ← Real.exp_add,
        show 35*Real.pi/4096+1/10^10+1/10^10 = 35*Real.pi/4096+2/10^10 by ring]

#print axioms dottie_gamma_norm_recurrence
#print axioms dottie_gamma_left_tilted_norm_ratio

end QuarticModel
