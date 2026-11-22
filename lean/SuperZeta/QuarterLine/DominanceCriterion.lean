import SuperZeta.UnitSpectrum

namespace SuperZeta.QuarterLine
open Complex Real UnitSpectrum

noncomputable section

def point (σ t : ℝ) : ℂ := ⟨σ,t⟩

theorem hundred_margin {t : ℝ} (ht : 100 ≤ t) :
    160 * (t+2) < Real.exp (3*t/20) := by
  have h15 : (32768:ℝ) ≤ Real.exp 15 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
      (show (2:ℝ) ≤ Real.exp 1 by linarith [Real.add_one_le_exp (1:ℝ)]) 15
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh ⊢
    exact hh
  let x := 3*(t-100)/20
  have hx : 0 ≤ x := by dsimp [x]; linarith
  have he := mul_le_mul h15 (Real.add_one_le_exp x) (by linarith) (Real.exp_pos _).le
  rw [← Real.exp_add] at he
  have hsum : 15+x=3*t/20 := by dsimp [x]; ring
  rw [hsum] at he
  dsimp [x] at he
  linarith

theorem dominates {z v : ℂ} {t : ℝ} (ht : 100 ≤ t)
    (herr : ‖z-v‖ ≤ 80*(t+2)*Real.exp (11*t/10))
    (hmain : Real.exp (5*t/4)/2 ≤ ‖v‖) : ‖z-v‖ < ‖v‖ := by
  have he := mul_lt_mul_of_pos_right (hundred_margin ht) (Real.exp_pos (11*t/10))
  rw [← Real.exp_add, show 3*t/20+11*t/10=5*t/4 by ring] at he
  linarith

theorem nonzero_of_dominates {z v : ℂ} (h : ‖z-v‖ < ‖v‖) : z ≠ 0 := by
  rintro rfl
  simp at h

/-- Zeros of the residual are intersections of the two actual spectra at the halved inputs. -/
theorem zero_at_half (w : ℂ) (h₀ : 0 < w.re) (h₁ : w.re < 1) :
    riemannZeta w = 0 ↔ continuation (w/2) = Reference.entireCorrection 1 (w/2) := by
  have ha : (w/2).re = w.re/2 := by simp [Complex.div_ofNat_re]
  have h := (equality_iff_riemann_zero (s:=w/2) (by rw [ha]; linarith)
    (by rw [ha]; linarith)).2
  rw [show 2*(w/2)=w by ring] at h
  exact h.symm

/-- If two inputs have unequal complex increments of Z and J, they cannot both lift zeros. -/
theorem two_readings_obstruction {a b : ℂ} (ha₀ : 0 < a.re) (ha₁ : a.re < 1)
    (hb₀ : 0 < b.re) (hb₁ : b.re < 1)
    (hm : continuation (a/2) - continuation (b/2) ≠
      Reference.entireCorrection 1 (a/2) - Reference.entireCorrection 1 (b/2)) :
    ¬ (riemannZeta a = 0 ∧ riemannZeta b = 0) := by
  rintro ⟨ha,hb⟩
  apply hm
  rw [(zero_at_half a ha₀ ha₁).mp ha, (zero_at_half b hb₀ hb₁).mp hb]

end
end SuperZeta.QuarterLine
