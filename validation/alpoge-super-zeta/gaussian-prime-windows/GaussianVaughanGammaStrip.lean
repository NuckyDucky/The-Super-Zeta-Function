import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-! Euler-integral and recurrence estimates for the Gamma factor of the
seventh-scale theta Mellin transform. -/

namespace AlpogeSuperZeta

open Complex MeasureTheory Set

private theorem gamma_norm_le_real {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs, Complex.GammaIntegral]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp hx),
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp

/-- The recurrence bounds each imaginary-height power by shifting the
Gamma argument horizontally by that many units. -/
theorem gamma_pow_im_le_shift {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    |s.im| ^ k * ‖Complex.Gamma s‖ ≤ ‖Complex.Gamma (s + (k : ℂ))‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have him : |s.im| ≤ ‖s + (k : ℂ)‖ := by
      simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
        Complex.abs_im_le_norm (s + (k : ℂ))
    have hn : s + (k : ℂ) ≠ 0 := by
      intro h
      have he := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.zero_re] at he
      linarith [Nat.cast_nonneg (α := ℝ) k]
    rw [Nat.cast_succ, ← add_assoc, Complex.Gamma_add_one _ hn, norm_mul, pow_succ', mul_assoc]
    exact mul_le_mul him ih (by positivity) (norm_nonneg _)

/-- On a closed strip strictly right of zero, the Gamma factor supplies
arbitrarily many powers of decay, uniformly at every height. -/
theorem gamma_rapid_decay_on_positive_strip {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (k : ℕ) :
    ∃ C > 0, ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      (1 + |s.im|) ^ k * ‖Complex.Gamma s‖ ≤ C := by
  let M := max (Real.Gamma a) (Real.Gamma (b + (k : ℝ)))
  have hM : 0 < M := (Real.Gamma_pos_of_pos ha).trans_le (le_max_left _ _)
  have hb : 0 < b + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have huniform {w : ℂ} (hw₁ : a ≤ w.re) (hw₂ : w.re ≤ b + (k : ℝ)) :
      ‖Complex.Gamma w‖ ≤ M :=
    (gamma_norm_le_real (ha.trans_le hw₁)).trans
      (Real.convexOn_Gamma.le_max_of_mem_Icc ha hb ⟨hw₁, hw₂⟩)
  refine ⟨2 ^ k * M, by positivity, fun s hs₁ hs₂ => ?_⟩
  have hk := Nat.cast_nonneg (α := ℝ) k
  by_cases hi : |s.im| ≤ 1
  · have hpow : (1 + |s.im|) ^ k ≤ (2 : ℝ) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith) _
    exact mul_le_mul hpow (huniform hs₁ (by linarith)) (norm_nonneg _) (by positivity)
  · have hpow : (1 + |s.im|) ^ k ≤ (2 * |s.im|) ^ k :=
      pow_le_pow_left₀ (by positivity) (by linarith [lt_of_not_ge hi]) _
    have hshift : ‖Complex.Gamma (s + (k : ℂ))‖ ≤ M :=
      huniform (by rw [add_re, natCast_re]; linarith)
        (by rw [add_re, natCast_re]; linarith)
    calc
      _ ≤ (2 * |s.im|) ^ k * ‖Complex.Gamma s‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = 2 ^ k * (|s.im| ^ k * ‖Complex.Gamma s‖) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((gamma_pow_im_le_shift (ha.trans_le hs₁) k).trans hshift) (by positivity)


private theorem norm_sin_le_exp_abs_im (s : ℂ) :
    ‖Complex.sin s‖ ≤ Real.exp |s.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_I, mul_one, norm_ofNat]
  have h₁ : ‖Complex.exp (-s * I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    simpa [mul_re] using Real.exp_le_exp.mpr (le_abs_self s.im)
  have h₂ : ‖Complex.exp (s * I)‖ ≤ Real.exp |s.im| := by
    rw [Complex.norm_exp]
    simpa [mul_re] using Real.exp_le_exp.mpr (neg_le_abs s.im)
  linarith [norm_sub_le (Complex.exp (-s * I)) (Complex.exp (s * I))]

/-- Reflected Gamma gives an exponential growth envelope for the reciprocal
across the strip used to control the entire uncompleted Gaussian factor. -/
theorem inv_gamma_bound_on_strip :
    ∃ C > 0, ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → 1 ≤ |s.im| →
      ‖(Complex.Gamma s)⁻¹‖ ≤ C * Real.exp (Real.pi * |s.im|) := by
  let B := max (Real.Gamma 2) (Real.Gamma 5)
  have hB : 0 < B := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2)).trans_le (le_max_left _ _)
  refine ⟨B / Real.pi, div_pos hB Real.pi_pos, fun s hs₁ hs₂ ht => ?_⟩
  let u := s - 3
  let g := Complex.Gamma (4 - s)
  let S := Complex.sin ((Real.pi : ℂ) * u)
  have him : s.im ≠ 0 := by intro h; rw [h, abs_zero] at ht; norm_num at ht
  have hnon (r : ℝ) : s - (r : ℂ) ≠ 0 := by
    intro h
    apply him
    simpa using congrArg Complex.im h
  have hγ : Complex.Gamma u ≠ 0 :=
    Complex.Gamma_ne_zero (fun n h => him (by simpa [u, sub_im] using congrArg Complex.im h))
  have hg : ‖g‖ ≤ B := by
    have hre : (4 - s).re = 4 - s.re := by simp [sub_re]
    apply (gamma_norm_le_real (by rw [hre]; linarith)).trans
    exact Real.convexOn_Gamma.le_max_of_mem_Icc (by norm_num) (by norm_num)
      ⟨by rw [hre]; linarith, by rw [hre]; linarith⟩
  have hgn : g ≠ 0 := Complex.Gamma_ne_zero fun n h => by
    have he := congrArg Complex.re h
    simp [sub_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hreflect : Complex.Gamma u * g = (Real.pi : ℂ) / S := by
    have hu : 1 - u = 4 - s := by dsimp [u]; ring
    simpa only [g, S, hu] using Complex.Gamma_mul_Gamma_one_sub u
  have hS : S ≠ 0 := by
    intro h
    rw [h, div_zero] at hreflect
    exact mul_ne_zero hγ hgn hreflect
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hinv : (Complex.Gamma u)⁻¹ = g * S / (Real.pi : ℂ) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_div_assoc, ← mul_assoc, hreflect, div_mul_cancel₀ _ hS, div_self hπ]
  have hSbd : ‖S‖ ≤ Real.exp (Real.pi * |s.im|) := by
    dsimp only [S]
    have he : |((Real.pi : ℂ) * u).im| = Real.pi * |s.im| := by
      simp [mul_im, u, sub_im, abs_mul, abs_of_pos Real.pi_pos]
    simpa only [he] using norm_sin_le_exp_abs_im ((Real.pi : ℂ) * u)
  have huBd : ‖(Complex.Gamma u)⁻¹‖ ≤ B / Real.pi * Real.exp (Real.pi * |s.im|) := by
    rw [hinv, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    calc
      _ ≤ B * Real.exp (Real.pi * |s.im|) / Real.pi :=
        div_le_div_of_nonneg_right (mul_le_mul hg hSbd (norm_nonneg S) hB.le) Real.pi_pos.le
      _ = _ := by ring
  have hstep (r : ℝ) : Complex.Gamma (s - (r : ℂ) + 1) =
      (s - (r : ℂ)) * Complex.Gamma (s - (r : ℂ)) :=
    Complex.Gamma_add_one _ (hnon r)
  have h₁ : Complex.Gamma s = (s - 1) * Complex.Gamma (s - 1) := by
    simpa using hstep 1
  have h₂ : Complex.Gamma (s - 1) = (s - 2) * Complex.Gamma (s - 2) := by
    simpa only [Complex.ofReal_ofNat, show s - 2 + 1 = s - 1 by ring] using hstep 2
  have h₃ : Complex.Gamma (s - 2) = (s - 3) * Complex.Gamma u := by
    simpa only [Complex.ofReal_ofNat, show s - 3 + 1 = s - 2 by ring, u] using hstep 3
  have hlow (r : ℝ) : 1 ≤ ‖s - (r : ℂ)‖ := ht.trans (by
    simpa only [sub_im, ofReal_im, sub_zero] using Complex.abs_im_le_norm (s - (r : ℂ)))
  rw [h₁, h₂, h₃]
  simp only [mul_inv, norm_mul]
  refine le_trans ?_ huBd
  have h₁' : ‖(s - 1)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (by simpa using hlow 1)
  have h₂' : ‖(s - 2)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (by simpa using hlow 2)
  have h₃' : ‖(s - 3)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ (by simpa using hlow 3)
  calc
    _ ≤ 1 * (1 * (1 * ‖(Complex.Gamma u)⁻¹‖)) := by gcongr
    _ = _ := by simp

#print axioms gamma_rapid_decay_on_positive_strip
#print axioms inv_gamma_bound_on_strip

end AlpogeSuperZeta
