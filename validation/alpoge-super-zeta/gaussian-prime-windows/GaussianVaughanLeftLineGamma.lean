import GaussianVaughanLogWindow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthGamma

/-! On the contours with real part `-7N`, the reflected Gamma factor
has an integer shift. Keep its growth explicit in `N`. -/

namespace AlpogeSuperZeta

open Complex Finset

noncomputable section

theorem gaussianGamma_nat_line_bound (n : ℕ) (t : ℝ) :
    ‖Gamma (1 + (n : ℂ) + (t : ℂ) * I)‖ ≤
      96 * ((n : ℝ) + 1 + |t|) ^ (n + 5) * Real.exp (-(Real.pi / 2 * |t|)) := by
  induction n with
  | zero =>
    let z : ℂ := 1 + (t : ℂ) * I
    have hre : z.re = 1 := by simp [z, mul_re]
    have him : z.im = t := by simp [z, mul_im]
    have hGamma := PI.EF.Gamma_decay (w := z) (by rw [hre]; norm_num) (by rw [hre]; norm_num)
    have hnorm : ‖z + 1‖ ≤ 2 * (1 + |t|) := by
      have e : z + 1 = 2 + (t : ℂ) * I := by dsimp [z]; ring
      rw [e]
      have h := norm_add_le (2 : ℂ) ((t : ℂ) * I)
      norm_num [norm_mul, norm_real, Real.norm_eq_abs, norm_I] at h
      linarith [abs_nonneg t]
    have h5 := pow_le_pow_left₀ (norm_nonneg _) hnorm (5 : ℕ)
    rw [him] at hGamma
    have hbase : ‖Gamma z‖ ≤ 96 * (1 + |t|) ^ (5 : ℕ) *
        Real.exp (-(Real.pi / 2 * |t|)) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
      rw [mul_pow] at h5
      linarith
    simpa [z] using hbase
  | succ n ih =>
    let z : ℂ := 1 + (n : ℂ) + (t : ℂ) * I
    let R : ℝ := (n : ℝ) + 1 + |t|
    let S : ℝ := (n.succ : ℝ) + 1 + |t|
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hRS : R ≤ S := by dsimp [R, S]; push_cast; linarith
    have hz : z ≠ 0 := by
      intro h
      have he := congrArg re h
      simp [z, mul_re] at he
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      linarith
    have hnorm : ‖z‖ ≤ R := by
      have h := norm_add_le (1 + (n : ℂ)) ((t : ℂ) * I)
      rw [add_comm (1 : ℂ) (n : ℂ), ← Nat.cast_succ, norm_natCast,
        norm_mul, norm_real, Real.norm_eq_abs, norm_I,
        mul_one] at h
      simpa [z, R, Nat.cast_succ, add_comm (1 : ℂ) (n : ℂ)] using h
    have e : 1 + (n.succ : ℂ) + (t : ℂ) * I = z + 1 := by
      dsimp [z]
      push_cast
      ring
    rw [e, Gamma_add_one _ hz, norm_mul]
    change ‖z‖ * ‖Gamma z‖ ≤
      96 * S ^ (n.succ + 5) * Real.exp (-(Real.pi / 2 * |t|))
    calc
      _ ≤ R * (96 * R ^ (n + 5) * Real.exp (-(Real.pi / 2 * |t|))) :=
        mul_le_mul hnorm ih (norm_nonneg _) hR
      _ = 96 * R ^ (n.succ + 5) * Real.exp (-(Real.pi / 2 * |t|)) := by
        rw [show n.succ + 5 = (n + 5) + 1 by omega, pow_succ]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR hRS _) (by norm_num)) (Real.exp_pos _).le

theorem gaussianGamma_leftLine_product_bound (N : ℕ) (t : ℝ) :
    ‖Gamma (1 + ((7 * N : ℕ) : ℂ) - (t : ℂ) * I) /
        Gamma (-((7 * N : ℕ) : ℂ) + (t : ℂ) * I)‖ *
      ‖Gamma (1 + (N : ℂ) - ((t / 7 : ℝ) : ℂ) * I)‖ ≤
      96 * ((7 * N : ℕ) + 1 + |t| : ℝ) ^ (15 * N + 6) *
        Real.exp (-(Real.pi * |t| / 14)) := by
  let R : ℝ := ((7 * N : ℕ) : ℝ) + 1 + |t|
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have ht : |t| ≤ R := le_add_of_nonneg_left (by positivity)
  have hnorm (j : ℕ) (hj : j ∈ range (7 * N)) :
      ((j : ℝ) + 1) ^ 2 + t ^ 2 ≤ R ^ 2 := by
    have hj' : (j : ℝ) + 1 ≤ ((7 * N : ℕ) : ℝ) + 1 :=
      add_le_add_left (Nat.cast_le.mpr (Nat.le_of_lt (mem_range.mp hj))) 1
    have hsq : ((j : ℝ) + 1) ^ 2 ≤ (((7 * N : ℕ) : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hj' _
    have hsqT : |t| ^ 2 = t ^ 2 := sq_abs t
    dsimp [R]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ ((7 * N : ℕ) : ℝ) + 1 by positivity) (abs_nonneg t)]
  have hRatio : ‖Gamma (1 + ((7 * N : ℕ) : ℂ) - (t : ℂ) * I) /
        Gamma (-((7 * N : ℕ) : ℂ) + (t : ℂ) * I)‖ ≤ R ^ (14 * N + 1) := by
    rw [gaussianGamma_left_ratio_norm]
    have h := prod_le_prod (fun j (_ : j ∈ range (7 * N)) =>
      add_nonneg (sq_nonneg _) (sq_nonneg _)) hnorm
    rw [prod_const, card_range, ← pow_mul] at h
    have he : 2 * (7 * N) = 14 * N := by omega
    rw [he] at h
    calc
      _ ≤ R * R ^ (14 * N) := mul_le_mul ht h (by positivity) hR
      _ = _ := (pow_succ' R (14 * N)).symm
  have hB : (N : ℝ) + 1 + |-(t / 7)| ≤ R := by
    rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 7)]
    dsimp [R]
    push_cast
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    linarith [abs_nonneg t]
  have hG := gaussianGamma_nat_line_bound N (-(t / 7))
  rw [ofReal_neg, neg_mul, ← sub_eq_add_neg] at hG
  have hExp : Real.pi / 2 * |-(t / 7)| = Real.pi * |t| / 14 := by
    rw [abs_neg, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 7)]
    ring
  rw [hExp] at hG
  have hc := hG.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hB (N + 5)) (by norm_num))
    (Real.exp_pos _).le)
  have h := mul_le_mul hRatio hc (norm_nonneg _) (by positivity : 0 ≤ R ^ (14 * N + 1))
  refine h.trans_eq ?_
  change R ^ (14 * N + 1) * (96 * R ^ (N + 5) *
    Real.exp (-(Real.pi * |t| / 14))) = 96 * R ^ (15 * N + 6) *
      Real.exp (-(Real.pi * |t| / 14))
  rw [show 15 * N + 6 = (14 * N + 1) + (N + 5) by omega, pow_add]
  ring

#print axioms gaussianGamma_nat_line_bound
#print axioms gaussianGamma_leftLine_product_bound

end
end AlpogeSuperZeta
