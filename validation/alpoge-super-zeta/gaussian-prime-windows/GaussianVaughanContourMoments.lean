import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-! Integrate the polynomial times exponential bounds at the negative
Mellin lines, keeping the dependence on the contour index. -/

namespace AlpogeSuperZeta

open Filter MeasureTheory Set

noncomputable section

private theorem exp_neg_abs_integrable :
    Integrable (fun t : ℝ => Real.exp (-|t| / 10)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  refine ⟨?_, ?_⟩
  · refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Iic).2
      (integrableOn_exp_mul_Iic (a := (1 / 10 : ℝ)) (by norm_num) 0)
    rw [abs_of_nonpos (mem_Iic.mp ht)]
    congr 1
    ring
  · refine (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi).2
      (integrableOn_exp_mul_Ioi (a := (-1 / 10 : ℝ)) (by norm_num) 0)
    rw [abs_of_pos (mem_Ioi.mp ht)]
    congr 1
    ring

private theorem integral_exp_neg_abs :
    (∫ t : ℝ, Real.exp (-|t| / 10)) = 20 := by
  have h : (fun t : ℝ => Real.exp (-|t| / 10)) =
      (fun t : ℝ => (fun u : ℝ => Real.exp ((-1 / 10 : ℝ) * u)) |t|) := by
    funext t
    congr 1
    ring
  rw [h, integral_comp_abs (f := fun u : ℝ => Real.exp ((-1 / 10 : ℝ) * u)),
    integral_exp_mul_Ioi (by norm_num : (-1 / 10 : ℝ) < 0)]
  norm_num

private theorem power_exp_neg_abs_le (d : ℕ) {A : ℝ} (hA : 0 ≤ A) (t : ℝ) :
    (A + |t|) ^ d * Real.exp (-|t| / 5) ≤
      ((d.factorial : ℝ) * (10 : ℝ) ^ d * Real.exp (A / 10)) *
        Real.exp (-|t| / 10) := by
  have hp : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have h10 : (0 : ℝ) < (10 : ℝ) ^ d := by positivity
  have h := Real.pow_div_factorial_le_exp (x := (A + |t|) / 10) (by positivity) d
  rw [div_le_iff₀ hp, div_pow, div_le_iff₀ h10] at h
  calc
    _ ≤ (Real.exp ((A + |t|) / 10) * (d.factorial : ℝ) * 10 ^ d) *
        Real.exp (-|t| / 5) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (d.factorial : ℝ) * 10 ^ d *
        (Real.exp ((A + |t|) / 10) * Real.exp (-|t| / 5)) := by ring
    _ = _ := by
      rw [← Real.exp_add, show (A + |t|) / 10 + -|t| / 5 = A / 10 + -|t| / 10 by ring,
        Real.exp_add]
      ring

private theorem one_add_nat_le_two_pow (N : ℕ) : (N : ℝ) + 1 ≤ (2 : ℝ) ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_succ, pow_succ]
    linarith [Nat.cast_nonneg (α := ℝ) N]

theorem gaussian_integrate_left_contours {F : ℕ → ℝ → ℂ}
    (hF : ∀ N ≥ 1, Continuous (F N)) {B : ℝ} (hB : 1 ≤ B)
    (hNorm : ∀ N ≥ 1, ∀ t : ℝ,
      ‖F N t‖ ≤ B ^ (N + 1) * ((7 * N : ℕ) + 1 + |t| : ℝ) ^ (15 * N + 6) *
        Real.exp (-(Real.pi * |t| / 14))) :
    ∃ C ≥ 1, ∀ N ≥ 1, Integrable (F N) ∧
      (∫ t : ℝ, ‖F N t‖) ≤ C ^ (N + 1) * ((N : ℝ) + 1) ^ (15 * N) := by
  let C := 20 * B * (210 : ℝ) ^ (15 : ℕ) * Real.exp 1 * 64
  have hC : 1 ≤ C := by
    dsimp [C]
    have h1 : (1 : ℝ) ≤ (210 : ℝ) ^ (15 : ℕ) := one_le_pow₀ (by norm_num)
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    calc
      (1 : ℝ) = 1 * 1 * 1 * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr <;> norm_num
  refine ⟨C, hC, fun N hN => ?_⟩
  let d := 15 * N + 6
  let A : ℝ := ((7 * N : ℕ) : ℝ) + 1
  let D := B ^ (N + 1) * (d.factorial : ℝ) * (10 : ℝ) ^ d * Real.exp (A / 10)
  have hD₀ : 0 ≤ D := by dsimp [D]; positivity
  have hEnvelope (t : ℝ) : ‖F N t‖ ≤ D * Real.exp (-|t| / 10) := by
    have hpi : -(Real.pi * |t| / 14) ≤ -|t| / 5 := by
      have hp : (1 / 5 : ℝ) ≤ Real.pi / 14 := by linarith [Real.pi_gt_three]
      linarith [mul_le_mul_of_nonneg_right hp (abs_nonneg t)]
    refine (hNorm N hN t).trans ?_
    change B ^ (N + 1) * (A + |t|) ^ d * Real.exp (-(Real.pi * |t| / 14)) ≤ _
    rw [mul_assoc]
    calc
      _ ≤ B ^ (N + 1) * ((A + |t|) ^ d * Real.exp (-|t| / 5)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hpi) (by positivity [show 0 ≤ A by positivity]))
          (by positivity)
      _ ≤ B ^ (N + 1) * (((d.factorial : ℝ) * 10 ^ d * Real.exp (A / 10)) *
          Real.exp (-|t| / 10)) :=
        mul_le_mul_of_nonneg_left (power_exp_neg_abs_le d (by dsimp [A]; positivity) t)
          (by positivity)
      _ = _ := by dsimp [D]; ring
  have hDom : Integrable (fun t : ℝ => D * Real.exp (-|t| / 10)) :=
    exp_neg_abs_integrable.const_mul D
  have hInt : Integrable (F N) :=
    hDom.mono' (hF N hN).aestronglyMeasurable (Eventually.of_forall hEnvelope)
  refine ⟨hInt, ?_⟩
  have hI := integral_mono hInt.norm hDom hEnvelope
  rw [integral_const_mul, integral_exp_neg_abs] at hI
  refine hI.trans ?_
  have hd : (d : ℝ) ≤ 21 * ((N : ℝ) + 1) := by
    dsimp [d]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hFact : (d.factorial : ℝ) ≤ (21 * ((N : ℝ) + 1)) ^ d := by
    have h := Nat.factorial_le_pow d
    have h' : (d.factorial : ℝ) ≤ (d : ℝ) ^ d := by exact_mod_cast h
    exact h'.trans (pow_le_pow_left₀ (by positivity) hd _)
  have hA : A / 10 ≤ (N : ℝ) + 1 := by
    dsimp [A]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hExp : Real.exp (A / 10) ≤ Real.exp 1 ^ (N + 1) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    linarith
  have hR : (((N : ℝ) + 1) ^ (6 : ℕ)) ≤ (64 : ℝ) ^ (N + 1) := by
    calc
      _ ≤ ((2 : ℝ) ^ N) ^ (6 : ℕ) :=
        pow_le_pow_left₀ (by positivity) (one_add_nat_le_two_pow N) _
      _ = ((2 : ℝ) ^ (6 : ℕ)) ^ N := by rw [← pow_mul, mul_comm N, pow_mul]
      _ ≤ _ := by
        rw [show (2 : ℝ) ^ (6 : ℕ) = 64 by norm_num]
        exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h20 : (20 : ℝ) ≤ 20 ^ (N + 1 : ℕ) :=
    le_self_pow₀ (by norm_num) (by omega)
  have h210 : (210 : ℝ) ^ d ≤ ((210 : ℝ) ^ (15 : ℕ)) ^ (N + 1) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by dsimp [d]; omega)
  calc
    D * 20 = 20 * B ^ (N + 1) * (d.factorial : ℝ) * (10 : ℝ) ^ d * Real.exp (A / 10) := by
      dsimp [D]; ring
    _ ≤ 20 * B ^ (N + 1) * (21 * ((N : ℝ) + 1)) ^ d * (10 : ℝ) ^ d *
        Real.exp 1 ^ (N + 1) := by gcongr
    _ = 20 * B ^ (N + 1) * (210 : ℝ) ^ d * Real.exp 1 ^ (N + 1) *
        (((N : ℝ) + 1) ^ (6 : ℕ)) * (((N : ℝ) + 1) ^ (15 * N)) := by
      rw [mul_pow, show (210 : ℝ) = 21 * 10 by norm_num, mul_pow]
      conv_lhs => rw [show d = 15 * N + 6 by rfl,
        pow_add ((N : ℝ) + 1) (15 * N)]
      ring
    _ ≤ (20 : ℝ) ^ (N + 1) * B ^ (N + 1) * ((210 : ℝ) ^ (15 : ℕ)) ^ (N + 1) *
        Real.exp 1 ^ (N + 1) * (64 : ℝ) ^ (N + 1) * (((N : ℝ) + 1) ^ (15 * N)) := by gcongr
    _ = _ := by simp only [C, mul_pow]

#print axioms gaussian_integrate_left_contours

end
end AlpogeSuperZeta
