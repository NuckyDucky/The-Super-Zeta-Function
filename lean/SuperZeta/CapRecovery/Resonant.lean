import SuperZeta.CapRecovery.Dominance
import SuperZeta.CapRecovery.GeneralWeights

/-! Common caps and their first two derivatives at the integer lifts of πi.
The logarithmic curvature reads the chronological prefix signs in the base
`phase m * lift m`. -/
noncomputable section
namespace SuperZeta.Resonant

open Complex SignWords DyadicWeights
open DyadicCap (polynomial_snoc product_snoc)

def lift (m : ℤ) : ℂ := (m : ℂ) * (Real.pi * I)

def phase (m : ℤ) : ℂ := (-1 : ℂ) ^ m

def base (m : ℤ) : ℂ := phase m * lift m

def curvature (m : ℤ) (w : List Sign) : ℂ :=
  deriv (deriv (eval (lift m) w)) 1 / deriv (eval (lift m) w) 1

theorem phase_cases (m : ℤ) : phase m = 1 ∨ phase m = -1 := by
  rcases Int.even_or_odd m with hm | hm
  · exact Or.inl hm.neg_one_zpow
  · obtain ⟨k, rfl⟩ := hm
    right
    norm_num [phase, zpow_add₀, zpow_mul]

theorem phase_sq (m : ℤ) : phase m ^ 2 = 1 := by
  rcases phase_cases m with h | h <;> rw [h] <;> norm_num

theorem exp_lift (m : ℤ) : exp (lift m) = phase m := by
  rw [lift, Complex.exp_int_mul, Complex.exp_pi_mul_I, phase]

private theorem exp_rate (m : ℤ) (s : Sign) : exp (s.rate (lift m)) = phase m := by
  cases s with
  | plus => exact exp_lift m
  | minus =>
    change exp (-lift m) = phase m
    rw [exp_neg, exp_lift]
    rcases phase_cases m with h | h <;> simp [h]

private theorem exp_rate_phase (m : ℤ) (s : Sign) :
    exp (s.rate (lift m) * phase m) = phase m := by
  rcases phase_cases m with h | h
  · rw [h, mul_one, exp_rate, h]
  · rw [h, mul_neg_one, exp_neg, exp_rate, h]
    norm_num

/-- The common cap of the two one-letter words occurs exactly on πiℤ. -/
theorem one_letter_iff (L : ℂ) :
    eval L [.plus] 1 = eval L [.minus] 1 ↔ ∃ m : ℤ, L = lift m := by
  change exp (L * 1) = exp (-L * 1) ↔ _
  simp only [mul_one, Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨m, h⟩
    exact ⟨m, by unfold lift; linear_combination h / 2⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by unfold lift; ring⟩

/-- Every first letter sends 1 to the same phase, and each next letter fixes it. -/
theorem cap_value (m : ℤ) (s : Sign) (w : List Sign) :
    eval (lift m) (s :: w) 1 = phase m := by
  have fixed (v : List Sign) : eval (lift m) v (phase m) = phase m := by
    induction v with
    | nil => rfl
    | cons a v ih =>
      change eval _ v (exp (a.rate (lift m) * phase m)) = _
      rw [exp_rate_phase, ih]
  change eval _ w (exp (s.rate (lift m) * 1)) = _
  rw [mul_one, exp_rate, fixed]

theorem lift_ne_zero {m : ℤ} (hm : m ≠ 0) : lift m ≠ 0 :=
  mul_ne_zero (by exact_mod_cast hm)
    (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero)

theorem base_ne_zero {m : ℤ} (hm : m ≠ 0) : base m ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (by norm_num)) (lift_ne_zero hm)

theorem norm_base (m : ℤ) : ‖base m‖ = |(m : ℝ)| * Real.pi := by
  rcases phase_cases m with h | h <;>
    simp [base, h, lift, norm_mul, Complex.norm_intCast, abs_of_pos Real.pi_pos]

private theorem word_diff (L : ℂ) (w : List Sign) : Differentiable ℂ (eval L w) := by
  induction w with
  | nil => exact differentiable_id
  | cons s w ih =>
    change Differentiable ℂ (fun z => eval L w (exp (s.rate L * z)))
    fun_prop

private theorem append_exp (L : ℂ) (w : List Sign) (s : Sign) :
    eval L (w ++ [s]) = fun z => exp (s.rate L * eval L w z) := by
  funext z
  rw [eval_append]
  rfl

private theorem derivatives_snoc (m : ℤ) (w : List Sign) (s : Sign) :
    let f := eval (lift m) w
    let g := eval (lift m) (w ++ [s])
    let a := s.rate (lift m)
    deriv g 1 = phase m * (a * deriv f 1) ∧
      deriv (deriv g) 1 = phase m * ((a * deriv f 1)^2 + a * deriv (deriv f) 1) := by
  dsimp only
  let f := eval (lift m) w
  let a := s.rate (lift m)
  have hf : Differentiable ℂ f := word_diff _ _
  have hd : Differentiable ℂ (deriv f) :=
    differentiableOn_univ.mp (hf.differentiableOn.deriv isOpen_univ)
  have h (x : ℂ) := (((hf x).hasDerivAt.const_mul a).cexp)
  have hg : deriv (eval (lift m) (w ++ [s])) =
      fun x => exp (a * f x) * (a * deriv f x) := by
    rw [append_exp]
    exact funext fun x => (h x).deriv
  have hc : exp (a * f 1) = phase m := by
    rw [← congrFun (append_exp (lift m) w s) 1]
    cases w with
    | nil => exact cap_value m s []
    | cons u w => exact cap_value m u (w ++ [s])
  have h₂ := ((h 1).mul ((hd 1).hasDerivAt.const_mul a)).deriv
  rw [hg]
  change exp (a * f 1) * (a * deriv f 1) = _ ∧
    deriv (fun x => exp (a * f x) * (a * deriv f x)) 1 = _
  constructor
  · rw [hc]
  · rw [h₂, hc]; ring

private theorem rate_letter (s : Sign) (L : ℂ) : s.rate L = (letter s : ℂ) * L := by
  cases s <;> simp [Sign.rate, letter]

theorem first_snoc (m : ℤ) (w : List Sign) (s : Sign) :
    deriv (eval (lift m) (w ++ [s])) 1 =
      (letter s : ℂ) * base m * deriv (eval (lift m) w) 1 := by
  rw [(derivatives_snoc m w s).1, rate_letter, base]
  ring

/-- Division-free formula for the two actual derivatives, including the empty
word and the zero lift. -/
theorem derivatives (m : ℤ) (w : List Sign) :
    deriv (eval (lift m) w) 1 = (signProduct w : ℂ) * (base m)^w.length ∧
    deriv (deriv (eval (lift m) w)) 1 =
      deriv (eval (lift m) w) 1 * (lift m * DyadicCap.polynomial w (base m)) := by
  induction w using List.reverseRecOn with
  | nil =>
    change deriv (fun z : ℂ => z) 1 = _ ∧ deriv (deriv (fun z : ℂ => z)) 1 = _
    simp [signProduct, DyadicCap.polynomial]
  | append_singleton w s ih =>
    obtain ⟨hf, hs⟩ := derivatives_snoc m w s
    rw [hf, hs, ih.2, ih.1, polynomial_snoc, product_snoc, Complex.ofReal_mul, rate_letter]
    simp only [List.length_append, List.length_singleton, pow_succ, base]
    constructor <;> ring

theorem first_derivative (m : ℤ) (w : List Sign) :
    deriv (eval (lift m) w) 1 = (signProduct w : ℂ) * (base m)^w.length :=
  (derivatives m w).1

theorem first_ne_zero {m : ℤ} (hm : m ≠ 0) (w : List Sign) :
    deriv (eval (lift m) w) 1 ≠ 0 := by
  rw [first_derivative]
  apply mul_ne_zero _ (pow_ne_zero _ (base_ne_zero hm))
  suffices h : signProduct w ≠ 0 by exact_mod_cast h
  induction w with
  | nil => simp [signProduct]
  | cons s w ih => cases s <;> simpa [signProduct, letter] using ih

theorem curvature_eq (m : ℤ) (w : List Sign) :
    curvature m w = lift m * DyadicCap.polynomial w (base m) := by
  unfold curvature
  rw [(derivatives m w).2]
  by_cases hm : m = 0
  · subst m; simp [lift]
  · field_simp [first_ne_zero hm w]

theorem curvature_snoc (m : ℤ) (w : List Sign) (s : Sign) :
    curvature m (w ++ [s]) =
      curvature m w + phase m * deriv (eval (lift m) (w ++ [s])) 1 := by
  rw [curvature_eq, curvature_eq, polynomial_snoc, first_derivative]
  simp only [List.length_append, List.length_singleton, pow_succ]
  have h : lift m = phase m * base m := by
    unfold base
    linear_combination -(lift m) * phase_sq m
  linear_combination (signProduct (w ++ [s]) : ℂ) * (base m)^w.length * h

/-- The cap curvature reads powers numbered from 1 through the word length. -/
theorem curvature_prefixes (m : ℤ) (w : List Sign) :
    curvature m w = phase m * ∑ j ∈ Finset.range w.length,
      (signProduct (w.take (j+1)) : ℂ) * (base m)^(j+1) := by
  rw [curvature_eq, DyadicCap.polynomial]
  simp_rw [pow_succ, ← mul_assoc, ← Finset.sum_mul]
  have hq := phase_sq m
  unfold base
  linear_combination -(lift m * ∑ j ∈ Finset.range w.length,
    (signProduct (w.take (j+1)) : ℂ) * (phase m * lift m)^j) * hq

/-- The normalized dyadic prime-power readings give these same coefficients
at each integer lift, in the order selected by the word. -/
theorem curvature_dyadic (m : ℤ) (w : List Sign) :
    curvature m w = lift m * ∑ j ∈ Finset.range w.length,
      ((7 * (FieldWeights.primePowerWeight (1/7) (legendreSym 3 2 : ℝ)
        (exponent (w.take (j+1))) - 1) : ℝ) : ℂ) * (base m)^j := by
  rw [curvature_eq, DyadicCap.polynomial]
  simp_rw [recover_character_prefix]

/-- A known nonzero character weight can be removed from every prefix reading
before evaluating the curvature at any integer lift. -/
theorem curvature_weight (m : ℤ) (w : List Sign) (b : ℝ) (hb : b ≠ 0) :
    curvature m w = lift m * ∑ j ∈ Finset.range w.length,
      (((FieldWeights.primePowerWeight b (-1) (exponent (w.take (j+1))) - 1) / b : ℝ) : ℂ) *
        (base m)^j := by
  rw [curvature_eq, DyadicCap.polynomial]
  simp_rw [GeneralWeights.recover_prefix _ b hb]

theorem three_le_norm_base {m : ℤ} (hm : m ≠ 0) : 3 ≤ ‖base m‖ := by
  have ha : (1 : ℝ) ≤ |(m : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm
  rw [norm_base]
  nlinarith [Real.pi_gt_three, mul_nonneg (sub_nonneg.mpr ha) Real.pi_pos.le]

/-- At each fixed nonzero integer lift one curvature recovers the entire
finite chronological word, including its length. -/
theorem curvature_injective {m : ℤ} (hm : m ≠ 0) : Function.Injective (curvature m) := by
  intro u v h
  simp only [curvature_eq] at h
  exact CapDominance.polynomial_injective _ (three_le_norm_base hm)
    (mul_left_cancel₀ (lift_ne_zero hm) h)

end SuperZeta.Resonant
