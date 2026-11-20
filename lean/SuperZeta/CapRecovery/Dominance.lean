import SuperZeta.CapRecovery.DyadicCap
import Mathlib.Data.Real.Pi.Bounds

/-! Separation of arbitrary finite signed polynomials in the complex plane.
The head of the list is the coefficient of the lowest power. -/
noncomputable section
namespace SuperZeta.CapDominance
open SignWords

private def digit : Sign → ℂ
  | .plus => 1
  | .minus => -1

def value (t : ℂ) : List Sign → ℂ
  | [] => 0
  | s :: w => digit s + t * value t w

private theorem value_nil (t : ℂ) : value t [] = 0 := rfl

private theorem norm_digit (a : Sign) : ‖digit a‖ = 1 := by
  cases a <;> simp [digit]

private theorem step (t x e : ℂ) (ht : 3 ≤ ‖t‖) (hx : 1 ≤ ‖x‖)
    (he : ‖e‖ ≤ 2) : 1 ≤ ‖e+t*x‖ := by
  have h : ‖t*x‖ ≤ ‖e+t*x‖ + ‖e‖ := by
    simpa using norm_sub_le (e+t*x) e
  rw [norm_mul] at h
  have hh : 3 * 1 ≤ ‖t‖ * ‖x‖ :=
    mul_le_mul ht hx (by norm_num) (norm_nonneg t)
  linarith

private theorem magnitude (t : ℂ) (ht : 3 ≤ ‖t‖) (a : Sign) (w : List Sign) :
    1 ≤ ‖value t (a :: w)‖ := by
  induction w generalizing a with
  | nil => simp [value, norm_digit]
  | cons b tail ih =>
    exact step t _ _ ht (ih b) (by rw [norm_digit]; norm_num)

/-- Unequal lists give separated values, even at different lengths. -/
theorem separated (t : ℂ) (ht : 3 ≤ ‖t‖) (u v : List Sign) (hne : u ≠ v) :
    1 ≤ ‖value t u - value t v‖ := by
  induction u generalizing v with
  | nil =>
    cases v with
    | nil => exact (hne rfl).elim
    | cons b tail => simpa [value_nil] using magnitude t ht b tail
  | cons a xs ih =>
    cases v with
    | nil => simpa [value_nil] using magnitude t ht a xs
    | cons b ys =>
      have eqn : value t (a :: xs) - value t (b :: ys) =
          (digit a - digit b) + t*(value t xs - value t ys) := by
        simp only [value]; ring
      rw [eqn]
      by_cases hxy : xs = ys
      · subst ys
        have hab : a ≠ b := by intro h; subst b; exact hne rfl
        cases a <;> cases b <;> simp_all [digit] <;> norm_num
      · apply step t _ _ ht (ih ys hxy)
        have h := norm_sub_le (digit a) (digit b)
        rw [norm_digit, norm_digit] at h
        linarith

theorem injective (t : ℂ) (ht : 3 ≤ ‖t‖) : Function.Injective (value t) := by
  intro u v h
  by_contra hne
  have hgap := separated t ht u v hne
  simp [h] at hgap
  linarith

/-- Specialization to the exponential cap, with the missing constant term
restored by multiplying the value by minus the base. -/
theorem capPolynomial_injective :
    Function.Injective (fun w =>
      (Real.pi * Complex.I) * value (-(Real.pi * Complex.I)) w) := by
  let r : ℂ := Real.pi * Complex.I
  have hr : ‖-r‖ = Real.pi := by simp [r, norm_mul, abs_of_pos Real.pi_pos]
  have hr0 : r ≠ 0 := mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  intro u v h
  exact injective (-r) (hr.symm ▸ Real.pi_gt_three.le) (mul_left_cancel₀ hr0 h)

private noncomputable def prefixes : List Sign → List Sign
  | [] => []
  | .plus :: tail => .plus :: prefixes tail
  | .minus :: tail => .minus :: (prefixes tail).map Sign.flip

private theorem flip_flip (a : Sign) : a.flip.flip = a := by cases a <;> rfl

private theorem prefix_injective : Function.Injective prefixes := by
  intro u
  induction u with
  | nil => intro v h; cases v with
           | nil => rfl
           | cons b ys => cases b <;> simp [prefixes] at h
  | cons a xs ih =>
    intro v h
    cases v with
    | nil => cases a <;> simp [prefixes] at h
    | cons b ys =>
      cases a <;> cases b <;> simp [prefixes] at h ⊢
      · exact ih h
      · apply ih
        have hh := congrArg (List.map Sign.flip) h
        simpa [List.map_map, Function.comp_def, flip_flip] using hh

private theorem value_flip (t : ℂ) (w : List Sign) :
    value t (w.map Sign.flip) = - value t w := by
  induction w with
  | nil => simp [value]
  | cons s w ih =>
    cases s <;> simp [value, Sign.flip, digit, ih] <;> ring

private theorem polynomial_cons (s : Sign) (w : List Sign) (t : ℂ) :
    DyadicCap.polynomial (s::w) t = (DyadicWeights.letter s : ℂ) *
      (1 + t * DyadicCap.polynomial w t) := by
  unfold DyadicCap.polynomial
  rw [List.length_cons, Finset.sum_range_succ']
  simp only [List.take_succ_cons, DyadicWeights.signProduct, List.map_cons, List.prod_cons,
    List.take_zero, List.map_nil, List.prod_nil, mul_one, pow_zero, Complex.ofReal_mul]
  rw [mul_add, mul_one, ← mul_assoc, Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [pow_succ]
  ring

private theorem value_prefixes (t : ℂ) (w : List Sign) :
    value t (prefixes w) = DyadicCap.polynomial w t := by
  induction w with
  | nil => simp [prefixes, value, DyadicCap.polynomial]
  | cons s w ih =>
    rw [polynomial_cons]
    cases s <;> simp [prefixes, value, value_flip, ih, DyadicWeights.letter, digit]
    ring

/-- The second-to-first derivative ratio of the actual exponential maps at their
common cap identifies every finite chronological word, even its length. -/
theorem cap_ratio_injective : Function.Injective (fun w : List Sign =>
    deriv (deriv (eval CapJets.lift w)) 1 / deriv (eval CapJets.lift w) 1) := by
  intro u v h
  simp only [CapJets.jet_ratio, (DyadicCap.jet_prefixes _).2, ← value_prefixes] at h
  exact prefix_injective (capPolynomial_injective h)

end SuperZeta.CapDominance
