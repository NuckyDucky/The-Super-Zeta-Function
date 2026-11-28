import Discriminant23GaussHeat

namespace FieldTarget

open Complex Finset

noncomputable section

set_option exponentiation.threshold 512

def gaussMomentScale : ℕ := 2 ^ 256

def gaussPanelMoment (p : ℕ) (i : Fin 24) (k : ℕ) : ℝ :=
  gaussPanelNode p i ^ k / (k.factorial : ℝ)

private def gaussMomentNodeNumerator (p : ℕ) (i : Fin 24) : ℤ :=
  (2 * (p : ℤ) + 1) * 10 ^ 30 + (gauss24Pair i).1

private def gaussMomentNodeDenominator : ℕ := 16 * 10 ^ 30

private def gaussPanelMomentDenominator (k : ℕ) : ℕ :=
  gaussMomentNodeDenominator ^ k * k.factorial

/-- Compute the exact rational moment and round it with one integer division. -/
def gaussPanelMomentNumerator (p : ℕ) (i : Fin 24) (k : ℕ) : ℤ :=
  (gaussMomentScale : ℤ) * (gaussMomentNodeNumerator p i) ^ k / (gaussPanelMomentDenominator k : ℤ)

private theorem gaussMomentNode_eq (p : ℕ) (i : Fin 24) :
    (gaussMomentNodeNumerator p i : ℝ) / (gaussMomentNodeDenominator : ℝ) = gaussPanelNode p i := by
  unfold gaussMomentNodeNumerator gaussMomentNodeDenominator gaussPanelNode gauss24Node gauss24Denominator
  push_cast
  ring

theorem gaussPanelMoment_mem {p : ℕ} (hp : p < 32) (i : Fin 24) (k : ℕ) :
    0 ≤ gaussPanelMoment p i k ∧ gaussPanelMoment p i k ≤ 64 := by
  have hu := gaussPanelNode_nonneg p i
  refine ⟨div_nonneg (pow_nonneg hu _) (by positivity), ?_⟩
  have hOne : gaussPanelMoment p i k ≤ ∑ j ∈ Finset.range (k + 1), gaussPanelMoment p i j := by
    apply Finset.single_le_sum _ (mem_range.mpr (Nat.lt_succ_self k))
    intro j _
    exact div_nonneg (pow_nonneg hu j) (by positivity : (0 : ℝ) ≤ (j.factorial : ℝ))
  exact hOne.trans ((Real.sum_le_exp_of_nonneg hu (k + 1)).trans (gaussPanelExp_le_sixtyFour hp i))

/-- The moment denominator is shared by all nodes at a given degree. -/
theorem discriminant23_gaussPanelMoment_error (p : ℕ) (i : Fin 24) (k : ℕ) :
    |gaussPanelMoment p i k -
      (gaussPanelMomentNumerator p i k : ℝ) / (gaussMomentScale : ℝ)| ≤ 2 / 10 ^ 45 := by
  let a : GaussianInt := ⟨(gaussMomentScale : ℤ) * (gaussMomentNodeNumerator p i) ^ k, 0⟩
  let d := gaussPanelMomentDenominator k
  have hd : 0 < d := by dsimp [d, gaussPanelMomentDenominator, gaussMomentNodeDenominator]; positivity
  have hS : 0 < gaussMomentScale := by norm_num [gaussMomentScale]
  have hTerm := (Complex.abs_re_le_norm _).trans (norm_gaussianFloorDiv_error a hd hS)
  rw [Complex.sub_re, gaussianScaled_re_eq, gaussianScaled_re_eq, Nat.cast_mul] at hTerm
  have hExact : (a.re : ℝ) / ((gaussMomentScale : ℝ) * (d : ℝ)) = gaussPanelMoment p i k := by
    change (((gaussMomentScale : ℤ) * (gaussMomentNodeNumerator p i) ^ k : ℤ) : ℝ) /
      ((gaussMomentScale : ℝ) * (d : ℝ)) = _
    have hS' : (gaussMomentScale : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
    push_cast
    rw [mul_div_mul_left _ _ hS']
    unfold d gaussPanelMomentDenominator gaussPanelMoment
    push_cast
    rw [← gaussMomentNode_eq, div_pow, div_div]
  rw [hExact] at hTerm
  exact hTerm.trans (by norm_num [gaussMomentScale])

#print axioms gaussPanelMoment_mem
#print axioms discriminant23_gaussPanelMoment_error

end
end FieldTarget
