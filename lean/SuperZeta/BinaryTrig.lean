import SuperZeta.BinaryAux
import Mathlib.Tactic.LinearCombination

/-! Differential characterization of the rational cosine and sinc series in
the variable `y=z²/2`. The unit-circle and doubling identities follow from
the formal differential equations and their constant terms. -/
namespace SuperZeta.BinaryTrig

open SuperZeta.Binary PowerSeries
noncomputable section

private abbrev S := PowerSeries ℚ
private abbrev D := derivative ℚ

private lemma two_mul_coeff (f : S) (n : ℕ) :
    coeff ℚ n (2*f) = 2 * coeff ℚ n f := by
  simp [two_mul]

private lemma four_mul_coeff (f : S) (n : ℕ) :
    coeff ℚ n (4*f) = 4 * coeff ℚ n f := by
  rw [show (4:S)*f = 2*(2*f) by ring, two_mul_coeff, two_mul_coeff]
  ring

private lemma euler_coeff (f : S) (n : ℕ) :
    coeff ℚ n (X*D f) = n*coeff ℚ n f := by
  cases n with
  | zero => simp
  | succ n => rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

private theorem cos_d : D cosineSeries = -sincSeries := by
  ext n
  rw [coeff_derivative, map_neg]
  simp only [cosineSeries, sincSeries, exponentialSeries, coeff_mk, sincCoeff,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp
  ring

private theorem double_cos_d : D doubleCosineSeries = -(4*doubleSincSeries) := by
  ext n
  rw [coeff_derivative, map_neg, four_mul_coeff]
  simp only [doubleCosineSeries, doubleSincSeries, exponentialSeries, coeff_mk,
    sincCoeff, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, pow_succ]
  field_simp
  ring

private theorem sinc_d : 2*(X*D sincSeries) = cosineSeries-sincSeries := by
  ext n
  rw [two_mul_coeff, euler_coeff, map_sub]
  simp only [sincSeries, cosineSeries, exponentialSeries, coeff_mk]
  ring

private theorem double_sinc_d : 2*(X*D doubleSincSeries) = doubleCosineSeries-doubleSincSeries := by
  ext n
  rw [two_mul_coeff, euler_coeff, map_sub]
  simp only [doubleSincSeries, doubleCosineSeries, exponentialSeries, coeff_mk]
  ring

private lemma cos_zero : constantCoeff ℚ cosineSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  norm_num [cosineSeries, exponentialSeries, sincCoeff]

/-- The formal square identity is valid before taking any valuation. -/
theorem trig_circle : cosineSeries^2 + 2*(X:S)*sincSeries^2 = 1 := by
  apply derivative.ext
  · simp only [map_add, pow_two, Derivation.leibniz, smul_eq_mul, cos_d,
      derivative_X, Derivation.map_one_eq_zero, show D 2 = 0 from Derivation.map_natCast D 2]
    linear_combination 2*sincSeries*sinc_d
  · simp [cos_zero]

private lemma double_cos_zero : constantCoeff ℚ doubleCosineSeries = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  norm_num [doubleCosineSeries, exponentialSeries, sincCoeff]

private theorem unique_double {f g f' g' : S}
    (hf : D f = -(4*g)) (hg : 2*(X*D g)=f-g)
    (hf' : D f' = -(4*g')) (hg' : 2*(X*D g')=f'-g')
    (h0 : constantCoeff ℚ f = constantCoeff ℚ f') : f=f' ∧ g=g' := by
  have get_g (n : ℕ) (hn : coeff ℚ n f = coeff ℚ n f') : coeff ℚ n g = coeff ℚ n g' := by
    have h := congrArg (coeff ℚ n) hg
    have h' := congrArg (coeff ℚ n) hg'
    rw [two_mul_coeff, euler_coeff, map_sub, hn] at h
    rw [two_mul_coeff, euler_coeff, map_sub] at h'
    have hne : (2*(n:ℚ)+1) ≠ 0 := by positivity
    apply mul_left_cancel₀ hne
    linear_combination h - h'
  have hn : ∀ n, coeff ℚ n f = coeff ℚ n f' := by
    intro n
    induction n with
    | zero => simpa only [coeff_zero_eq_constantCoeff] using h0
    | succ n ih =>
      have h := congrArg (coeff ℚ n) hf
      have h' := congrArg (coeff ℚ n) hf'
      rw [coeff_derivative, map_neg, four_mul_coeff, get_g n ih] at h
      rw [coeff_derivative, map_neg, four_mul_coeff] at h'
      exact mul_right_cancel₀ (by positivity : (n:ℚ)+1 ≠ 0) (h.trans h'.symm)
  exact ⟨PowerSeries.ext hn, PowerSeries.ext (fun n => get_g n (hn n))⟩

private theorem double_pair :
    1-4*(X:S)*sincSeries^2 = doubleCosineSeries ∧
    cosineSeries*sincSeries = doubleSincSeries := by
  apply unique_double (g := cosineSeries*sincSeries) (g' := doubleSincSeries) _ _ double_cos_d double_sinc_d
  · simp [double_cos_zero]
  · simp only [map_sub, pow_two, Derivation.leibniz, smul_eq_mul, derivative_X,
      Derivation.map_one_eq_zero, show D 4 = 0 from Derivation.map_natCast D 4]
    linear_combination -4*sincSeries*sinc_d
  · simp only [Derivation.leibniz, smul_eq_mul, cos_d]
    linear_combination cosineSeries*sinc_d + trig_circle

theorem trig_double : cosineSeries*sincSeries = doubleSincSeries := double_pair.2

theorem trig_double_cosine : 4*(X:S)*sincSeries^2 = 1-doubleCosineSeries := by
  linear_combination -double_pair.1

end
end SuperZeta.BinaryTrig
