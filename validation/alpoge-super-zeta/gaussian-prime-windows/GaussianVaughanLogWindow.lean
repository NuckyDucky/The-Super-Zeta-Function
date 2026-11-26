import GaussianVaughanLargestPrime
import Mathlib.Algebra.BigOperators.Module

/-! The two-scale Mellin weight, its Gamma factor on displaced contours,
and the finite signed-prime bound for the logarithmic cutoffs. -/

namespace AlpogeSuperZeta

open Complex Finset
open scoped ComplexConjugate

noncomputable section

/-- At integer left boundaries the reflected Gamma quotient has an exact
finite norm product. The zero at t = 0 agrees with the reciprocal Gamma. -/
theorem gaussianGamma_left_ratio_norm (N : ℕ) (t : ℝ) :
    ‖Gamma (1 + (N : ℂ) - (t : ℂ) * I) / Gamma (-(N : ℂ) + (t : ℂ) * I)‖ =
      |t| * ∏ j ∈ range N, (((j : ℝ) + 1) ^ 2 + t ^ 2) := by
  by_cases ht : t = 0
  · subst t
    simp [Gamma_neg_nat_eq_zero]
  let r : ℂ := (t : ℂ) * I
  change ‖Gamma (1 + (N : ℂ) - r) / Gamma (-(N : ℂ) + r)‖ =
    |t| * ∏ j ∈ range N, (((j : ℝ) + 1) ^ 2 + t ^ 2)
  have hre : r.re = 0 := by simp [r, mul_re]
  have him : r.im = t := by simp [r, mul_im]
  have hneg (n k : ℕ) : -(n : ℂ) + r ≠ -(k : ℂ) := by
    intro h
    apply ht
    simpa [him] using congrArg Complex.im h
  have hg (n : ℕ) : ‖Gamma (-(n : ℂ) + r)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Gamma_ne_zero (hneg n))
  induction N with
  | zero =>
    have hr : r ≠ 0 := by simpa using hneg 0 0
    have hgr : ‖Gamma r‖ ≠ 0 := by simpa using hg 0
    have hc : conj (r + 1) = 1 - r := by
      simp [r, sub_eq_add_neg, add_comm]
    simp only [Nat.cast_zero, add_zero, neg_zero, zero_add, prod_range_zero, mul_one]
    rw [norm_div, ← hc, Gamma_conj, norm_conj, Gamma_add_one _ hr, norm_mul,
      mul_div_cancel_right₀ _ hgr]
    simp [r, norm_real, Real.norm_eq_abs]
  | succ n ih =>
    have hp : 1 + (n : ℂ) - r ≠ 0 := by
      intro h
      apply ht
      simpa [him] using (congrArg Complex.im h).symm
    have hq : -(n.succ : ℂ) + r ≠ 0 := by simpa using hneg n.succ 0
    have hnum : Gamma (1 + (n.succ : ℂ) - r) =
        (1 + (n : ℂ) - r) * Gamma (1 + (n : ℂ) - r) := by
      rw [← Gamma_add_one _ hp]
      congr 1
      push_cast
      ring
    have hden : Gamma (-(n : ℂ) + r) = (-(n.succ : ℂ) + r) *
        Gamma (-(n.succ : ℂ) + r) := by
      rw [← Gamma_add_one _ hq]
      congr 1
      push_cast
      ring
    have he : -(n.succ : ℂ) + r = -(1 + (n : ℂ) - r) := by push_cast; ring
    have hsq : ‖1 + (n : ℂ) - r‖ ^ 2 = ((n : ℝ) + 1) ^ 2 + t ^ 2 := by
      rw [Complex.sq_norm]
      simp [normSq_apply, hre, him, pow_two, add_comm]
    have hrn := norm_ne_zero_iff.mpr hp
    have hgn := hg n.succ
    rw [prod_range_succ, ← mul_assoc, ← ih, norm_div, norm_div, hnum, hden, norm_mul,
      norm_mul, he, norm_neg, ← hsq]
    field_simp

/-- The Mellin multiplier for subtracting the theta reading at twice the
argument with factor exp(log(2)/2). -/
theorem gaussianHalfScale_mellin (f : ℝ → ℂ) {z : ℂ} (hf : MellinConvergent f z) :
    HasMellin (fun v => f v - Complex.exp (((1 / 2 : ℝ) : ℂ) * (Real.log 2 : ℂ)) *
      f (2 * v)) z (gaussianScaleDifference (1 / 2) z * mellin f z) := by
  have h₂ := (MellinConvergent.comp_mul_left (f := f) (s := z) (by norm_num : (0 : ℝ) < 2)).mpr hf
  have hterm := hasMellin_const_smul h₂ (Complex.exp (((1 / 2 : ℝ) : ℂ) * (Real.log 2 : ℂ)))
  refine ⟨(hasMellin_sub hf hterm.1).1, ?_⟩
  have hsub := (hasMellin_sub hf hterm.1).2
  have hval := hterm.2
  simp only [smul_eq_mul] at hsub hval
  rw [hsub, hval, mellin_comp_mul_left f z (by norm_num), smul_eq_mul, gaussianScaleDifference,
    sub_mul, one_mul]
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (↑(2 : ℝ) : ℂ) ≠ 0), ← Complex.ofReal_log (by norm_num)]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring_nf

theorem gaussianHalfScale_zero_ne_zero {z : ℂ} (hz : (1 / 2 : ℝ) < z.re) :
    gaussianScaleDifference (1 / 2) ((1 / 2 : ℝ) : ℂ) = 0 ∧
      gaussianScaleDifference (1 / 2) z ≠ 0 := by
  refine ⟨by simp [gaussianScaleDifference], fun h => ?_⟩
  apply gaussianPairDiagonalFilter_ne_zero hz
  unfold gaussianPairDiagonalFilter
  rw [h, zero_mul]

/-- The exponents in the two tails and the prime-power shift. -/
theorem gaussianLogWindow_exponents :
    (5 / 2 - 1 / 6 : ℝ) * (7 / 15) > 1 ∧
      (1 / 6 : ℝ) * 7 > 1 ∧ 3 * (3 / 8 : ℝ) > 1 ∧
      (3 / 8 : ℝ) < 1 / 2 ∧ (5 / 2 : ℝ) + 1 / 6 = 8 / 3 ∧
      (5 - 8 / 3 : ℝ) * (7 / 15) > 1 := by norm_num

/-- A product in the logarithmic window has a unique possible large prime,
and that prime is smaller than X. -/
theorem gaussianLogWindow_addresses {X ℓ m p : ℝ}
    (hX : 0 < X) (hℓ : 0 < ℓ) (hsep : ℓ ^ (31 / 6 : ℝ) ≤ X)
    (hm : ℓ ^ (1 / 6 : ℝ) < m) (hp : X / ℓ ^ (5 / 2 : ℝ) < p)
    (hmp : m * p ≤ X * ℓ ^ (1 / 6 : ℝ)) :
    m * p < p ^ 2 ∧ m ≤ ℓ ^ (8 / 3 : ℝ) ∧ p < X := by
  have h5 : 0 < ℓ ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hℓ _
  have h1 : 0 < ℓ ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos hℓ _
  have hV : 0 < X / ℓ ^ (5 / 2 : ℝ) := div_pos hX h5
  have hvn : X * ℓ ^ (1 / 6 : ℝ) ≤ (X / ℓ ^ (5 / 2 : ℝ)) ^ 2 := by
    have he : ℓ ^ (1 / 6 : ℝ) * (ℓ ^ (5 / 2 : ℝ)) ^ 2 = ℓ ^ (31 / 6 : ℝ) := by
      rw [pow_two, ← Real.rpow_add hℓ, ← Real.rpow_add hℓ]
      congr 1
      norm_num
    rw [div_pow, le_div_iff₀ (pow_pos h5 _), mul_assoc, he, pow_two]
    exact mul_le_mul_of_nonneg_left hsep hX.le
  have hp0 := hV.trans hp
  refine ⟨hmp.trans_lt (hvn.trans_lt (pow_lt_pow_left₀ hp hV.le (by decide))), ?_, ?_⟩
  · apply le_of_mul_le_mul_right _ hV
    calc
      m * (X / ℓ ^ (5 / 2 : ℝ)) ≤ m * p := mul_le_mul_of_nonneg_left hp.le (h1.le.trans hm.le)
      _ ≤ X * ℓ ^ (1 / 6 : ℝ) := hmp
      _ = ℓ ^ (8 / 3 : ℝ) * (X / ℓ ^ (5 / 2 : ℝ)) := by
        have he : ℓ ^ (1 / 6 : ℝ) * ℓ ^ (5 / 2 : ℝ) = ℓ ^ (8 / 3 : ℝ) := by
          rw [← Real.rpow_add hℓ]
          congr 1
          norm_num
        rw [← he]
        field_simp
  · apply lt_of_mul_lt_mul_left _ h1.le
    simpa only [mul_comm (ℓ ^ (1 / 6 : ℝ)) X] using
      (mul_lt_mul_of_pos_right hm hp0).trans_le hmp

/-- An endpoint and the total variation of the weights bound the effect of
each signed prefix. This applies to log-weighted Frobenius counts. -/
theorem gaussianPrime_abel_bound (n : ℕ) (f g : ℕ → ℂ) (D : ℝ)
    (hD : ∀ k ≤ n, ‖∑ i ∈ range k, g i‖ ≤ D) :
    ‖∑ i ∈ range n, f i * g i‖ ≤
      D * (‖f (n - 1)‖ + ∑ i ∈ range (n - 1), ‖f (i + 1) - f i‖) := by
  have hsum : (∑ i ∈ range n, f i * g i) = ∑ i ∈ range n, f i • g i := by
    simp only [smul_eq_mul]
  rw [hsum, sum_range_by_parts f g n]
  calc
    _ ≤ ‖f (n - 1) • ∑ i ∈ range n, g i‖ +
        ‖∑ i ∈ range (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ :=
      norm_sub_le _ _
    _ ≤ ‖f (n - 1)‖ * D +
        ∑ i ∈ range (n - 1), ‖f (i + 1) - f i‖ * D := by
      apply add_le_add
      · rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hD n le_rfl) (norm_nonneg _)
      · refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
        rw [norm_smul]
        have hi' := mem_range.mp hi
        exact mul_le_mul_of_nonneg_left (hD (i + 1) (by omega)) (norm_nonneg _)
    _ = _ := by rw [← sum_mul, ← add_mul, mul_comm]

#print axioms gaussianGamma_left_ratio_norm
#print axioms gaussianHalfScale_mellin
#print axioms gaussianHalfScale_zero_ne_zero
#print axioms gaussianLogWindow_exponents
#print axioms gaussianLogWindow_addresses
#print axioms gaussianPrime_abel_bound

end
end AlpogeSuperZeta
