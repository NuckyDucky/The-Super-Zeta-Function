import DedekindDiscriminant23CharacterPanel
import DedekindDiscriminant23CountFromSigns
import Mathlib.Analysis.Complex.ExponentialBounds

namespace FieldTarget

open MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

/-- The five nonzero terms below degree 13 in the difference of the class theta series. -/
def discriminant23SparsePolynomial (q : ℝ) : ℝ :=
  2 * (q - q ^ 2 - q ^ 3 + q ^ 6 + q ^ 8)

/-- The finite identity only uses the already checked theta coefficient table. -/
theorem discriminant23_characterPolynomial_sub_sparse (q : ℝ) :
    discriminant23CharacterPolynomial q - discriminant23SparsePolynomial q =
      ∑ k ∈ Finset.range 20, (discriminant23CharacterCoefficient (13 + k) : ℝ) * q ^ (13 + k) := by
  have hhead :
      (∑ k ∈ Finset.range 13, (discriminant23CharacterCoefficient k : ℝ) * q ^ k) =
        discriminant23SparsePolynomial q := by
    norm_num [Finset.sum_range_succ, discriminant23CharacterCoefficient,
      discriminant23SparsePolynomial]
    ring
  unfold discriminant23CharacterPolynomial
  rw [show (33 : ℕ) = 13 + 20 by decide, Finset.sum_range_add, hhead, add_sub_cancel_left]

/-- Dropping the later terms costs at most three times the thirteenth power
on the real heat coordinate used by the folded integral. -/
theorem discriminant23_characterPolynomial_sparse_error {q : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1 / 3) :
    |discriminant23CharacterPolynomial q - discriminant23SparsePolynomial q| ≤ 3 * q ^ 13 := by
  rw [discriminant23_characterPolynomial_sub_sparse]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hs : ∑ k ∈ Finset.range 20, (2 : ℚ) * (1 / 3 : ℚ) ^ k ≤ 3 := by decide +kernel
  have hs' : ∑ k ∈ Finset.range 20, (2 : ℝ) * (1 / 3 : ℝ) ^ k ≤ 3 := by
    have hreal : ((∑ k ∈ Finset.range 20, (2 : ℚ) * (1 / 3 : ℚ) ^ k : ℚ) : ℝ) ≤
      ((3 : ℚ) : ℝ) := Rat.cast_le.mpr hs
    push_cast at hreal
    exact hreal
  calc
    _ ≤ ∑ k ∈ Finset.range 20, (2 * (1 / 3 : ℝ) ^ k) * q ^ 13 := by
      apply Finset.sum_le_sum
      intro k hk
      have hidx : 13 + k < 33 := by have := Finset.mem_range.mp hk; omega
      have hc : |(discriminant23CharacterCoefficient (13 + k) : ℝ)| ≤ 2 := by
        exact_mod_cast discriminant23_characterCoefficient_abs_le ⟨13 + k, hidx⟩
      rw [abs_mul, abs_pow, abs_of_nonneg hq₀, pow_add, mul_left_comm,
        mul_comm (q ^ 13)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hc (pow_le_pow_left₀ hq₀ hq₁ k) (by positivity) (by norm_num))
        (by positivity)
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hs' (by positivity)

/-- Keep the existing logarithmic integration interval and replace only the polynomial. -/
def discriminant23SparseModel (w : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..3,
    (Complex.exp (w * (u : ℂ)) + Complex.exp ((1 - w) * (u : ℂ))) *
      (discriminant23SparsePolynomial
        (Real.exp (-discriminant23ThetaScale * Real.exp u)) : ℂ)

theorem discriminant23_sparseModel_differentiable :
    Differentiable ℂ discriminant23SparseModel := by
  let f : ℝ → ℂ := fun x ↦ (discriminant23SparsePolynomial
    (Real.exp (-discriminant23ThetaScale * x)) : ℂ)
  have hf : Continuous f := by dsimp [f, discriminant23SparsePolynomial]; fun_prop
  have htop : 1 ≤ Real.exp 3 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hmodel : discriminant23SparseModel = foldedMellinTruncation f (Real.exp 3) := by
    funext w
    let g (x : ℝ) := foldedMellinWeight w x * f x
    have hcont : ContinuousOn g (Real.exp '' [[(0 : ℝ), 3]]) := by
      have hl : ContinuousOn (fun x : ℝ ↦ (Real.log x : ℂ)) (Real.exp '' [[(0 : ℝ), 3]]) :=
        Complex.continuous_ofReal.comp_continuousOn fun x hx ↦
          (Real.continuousAt_log (by obtain ⟨u, _, rfl⟩ := hx; exact (Real.exp_pos u).ne')).continuousWithinAt
      unfold g foldedMellinWeight
      exact ((Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hl)).add
        (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hl))).mul hf.continuousOn
    have he := intervalIntegral.integral_deriv_smul_comp' (a := (0 : ℝ)) (b := 3)
      (fun u _ ↦ Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn hcont
    rw [Real.exp_zero] at he
    change discriminant23SparseModel w = ∫ x in (1 : ℝ)..Real.exp 3, g x
    rw [← he, discriminant23SparseModel]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only [g, f, foldedMellinWeight, Function.comp_apply]
    simp only [Real.log_exp, Complex.real_smul, Complex.ofReal_exp]
    rw [← mul_assoc, mul_add, ← Complex.exp_add, ← Complex.exp_add,
      show (u : ℂ) + (w - 1) * (u : ℂ) = w * (u : ℂ) by ring,
      show (u : ℂ) + -w * (u : ℂ) = (1 - w) * (u : ℂ) by ring]
  rw [hmodel]
  exact foldedMellinTruncation_differentiable htop (hf.intervalIntegrable _ _)

private theorem sparse_majorant_integral :
    (∫ u in (0 : ℝ)..3, 6 * Real.exp (-(169 / 10 : ℝ)) *
      Real.exp (-(149 / 10 : ℝ) * u)) ≤ 1 / 20000000 := by
  have hExpOne : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hExpSixteen : Real.exp (-(16 : ℝ)) ≤ (3 / 8 : ℝ) ^ 16 := by
    have hOne : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
      rw [Real.exp_neg, ← one_div, show (3 / 8 : ℝ) = 1 / (8 / 3) by norm_num]
      exact one_div_le_one_div_of_le (by norm_num) hExpOne
    rw [show (-(16 : ℝ)) = (16 : ℕ) * (-1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hOne 16
  have hExpFraction : Real.exp (-(9 / 10 : ℝ)) ≤ 10 / 19 := by
    rw [Real.exp_neg, ← one_div, show (10 / 19 : ℝ) = 1 / (19 / 10) by norm_num]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [Real.add_one_le_exp (9 / 10)])
  have hExp : Real.exp (-(169 / 10 : ℝ)) ≤ (3 / 8 : ℝ) ^ 16 * (10 / 19) := by
    rw [show (-(169 / 10 : ℝ)) = -16 + -(9 / 10) by norm_num, Real.exp_add]
    exact mul_le_mul hExpSixteen hExpFraction (Real.exp_nonneg _) (by norm_num)
  rw [intervalIntegral.integral_const_mul]
  have hInterval :
      (∫ u in (0 : ℝ)..3, Real.exp (-(149 / 10 : ℝ) * u)) ≤ 10 / 149 := by
    rw [intervalIntegral.integral_comp_mul_left Real.exp
      (by norm_num : (-(149 / 10 : ℝ)) ≠ 0), integral_exp]
    have h := Real.exp_nonneg (-(149 / 10 : ℝ) * 3)
    simp only [mul_zero, Real.exp_zero, smul_eq_mul]
    linarith only [h, show (-(149 / 10 : ℝ))⁻¹ = -(10 / 149) by norm_num]
  calc
    _ ≤ (6 * ((3 / 8 : ℝ) ^ 16 * (10 / 19))) * (10 / 149) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hExp (by norm_num)) hInterval
        (intervalIntegral.integral_nonneg (by norm_num) (fun u _ ↦ Real.exp_nonneg _)) (by positivity)
    _ ≤ _ := by norm_num

/-- Five heat powers approximate the original compact model on a strip that is
one unit wider on either side. There is no restriction on height. -/
theorem discriminant23_sparseModel_error {w : ℂ} (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2) :
    ‖discriminant23CharacterComplexModel w - discriminant23SparseModel w‖ ≤ 1 / 20000000 := by
  let e (u : ℝ) := Complex.exp (w * (u : ℂ)) + Complex.exp ((1 - w) * (u : ℂ))
  let q (u : ℝ) := Real.exp (-discriminant23ThetaScale * Real.exp u)
  let f (u : ℝ) : ℂ := e u * (discriminant23CharacterPolynomial (q u) : ℂ)
  let g (u : ℝ) : ℂ := e u * (discriminant23SparsePolynomial (q u) : ℂ)
  let B (u : ℝ) := 6 * Real.exp (-(169 / 10 : ℝ)) * Real.exp (-(149 / 10 : ℝ) * u)
  have hf : Continuous f := by dsimp [f, e, q, discriminant23CharacterPolynomial]; fun_prop
  have hg : Continuous g := by dsimp [g, e, q, discriminant23SparsePolynomial]; fun_prop
  have hB : Continuous B := by dsimp [B]; fun_prop
  have hab : (0 : ℝ) ≤ 3 := by norm_num
  change ‖(∫ u in (0 : ℝ)..3, f u) - ∫ u in (0 : ℝ)..3, g u‖ ≤ _
  rw [← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
  refine (intervalIntegral.integral_mono_on hab ((hf.sub hg).norm.intervalIntegrable _ _)
    (hB.intervalIntegrable _ _) ?_).trans sparse_majorant_integral
  intro u hu
  have hu₀ : 0 ≤ u := hu.1
  have hα := discriminant23_thetaScale_interval.1
  have hα₀ : 0 ≤ discriminant23ThetaScale := by linarith only [hα]
  have hExp : 1 + u ≤ Real.exp u := by linarith only [Real.add_one_le_exp u]
  have hsmall : q u ≤ 1 / 3 := by
    have hl := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ Real.exp u by linarith only [hExp, hu₀]) hα₀
    have he : q u ≤ Real.exp (-discriminant23ThetaScale) :=
      Real.exp_le_exp.mpr (by linarith only [hl])
    exact he.trans (discriminant23_thetaExp_interval.2.trans (by norm_num))
  have hq₁ : (q u) ^ 13 ≤ Real.exp (-(169 / 10 : ℝ) * (1 + u)) := by
    dsimp only [q]
    rw [← Real.exp_nat_mul]
    have h := mul_le_mul hα hExp (by linarith only [hu₀]) hα₀
    apply Real.exp_le_exp.mpr
    linarith only [h]
  have he : ‖e u‖ ≤ 2 * Real.exp (2 * u) := by
    refine (norm_add_le _ _).trans ?_
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, Complex.sub_re, Complex.one_re]
    have h₁ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi hu₀)
    have h₂ := Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (show 1 - w.re ≤ 2 by linarith only [hlo]) hu₀)
    linarith only [h₁, h₂]
  simp only [f, g, B, Pi.sub_apply]
  rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (2 * Real.exp (2 * u)) * (3 * (q u) ^ 13) :=
      mul_le_mul he (discriminant23_characterPolynomial_sparse_error (Real.exp_nonneg _) hsmall)
        (abs_nonneg _) (by positivity)
    _ ≤ (2 * Real.exp (2 * u)) * (3 * Real.exp (-(169 / 10 : ℝ) * (1 + u))) := by
      gcongr
    _ = 6 * Real.exp (2 * u + -(169 / 10 : ℝ) * (1 + u)) := by rw [Real.exp_add]; ring
    _ = _ := by
      rw [show 2 * u + -(169 / 10 : ℝ) * (1 + u) =
        -(169 / 10 : ℝ) + -(149 / 10 : ℝ) * u by ring, Real.exp_add]
      ring

/-- The same five-term replacement controls the derivative on the critical strip. -/
theorem discriminant23_sparseModel_deriv_error {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖deriv discriminant23CharacterComplexModel w - deriv discriminant23SparseModel w‖ ≤
      1 / 20000000 := by
  have h := iteratedDeriv_error_le_of_strip
    discriminant23_characterComplexModel_differentiable discriminant23_sparseModel_differentiable
    1 (ρ := 1) (E := 1 / 20000000) (by norm_num)
    (fun z hz₀ hz₁ ↦ discriminant23_sparseModel_error hz₀ (by linarith only [hz₁])) hlo hhi
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, pow_one, mul_one, one_mul, div_one] using h

/-- Evaluating the signs on the five-term model adds its explicit allowance
to the three thresholds of the original character count. -/
theorem discriminant23_character_counts_at_eleven_halves_of_sparse_signs
    (hBelow : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (7 / 6) (9 / 2) →
      201 / 20000000 < (discriminant23SparseModel w).re)
    (hAbove : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (83 / 16) (11 / 2) →
      (discriminant23SparseModel w).re < -(201 / 20000000))
    (hSlope : ∀ w : ℂ, w.re ∈ Icc (0 : ℝ) 1 → w.im ∈ Icc (9 / 2) (83 / 16) →
      201 / 20000000 < (deriv discriminant23SparseModel w).im) :
    discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun _ ↦ True) = 2 ∧
      discriminant23CharacterCountingFunction.stripZeroCount (11 / 2) (fun w ↦ w.re = 1 / 2) = 2 := by
  have hrError (w : ℂ) (hr : w.re ∈ Icc (0 : ℝ) 1) :
      |(discriminant23CharacterComplexModel w).re - (discriminant23SparseModel w).re| ≤
        1 / 20000000 := by
    have h := (Complex.abs_re_le_norm _).trans (discriminant23_sparseModel_error
      (w := w) (by linarith only [hr.1]) (by linarith only [hr.2]))
    rwa [Complex.sub_re] at h
  refine discriminant23_character_counts_at_eleven_halves_of_model_signs ?_ ?_ ?_
  · intro w hr ht
    linarith only [(abs_le.mp (hrError w hr)).1, hBelow w hr ht]
  · intro w hr ht
    linarith only [(abs_le.mp (hrError w hr)).2, hAbove w hr ht]
  · intro w hr ht
    have h := (Complex.abs_im_le_norm _).trans (discriminant23_sparseModel_deriv_error hr.1 hr.2)
    rw [Complex.sub_im] at h
    linarith only [(abs_le.mp h).1, hSlope w hr ht]

#check @discriminant23_sparseModel_error
#check @discriminant23_sparseModel_deriv_error
#check @discriminant23_character_counts_at_eleven_halves_of_sparse_signs
#print axioms discriminant23_characterPolynomial_sub_sparse
#print axioms discriminant23_characterPolynomial_sparse_error
#print axioms discriminant23_sparseModel_differentiable
#print axioms discriminant23_sparseModel_error
#print axioms discriminant23_sparseModel_deriv_error
#print axioms discriminant23_character_counts_at_eleven_halves_of_sparse_signs

end

end FieldTarget

