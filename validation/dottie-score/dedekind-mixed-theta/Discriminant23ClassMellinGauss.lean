import Discriminant23ClassMellinTruncation
import Gauss24PanelTable

namespace FieldTarget

open Complex MeasureTheory Metric Set
open scoped Interval NNReal

noncomputable section

/-- The same logarithmic rule evaluates either class combination. -/
def discriminant23ClassCombinationQuadrature (b : ℝ) (w : ℂ) : ℂ :=
  rationalCompositeRule gauss24Node gauss24Weight
    (fun u ↦ discriminant23ClassCombinationIntegrand b 80 w u) 0 (1 / 16) 32 / 2

private def thetaMass (Q : ℤ → ℤ → ℤ) : ℚ :=
  ∑ p ∈ characterThetaTermsUpTo Q 80, (2 / 3 : ℚ) ^ ((Q p.1 p.2).toNat - 1)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem principal_mass_le : thetaMass discriminant23PrincipalForm ≤ 4 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 5000000 in
private theorem other_mass_le : thetaMass discriminant23OtherForm ≤ 4 := by
  decide +kernel

private theorem norm_exp_mul_heat_pow_le {z : ℂ} (hx : -1 / 2 ≤ z.re)
    (hy : |z.im| ≤ 1 / 2) {k : ℕ} (hk : 1 ≤ k) :
    ‖Complex.exp z * Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z) ^ k‖ ≤
      (2 / 3 : ℝ) ^ (k - 1) := by
  let q := Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)
  have hcos : (7 / 8 : ℝ) ≤ Real.cos z.im := by
    have hs : z.im ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    linarith only [hs, Real.one_sub_sq_div_two_le_cos (x := z.im)]
  have hScale : (1 : ℝ) ≤ discriminant23ThetaScale * Real.cos z.im :=
    (by norm_num : (1 : ℝ) ≤ (13 / 10) * (7 / 8)).trans
      (mul_le_mul discriminant23_thetaScale_interval.1 hcos (by norm_num)
        (by linarith only [discriminant23_thetaScale_interval.1]))
  have hq : ‖q‖ ≤ Real.exp (-Real.exp z.re) := by
    unfold q
    rw [Complex.norm_exp, ← Complex.ofReal_neg, Complex.re_ofReal_mul, Complex.exp_re]
    exact Real.exp_le_exp.mpr (by
      nlinarith only [mul_le_mul_of_nonneg_right hScale (Real.exp_nonneg z.re)])
  have hSmall : ‖q‖ ≤ 2 / 3 := by
    have hPos : (1 / 2 : ℝ) ≤ Real.exp z.re := by
      linarith only [hx, Real.add_one_le_exp z.re]
    refine hq.trans ((Real.exp_le_exp.mpr (neg_le_neg hPos)).trans ?_)
    rw [Real.exp_neg, ← one_div, show (2 / 3 : ℝ) = 1 / (3 / 2) by norm_num]
    exact one_div_le_one_div_of_le (by norm_num)
      (by linarith only [Real.add_one_le_exp (1 / 2 : ℝ)])
  have hExp : ‖Complex.exp z * q‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_exp]
    have hLinear : Real.exp z.re ≤ Real.exp (Real.exp z.re - 1) := by
      linarith only [Real.add_one_le_exp (Real.exp z.re - 1)]
    calc
      _ ≤ Real.exp z.re * Real.exp (-Real.exp z.re) :=
        mul_le_mul_of_nonneg_left hq (Real.exp_nonneg _)
      _ ≤ Real.exp (Real.exp z.re - 1) * Real.exp (-Real.exp z.re) :=
        mul_le_mul_of_nonneg_right hLinear (Real.exp_nonneg _)
      _ = Real.exp (-1) := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := (Real.exp_le_exp.mpr (by norm_num : (-1 : ℝ) ≤ 0)).trans_eq Real.exp_zero
  change ‖Complex.exp z * q ^ k‖ ≤ _
  have hPow : q ^ k = q * q ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk]
  rw [hPow, ← mul_assoc, norm_mul, norm_pow]
  exact (mul_le_mul hExp (pow_le_pow_left₀ (norm_nonneg _) hSmall _) (by positivity)
    zero_le_one).trans_eq (one_mul _)

theorem discriminant23_classCombination_density_norm_le {b : ℝ} (hb : |b| ≤ 2) {z : ℂ}
    (hx : -1 / 2 ≤ z.re) (hy : |z.im| ≤ 1 / 2) :
    ‖Complex.exp z * discriminant23ClassCombinationPolynomial b 80
      (Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z))‖ ≤ 12 := by
  let q := Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)
  have hSum (Q : ℤ → ℤ → ℤ) (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n)
      (hMass : thetaMass Q ≤ 4) :
      ‖∑ p ∈ characterThetaTermsUpTo Q 80, Complex.exp z * q ^ (Q p.1 p.2).toNat‖ ≤ 4 := by
    have hm : (∑ p ∈ characterThetaTermsUpTo Q 80,
        (2 / 3 : ℝ) ^ ((Q p.1 p.2).toNat - 1)) ≤ 4 := by
      have h : (thetaMass Q : ℝ) ≤ ((4 : ℚ) : ℝ) := Rat.cast_mono hMass
      simpa only [thetaMass, Rat.cast_sum, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using h
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum ?_).trans hm)
    intro p hp
    have hne := (Finset.mem_filter.mp hp).2.1
    have hPos : 0 < p.1 ^ 2 + p.2 ^ 2 := by
      by_cases h₁ : p.1 = 0
      · have h₂ : p.2 ≠ 0 := fun h₂ ↦ hne (Prod.ext h₁ h₂)
        exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h₂)
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h₁) (sq_nonneg _)
    have hpQ := hQ p.1 p.2
    exact norm_exp_mul_heat_pow_le hx hy (by omega)
  have hp := hSum _ discriminant23_principal_form_growth principal_mass_le
  have ho := hSum _ discriminant23_other_form_growth other_mass_le
  change ‖Complex.exp z * discriminant23ClassCombinationPolynomial b 80 q‖ ≤ _
  rw [discriminant23ClassCombinationPolynomial, mul_add, mul_left_comm (Complex.exp z) (b : ℂ),
    Finset.mul_sum, Finset.mul_sum]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := mul_le_mul hb ho (norm_nonneg _) (by norm_num)
  linarith only [hp, h]

private theorem norm_gaussIntegrand_le {b : ℝ} (hb : |b| ≤ 2) {w z : ℂ}
    (hlo : -1 / 4 ≤ w.re) (hhi : w.re ≤ 5 / 4) (ht : |w.im| ≤ 30)
    {c r : ℝ} (hc : c ∈ Icc 0 4) (hr₀ : 0 ≤ r) (hr₁ : r ≤ 1 / 2)
    (hz : z ∈ sphere (c : ℂ) r) :
    ‖discriminant23ClassCombinationIntegrand b 80 w z‖ ≤ 24 * Real.exp (1 + 32 * r) := by
  have hd := mem_sphere.mp hz
  rw [dist_eq_norm] at hd
  have hRe := (Complex.abs_re_le_norm (z - (c : ℂ))).trans_eq hd
  have hIm := (Complex.abs_im_le_norm (z - (c : ℂ))).trans_eq hd
  simp only [Complex.sub_re, Complex.ofReal_re] at hRe
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hIm
  have hLower : -r ≤ z.re := by linarith only [(abs_le.mp hRe).1, hc.1]
  have hUpper : z.re ≤ 4 + r := by linarith only [(abs_le.mp hRe).2, hc.2]
  have hE (v : ℂ) (hv₀ : -5 / 4 ≤ v.re) (hv₁ : v.re ≤ 1 / 4)
      (hvt : |v.im| ≤ 30) :
      ‖Complex.exp (v * z)‖ ≤ Real.exp (1 + 32 * r) := by
    have hX : v.re * z.re ≤ 1 + (5 / 4) * r := by
      by_cases hv : 0 ≤ v.re
      · have h := mul_le_mul_of_nonneg_left hUpper hv
        have h' := mul_le_mul_of_nonneg_right hv₁ (show 0 ≤ 4 + r by linarith only [hr₀])
        linarith only [h, h', hr₀]
      · have h := mul_le_mul_of_nonpos_left hLower (le_of_not_ge hv)
        have h' := mul_le_mul_of_nonneg_right (neg_le_neg hv₀) hr₀
        linarith only [h, h']
    have hY : -(v.im * z.im) ≤ 30 * r := by
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      exact mul_le_mul hvt hIm (abs_nonneg _) (by norm_num)
    rw [Complex.norm_exp, Complex.mul_re]
    exact Real.exp_le_exp.mpr (by linarith only [hX, hY, hr₀])
  have h₁ := hE (w - 1)
    (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hlo])
    (by simp only [Complex.sub_re, Complex.one_re]; linarith only [hhi])
    (by simpa only [Complex.sub_im, Complex.one_im, sub_zero] using ht)
  have h₂ := hE (-w)
    (by simp only [Complex.neg_re]; linarith only [hhi])
    (by simp only [Complex.neg_re]; linarith only [hlo])
    (by simpa only [Complex.neg_im, abs_neg] using ht)
  have hDensity := discriminant23_classCombination_density_norm_le hb
    (by linarith only [hLower, hr₁]) (hIm.trans hr₁)
  rw [discriminant23ClassCombinationIntegrand, norm_mul]
  exact (mul_le_mul ((norm_add_le _ _).trans (add_le_add h₁ h₂)) hDensity
    (norm_nonneg _) (by positivity)).trans_eq (by ring)

private theorem exp_nat_upper (n : ℕ) :
    Real.exp (n : ℝ) ≤ (11 / 4 : ℝ) ^ n := by
  rw [show (n : ℝ) = n * (1 : ℝ) by rw [mul_one], Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) (by linarith only [Real.exp_one_lt_d9]) _

private theorem truncation_at_four_le :
    576 * (3 / 11 : ℝ) ^ (58 - 1 : ℕ) + 48 * Real.exp (-(5 / 4 : ℝ) * Real.exp 4) ≤
      2 / 10 ^ 27 := by
  have h4 : (54 : ℝ) ≤ Real.exp 4 := by
    have h := Real.sum_le_exp_of_nonneg (x := (4 : ℝ)) (by norm_num) 10
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h]
  have hNeg : Real.exp (-1) ≤ 3 / 8 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 4
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    rw [Real.exp_neg, ← one_div, show (3 / 8 : ℝ) = 1 / (8 / 3) by norm_num]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [h])
  have hE : Real.exp (-(5 / 4 : ℝ) * Real.exp 4) ≤ (3 / 8 : ℝ) ^ 67 := by
    refine (Real.exp_le_exp.mpr (by linarith only [h4] :
      -(5 / 4 : ℝ) * Real.exp 4 ≤ -67)).trans ?_
    rw [show (-67 : ℝ) = (67 : ℕ) * (-1 : ℝ) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hNeg _
  norm_num at hE ⊢
  linarith only [hE]

private theorem finite_gauss_error {b : ℝ} (hb : |b| ≤ 2) {w : ℂ}
    (hlo : -1 / 4 ≤ w.re) (hhi : w.re ≤ 5 / 4) (ht : |w.im| ≤ 30) :
    ‖(∫ u in (0 : ℝ)..4, discriminant23ClassCombinationIntegrand b 80 w (u : ℂ)) -
      rationalCompositeRule gauss24Node gauss24Weight
        (fun u ↦ discriminant23ClassCombinationIntegrand b 80 w u) 0 (1 / 16) 32‖ ≤
      2 / 10 ^ 26 := by
  have hf : Differentiable ℂ (discriminant23ClassCombinationIntegrand b 80 w) := by
    unfold discriminant23ClassCombinationIntegrand discriminant23ClassCombinationPolynomial
    fun_prop
  have h := rationalCompositeRule_twoRadius_error_le gauss24Node gauss24Weight
    (F := discriminant23ClassCombinationIntegrand b 80 w) (a := 0) (h := 1 / 16)
    (R := (1 / 2 : ℝ≥0)) (r := (1 / 8 : ℝ≥0))
    (M := 24 * Real.exp 17) (mInner := 24 * Real.exp 5) (δ := 1 / 10 ^ 30) (W := 3) 48 32
    (by norm_num) (by norm_num) (by apply NNReal.coe_le_coe.mp; norm_num) (by norm_num)
    gauss24_node_abs_le gauss24_weight_abs_sum_le
    (fun _ hk ↦ gauss24_moment_error_tight hk) hf
    (fun c hc z hz ↦ by
      have h := norm_gaussIntegrand_le hb hlo hhi ht
        (show c ∈ Icc (0 : ℝ) 4 from by convert hc using 1; norm_num)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) le_rfl
        (show z ∈ sphere (c : ℂ) (1 / 2 : ℝ) from hz)
      norm_num at h ⊢
      exact h)
    (fun c hc z hz ↦ by
      have h := norm_gaussIntegrand_le hb hlo hhi ht
        (show c ∈ Icc (0 : ℝ) 4 from by convert hc using 1; norm_num)
        (by norm_num : (0 : ℝ) ≤ 1 / 8) (by norm_num)
        (show z ∈ sphere (c : ℂ) (1 / 8 : ℝ) from hz)
      norm_num at h ⊢
      exact h)
  have hLarge := exp_nat_upper 17
  have hSmall := exp_nat_upper 5
  norm_num at h hLarge hSmall ⊢
  linarith only [h, hLarge, hSmall]

/-- Uniform analytic error for the finite rule across the whole height-29
sampling rectangle. The quadrature term still contains exact exponentials. -/
theorem discriminant23_classCombination_quadrature_error {b : ℝ} (hb : |b| ≤ 2) {w : ℂ}
    (hlo : -1 / 4 ≤ w.re) (hhi : w.re ≤ 5 / 4) (ht : |w.im| ≤ 30) :
    ‖discriminant23ClassCombinationReading b w - discriminant23ClassCombinationQuadrature b w‖ ≤
      2 / 10 ^ 26 := by
  let I := ∫ u in (0 : ℝ)..4, discriminant23ClassCombinationIntegrand b 80 w (u : ℂ)
  let Q := rationalCompositeRule gauss24Node gauss24Weight
    (fun u ↦ discriminant23ClassCombinationIntegrand b 80 w u) 0 (1 / 16) 32
  have hI : ‖2 * discriminant23ClassCombinationReading b w - I‖ ≤ 2 / 10 ^ 27 :=
    (discriminant23_classCombination_integral_error hb
      (N := 80) (order := 58) (by decide) (by decide)
      (show (0 : ℝ) ≤ 4 by norm_num) (by linarith only [hlo])
      (by linarith only [hhi])).trans truncation_at_four_le
  have hQ : ‖I - Q‖ ≤ 2 / 10 ^ 26 := finite_gauss_error hb hlo hhi ht
  have h := (norm_sub_le_norm_sub_add_norm_sub _ I Q).trans (add_le_add hI hQ)
  change ‖discriminant23ClassCombinationReading b w - Q / 2‖ ≤ _
  rw [show discriminant23ClassCombinationReading b w - Q / 2 =
    (2 * discriminant23ClassCombinationReading b w - Q) / 2 by ring, norm_div, Complex.norm_ofNat]
  linarith only [h]

#check @discriminant23_classCombination_quadrature_error
#print axioms principal_mass_le
#print axioms other_mass_le
#print axioms discriminant23_classCombination_quadrature_error

end
end FieldTarget
