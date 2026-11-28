import Discriminant23GaussCoefficientData
import DedekindDiscriminant23Height29TaylorData

namespace FieldTarget

open Complex Finset

noncomputable section

set_option exponentiation.threshold 512

private theorem norm_add_mul_error {a a' b b' scale : ℂ} {e₁ e₂ : ℝ}
    (ha : ‖a - a'‖ ≤ e₁) (hb : ‖b - b'‖ ≤ e₂) :
    ‖(a + scale * b) - (a' + scale * b')‖ ≤ e₁ + ‖scale‖ * e₂ := by
  rw [show (a + scale * b) - (a' + scale * b') = (a - a') + scale * (b - b') by ring]
  exact (norm_add_le _ _).trans
    (add_le_add ha (by rw [norm_mul]; exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)))

private theorem norm_mellin_product_error
    {m m' x x' y y' z z' : ℂ}
    (hm : ‖m‖ ≤ 64) (hx₀ : 1 ≤ ‖x‖) (hx₁ : ‖x‖ ≤ 64)
    (hxy : ‖x * y‖ ≤ 12) (hz : ‖z‖ ≤ 2)
    (hmE : ‖m - m'‖ ≤ 2 / 10 ^ 45) (hxE : ‖x - x'‖ ≤ 1 / 10 ^ 47)
    (hyE : ‖y - y'‖ ≤ 6 / 10 ^ 33) (hzE : ‖z - z'‖ ≤ 2 / 10 ^ 51) :
    ‖m * x * y * z - m' * x' * y' * z'‖ ≤ 6 / 10 ^ 29 := by
  have hy : ‖y‖ ≤ 12 := by
    have h := mul_le_mul_of_nonneg_right hx₀ (norm_nonneg y)
    rw [one_mul, ← norm_mul] at h
    exact h.trans hxy
  have hm' : ‖m'‖ ≤ 65 := by
    have h := norm_le_norm_sub_add m' m
    rw [norm_sub_rev] at h
    linarith only [h, hm, hmE]
  have hx' : ‖x'‖ ≤ 65 := by
    have h := norm_le_norm_sub_add x' x
    rw [norm_sub_rev] at h
    linarith only [h, hx₁, hxE]
  have hy' : ‖y'‖ ≤ 13 := by
    have h := norm_le_norm_sub_add y' y
    rw [norm_sub_rev] at h
    linarith only [h, hy, hyE]
  have first : ‖(m - m') * (x * y) * z‖ ≤ (2 / 10 ^ 45 : ℝ) * 12 * 2 := by
    rw [norm_mul, norm_mul]
    gcongr
  have second : ‖m' * (x - x') * y * z‖ ≤ (65 : ℝ) * (1 / 10 ^ 47) * 12 * 2 := by
    simp only [norm_mul]
    gcongr
  have third : ‖m' * x' * (y - y') * z‖ ≤ (65 : ℝ) * 65 * (6 / 10 ^ 33) * 2 := by
    simp only [norm_mul]
    gcongr
  have fourth : ‖m' * x' * y' * (z - z')‖ ≤ (65 : ℝ) * 65 * 13 * (2 / 10 ^ 51) := by
    simp only [norm_mul]
    gcongr
  rw [show m * x * y * z - m' * x' * y' * z' =
      ((m - m') * (x * y) * z + m' * (x - x') * y * z) +
        (m' * x' * (y - y') * z + m' * x' * y' * (z - z')) by ring]
  exact (norm_add_le _ _).trans
    ((add_le_add ((norm_add_le _ _).trans (add_le_add first second))
      ((norm_add_le _ _).trans (add_le_add third fourth))).trans (by norm_num))

private theorem gaussianScaled_real_eq (r : ℤ) (d : ℕ) :
    gaussianScaled ⟨r, 0⟩ d = (((r : ℝ) / (d : ℝ) : ℝ) : ℂ) := by
  simp [gaussianScaled, GaussianInt.toComplex_def']

private theorem gaussianScaled_add_mul (a b c : GaussianInt) (s : ℕ) :
    gaussianScaled (a + b * c) s = gaussianScaled a s + (b : ℂ) * gaussianScaled c s := by
  simp only [gaussianScaled, GaussianInt.toComplex_add, GaussianInt.toComplex_mul, add_div,
    mul_div_assoc]

private def thetaAtNode (p : ℕ) (i : Fin 24) (principal : Bool) : ℂ :=
  ∑ xy ∈ characterThetaTermsUpTo (gaussThetaForm principal) 80,
    (gaussPanelHeat p i : ℂ) ^ (gaussThetaForm principal xy.1 xy.2).toNat

private theorem heatAtNode_eq (p : ℕ) (i : Fin 24) :
    Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp (gaussPanelNode p i : ℂ)) =
      (gaussPanelHeat p i : ℂ) := by
  unfold gaussPanelHeat
  push_cast
  rfl

private theorem thetaAtNode_combination (b : ℤ) (p : ℕ) (i : Fin 24) :
    discriminant23ClassCombinationPolynomial (b : ℝ) 80 (gaussPanelHeat p i : ℂ) =
      thetaAtNode p i true + (b : ℂ) * thetaAtNode p i false := by
  simp only [discriminant23ClassCombinationPolynomial, thetaAtNode, gaussThetaForm,
    ite_true, Bool.false_eq_true, ite_false, Complex.ofReal_intCast]

private theorem weighted_grid_eq (i : Fin 24) :
    ((gauss24Pair i).2 : ℂ) / (gaussWeightDenominator : ℂ) =
      (((gauss24Weight i : ℝ) / 32 : ℝ) : ℂ) := by
  unfold gauss24Weight gaussWeightDenominator gauss24Denominator
  push_cast
  ring

private theorem gaussPanelCoefficientNumerator_scaled (b : ℤ) (p : ℕ) (i : Fin 24)
    (k : ℕ) (a : GaussPanelApproximation) :
    gaussianScaled (gaussPanelCoefficientNumerator b p i k a) gaussCoefficientDenominator =
      (((gauss24Weight i : ℝ) / 32 : ℝ) : ℂ) *
        gaussianScaled ⟨gaussPanelMomentNumerator p i k, 0⟩ gaussMomentScale *
        gaussianScaled ⟨a.expNode, 0⟩ gaussExpScale *
        gaussianScaled (a.principal + (b : GaussianInt) * a.other) gaussExpScale *
        gaussianScaled (a.plusPhase + (-1 : GaussianInt) ^ k * a.minusPhase) gaussExpScale := by
  rw [← weighted_grid_eq]
  simp only [gaussPanelCoefficientNumerator, gaussCoefficientDenominator, gaussianScaled,
    GaussianInt.toComplex_mul, GaussianInt.toComplex_def',
    Nat.cast_mul, Nat.cast_pow, Int.cast_mul]
  have hW : (gaussWeightDenominator : ℂ) ≠ 0 := by norm_num [gaussWeightDenominator]
  have hX : (gaussExpScale : ℂ) ≠ 0 := by norm_num [gaussExpScale]
  have hM : (gaussMomentScale : ℂ) ≠ 0 := by norm_num [gaussMomentScale]
  field_simp
  ring

private theorem exp_norm_le_one {z : ℂ} {u : ℝ} (hz : z.re ≤ 0) (hu : 0 ≤ u) :
    ‖Complex.exp (z * (u : ℂ))‖ ≤ 1 := by
  rw [Complex.norm_exp, mul_comm, Complex.re_ofReal_mul]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hu hz)

private theorem gaussPanelCoefficient_error (b : ℤ) (hb : |(b : ℝ)| ≤ 2) {p k : ℕ}
    (hp : p < 32) (i : Fin 24) :
    ‖(((gauss24Weight i : ℝ) / 32 : ℝ) : ℂ) *
        ((gaussPanelNode p i : ℂ) ^ k / (k.factorial : ℂ)) *
        Complex.exp (gaussPanelNode p i : ℂ) *
        discriminant23ClassCombinationPolynomial (b : ℝ) 80 (gaussPanelHeat p i : ℂ) *
        (Complex.exp ((discriminant23Height29TaylorCenter - 1) * (gaussPanelNode p i : ℂ)) +
          (-1 : ℂ) ^ k * Complex.exp (-discriminant23Height29TaylorCenter * (gaussPanelNode p i : ℂ))) -
      gaussianScaled (gaussPanelCoefficientNumerator b p i k (gaussPanelApproximation p i))
        gaussCoefficientDenominator‖ ≤ ((gauss24Weight i : ℝ) / 32) * (6 / 10 ^ 29) := by
  let u := gaussPanelNode p i
  let w := (gauss24Weight i : ℝ) / 32
  let m : ℂ := (gaussPanelMoment p i k : ℝ)
  let x : ℂ := Complex.exp (u : ℂ)
  let y : ℂ := discriminant23ClassCombinationPolynomial (b : ℝ) 80 (gaussPanelHeat p i : ℂ)
  let a := gaussPanelApproximation p i
  let m' := gaussianScaled ⟨gaussPanelMomentNumerator p i k, 0⟩ gaussMomentScale
  let x' := gaussianScaled ⟨a.expNode, 0⟩ gaussExpScale
  let y' := gaussianScaled (a.principal + (b : GaussianInt) * a.other) gaussExpScale
  let c := discriminant23Height29TaylorCenter
  let z := Complex.exp ((c - 1) * (u : ℂ)) + (-1 : ℂ) ^ k * Complex.exp (-c * (u : ℂ))
  let z' := gaussianScaled (a.plusPhase + (-1 : GaussianInt) ^ k * a.minusPhase) gaussExpScale
  have hw : 0 ≤ w := div_nonneg (gauss24_weight_nonneg i) (by norm_num)
  have hu : 0 ≤ u := gaussPanelNode_nonneg p i
  have hM : ‖m‖ ≤ 64 := by
    dsimp only [m]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gaussPanelMoment_mem hp i k).1]
    exact (gaussPanelMoment_mem hp i k).2
  have hX₀ : 1 ≤ ‖x‖ := by
    dsimp only [x]
    rw [Complex.norm_exp, Complex.ofReal_re]
    exact Real.one_le_exp_iff.mpr hu
  have hX₁ : ‖x‖ ≤ 64 := by
    dsimp only [x]
    rw [Complex.norm_exp, Complex.ofReal_re]
    exact gaussPanelExp_le_sixtyFour hp i
  have hXY : ‖x * y‖ ≤ 12 := by
    have hre : (-1 / 2 : ℝ) ≤ ((u : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith only [hu]
    have him : |((u : ℝ) : ℂ).im| ≤ 1 / 2 := by norm_num
    have h := discriminant23_classCombination_density_norm_le hb hre him
    rw [heatAtNode_eq] at h
    exact h
  have hSign : ‖(-1 : ℂ) ^ k‖ = 1 := by simp
  have hA : ‖Complex.exp ((c - 1) * (u : ℂ))‖ ≤ 1 :=
    exp_norm_le_one (by norm_num [c, discriminant23Height29TaylorCenter, Complex.mul_re]) hu
  have hB : ‖Complex.exp (-c * (u : ℂ))‖ ≤ 1 :=
    exp_norm_le_one (by norm_num [c, discriminant23Height29TaylorCenter, Complex.mul_re]) hu
  have hZ : ‖z‖ ≤ 2 := by
    dsimp only [z]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, hSign, one_mul]
    linarith only [hA, hB]
  have hME : ‖m - m'‖ ≤ (2 / 10 ^ 45 : ℝ) := by
    dsimp only [m, m']
    rw [gaussianScaled_real_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact discriminant23_gaussPanelMoment_error p i k
  have hXE : ‖x - x'‖ ≤ (1 / 10 ^ 47 : ℝ) := by
    dsimp only [x, x']
    rw [← Complex.ofReal_exp, gaussianScaled_real_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact discriminant23_gaussPanelPositiveExp_error hp i
  have hYE : ‖y - y'‖ ≤ (6 / 10 ^ 33 : ℝ) := by
    dsimp only [y, y']
    rw [thetaAtNode_combination, gaussianScaled_add_mul, map_intCast]
    have h := norm_add_mul_error (scale := (b : ℂ))
      (discriminant23_gaussPanelTheta_error true hp i) (discriminant23_gaussPanelTheta_error false hp i)
    have hB' : ‖(b : ℂ)‖ ≤ 2 := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
      exact hb
    have hB'' := mul_le_mul_of_nonneg_right hB' (show (0 : ℝ) ≤ 2 / 10 ^ 33 by positivity)
    exact h.trans (by linarith only [hB''])
  have hZE : ‖z - z'‖ ≤ (2 / 10 ^ 51 : ℝ) := by
    have hFst := discriminant23_gaussPanelExp_error (a := -1) (b := 116)
      (by norm_num) (by norm_num) (by norm_num) hp i
    have hSnd := discriminant23_gaussPanelExp_error (a := -3) (b := -116)
      (by norm_num) (by norm_num) (by norm_num) hp i
    rw [show gaussExpMultiplier (-1) 116 = c - 1 by
      norm_num [gaussExpMultiplier, c, discriminant23Height29TaylorCenter]; ring] at hFst
    rw [show gaussExpMultiplier (-3) (-116) = -c by
      norm_num [gaussExpMultiplier, c, discriminant23Height29TaylorCenter]; ring] at hSnd
    dsimp only [z, z']
    rw [gaussianScaled_add_mul, map_pow, map_neg, map_one]
    exact (norm_add_mul_error hFst hSnd).trans (by rw [hSign]; norm_num)
  have hEq : ((gaussPanelNode p i : ℂ) ^ k / (k.factorial : ℂ)) = m := by
    simp only [m, gaussPanelMoment, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]
  rw [gaussPanelCoefficientNumerator_scaled, hEq]
  change ‖(w : ℂ) * m * x * y * z - (w : ℂ) * m' * x' * y' * z'‖ ≤ _
  rw [show (w : ℂ) * m * x * y * z - (w : ℂ) * m' * x' * y' * z' =
      (w : ℂ) * (m * x * y * z - m' * x' * y' * z') by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (norm_mellin_product_error hM hX₀ hX₁ hXY hZ hME hXE hYE hZE) hw

theorem discriminant23_gaussCoefficient_approximation {b : ℤ} (hb : |(b : ℝ)| ≤ 2) {k : ℕ} :
    ‖discriminant23ClassCombinationTaylorCoeff (b : ℝ) discriminant23Height29TaylorCenter k -
      gaussianScaled (gaussCoefficientNumerator b k) gaussCoefficientDenominator‖ ≤ 2 / 10 ^ 28 := by
  have hGrid : gaussianScaled (gaussCoefficientNumerator b k) gaussCoefficientDenominator =
      ∑ p ∈ classGaussNodes, gaussianScaled
        (gaussPanelCoefficientNumerator b p.1 p.2 k (gaussPanelApproximation p.1 p.2))
        gaussCoefficientDenominator := by
    simp only [gaussCoefficientNumerator, gaussPanelCoefficientSum, classGaussNodes, sum_product,
      gaussianScaled, map_sum, sum_div]
  rw [discriminant23_classCombinationTaylorCoeff_eq_sum, hGrid, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (le_trans
    (b := ∑ p ∈ classGaussNodes, ((gauss24Weight p.2 : ℝ) / 32) * (6 / 10 ^ 29))
    (Finset.sum_le_sum (fun p hp ↦ ?_)) ?_)
  · have hP := Finset.mem_range.mp (Finset.mem_product.mp hp).1
    have h := gaussPanelCoefficient_error (k := k) b hb hP p.2
    simpa only [← heatAtNode_eq, classGaussNode, gaussPanelNode] using h
  · rw [← Finset.sum_mul]
    have hW := gauss24_weight_abs_sum_le
    simp_rw [abs_of_nonneg (gauss24_weight_nonneg _)] at hW
    have hWeightSum : (∑ p ∈ classGaussNodes, (gauss24Weight p.2 : ℝ) / 32) ≤ 3 := by
      calc
        _ = (32 : ℝ) * ((∑ i : Fin 24, (gauss24Weight i : ℝ)) / 32) := by
          rw [classGaussNodes, Finset.sum_product, Finset.sum_div]
          simp
        _ ≤ _ := by linarith only [hW]
    exact (mul_le_mul_of_nonneg_right hWeightSum (by norm_num)).trans (by norm_num)

#print axioms discriminant23_gaussCoefficient_approximation

end
end FieldTarget
