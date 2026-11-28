import GaussianFixedPointProducts
import GaussianFixedPointFast
import Gauss24PanelTable

namespace FieldTarget

open Complex

noncomputable section

set_option exponentiation.threshold 512

def gaussExpScale : ℕ := 2 ^ 192

def gaussPanelNode (p : ℕ) (i : Fin 24) : ℝ :=
  ((2 * (p : ℝ) + 1) + (gauss24Node i : ℝ)) / 16

theorem gaussPanelNode_nonneg (p : ℕ) (i : Fin 24) : 0 ≤ gaussPanelNode p i := by
  have h := (abs_le.mp (gauss24_node_abs_le i)).1
  unfold gaussPanelNode
  linarith only [h, Nat.cast_nonneg (α := ℝ) p]

theorem gaussPanelNode_le_four {p : ℕ} (hp : p < 32) (i : Fin 24) : gaussPanelNode p i ≤ 4 := by
  have h := (abs_le.mp (gauss24_node_abs_le i)).2
  have hP : (p : ℝ) ≤ 31 := by exact_mod_cast (show p ≤ 31 by omega)
  unfold gaussPanelNode
  linarith only [h, hP]

def gaussExpMultiplier (a b : ℤ) : ℂ := ((a : ℂ) + (b : ℂ) * I) / 4

private theorem gaussExpMultiplier_re (a b : ℤ) :
    (gaussExpMultiplier a b).re = (a : ℝ) / 4 := by
  norm_num [gaussExpMultiplier, Complex.div_re, Complex.mul_re]

private def gaussOffset (m : ℤ) : ℝ := ((10 : ℝ) ^ 30 + (m : ℝ)) / (16 * 10 ^ 30)

private def gaussExpInput (a b m : ℤ) : GaussianInt :=
  ⟨a * (10 ^ 30 + m), b * (10 ^ 30 + m)⟩

private def gaussExpInputDenominator : ℕ := 64 * 10 ^ 30

def gaussExpSeed (a b m : ℤ) : GaussianInt :=
  gaussianFixedPointExpFast (gaussExpInput a b m) gaussExpInputDenominator gaussExpScale 3 48

private theorem gaussExpInput_eq (a b m : ℤ) :
    gaussianScaled (gaussExpInput a b m) gaussExpInputDenominator =
      gaussExpMultiplier a b * (gaussOffset m : ℂ) := by
  simp only [gaussianScaled, gaussExpInput, gaussExpInputDenominator, GaussianInt.toComplex_def',
    gaussExpMultiplier, gaussOffset, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  push_cast
  ring

private theorem gaussExpSeed_error {a b m : ℤ} (ha : -4 ≤ a) (ha' : a ≤ -1)
    (hb : |b| ≤ 116) (hm : |m| ≤ (10 : ℤ) ^ 30) :
    ‖Complex.exp (gaussExpMultiplier a b * (gaussOffset m : ℂ)) -
      gaussianScaled (gaussExpSeed a b m) gaussExpScale‖ ≤ 1 / 10 ^ 53 := by
  let z := gaussianScaled (gaussExpInput a b m) gaussExpInputDenominator
  have hZ : z = gaussExpMultiplier a b * (gaussOffset m : ℂ) := gaussExpInput_eq a b m
  have hM : |(m : ℝ)| ≤ (10 : ℝ) ^ 30 := by exact_mod_cast hm
  have hU₀ : 0 ≤ gaussOffset m := by
    unfold gaussOffset
    exact div_nonneg (by linarith only [(abs_le.mp hM).1]) (by positivity)
  have hU₁ : gaussOffset m ≤ 1 / 8 := by
    unfold gaussOffset
    apply (div_le_iff₀ (by positivity)).2
    linarith only [(abs_le.mp hM).2]
  have hA₀ : (-4 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have hA₁ : (a : ℝ) ≤ -1 := by exact_mod_cast ha'
  have hB : |(b : ℝ)| ≤ 116 := by exact_mod_cast hb
  have hRe : z.re ≤ 0 := by
    rw [hZ, mul_comm, Complex.re_ofReal_mul, gaussExpMultiplier_re]
    exact mul_nonpos_of_nonneg_of_nonpos hU₀ (by linarith only [hA₁])
  have hNorm : ‖gaussExpMultiplier a b‖ ≤ 30 := by
    have hA : |(a : ℝ)| ≤ 4 := abs_le.mpr ⟨hA₀, by linarith only [hA₁]⟩
    have h := norm_add_le (a : ℂ) ((b : ℂ) * I)
    rw [norm_mul, Complex.norm_I, mul_one] at h
    have hCast (n : ℤ) : ‖(n : ℂ)‖ = |(n : ℝ)| := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    rw [hCast, hCast] at h
    rw [gaussExpMultiplier, norm_div]
    norm_num
    linarith only [h, hA, hB]
  have hShift : gaussianScaled (gaussExpInput a b m) (gaussExpInputDenominator * 2 ^ 3) =
      z / (2 : ℂ) ^ 3 := by
    simp only [z, gaussianScaled, div_div, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hSmall : ‖gaussianScaled (gaussExpInput a b m) (gaussExpInputDenominator * 2 ^ 3)‖ ≤ 1 / 2 := by
    rw [hShift, hZ, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hU₀]
    have h := mul_le_mul hNorm hU₁ hU₀ (by norm_num)
    norm_num [norm_pow] at h ⊢
    linarith only [h]
  have h := norm_exp_sub_gaussianFixedPointExp (gaussExpInput a b m) (s := gaussExpScale)
    (by norm_num [gaussExpInputDenominator]) (by norm_num [gaussExpScale])
    3 48 hRe hSmall (by norm_num [Nat.factorial, gaussExpScale])
  rw [← gaussianFixedPointExpFast_eq] at h
  rw [← hZ]
  exact h.trans (by norm_num [Nat.factorial, gaussExpScale])

private theorem gaussNodeNumerator_abs_le : ∀ i : Fin 24, |(gauss24Pair i).1| ≤ (10 : ℤ) ^ 30 := by
  decide +kernel

private theorem gaussOffset_eq (i : Fin 24) :
    gaussOffset (gauss24Pair i).1 = gaussPanelNode 0 i := by
  unfold gaussOffset gaussPanelNode gauss24Node
  push_cast
  norm_num [gauss24Denominator]
  ring

def gaussPanelExpNumerator (a b : ℤ) (p : ℕ) (i : Fin 24) : GaussianInt :=
  gaussianFixedPointProducts (gaussExpSeed a b (10 ^ 30)) (gaussExpSeed a b (gauss24Pair i).1) gaussExpScale p

private theorem gaussPanelExp_error_unbounded {a b : ℤ} (ha : -4 ≤ a) (ha' : a ≤ -1)
    (hb : |b| ≤ 116) (p : ℕ) (i : Fin 24) :
    ‖Complex.exp (gaussExpMultiplier a b * (gaussPanelNode p i : ℂ)) -
      gaussianScaled (gaussPanelExpNumerator a b p i) gaussExpScale‖ ≤
      1 / 10 ^ 53 + (p : ℝ) * (1 / 10 ^ 53 + 2 / (gaussExpScale : ℝ)) := by
  let v := gaussExpMultiplier a b
  let step := Complex.exp (v * ((1 / 8 : ℝ) : ℂ))
  let start := Complex.exp (v * (gaussPanelNode 0 i : ℂ))
  have hA : (a : ℝ) ≤ -1 := by exact_mod_cast ha'
  have hRe : v.re = (a : ℝ) / 4 := gaussExpMultiplier_re a b
  have hStartNorm : ‖start‖ ≤ 1 := by
    dsimp only [start]
    rw [Complex.norm_exp, mul_comm, Complex.re_ofReal_mul, hRe]
    exact Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonneg_of_nonpos (gaussPanelNode_nonneg 0 i) (by linarith only [hA]))
  have hStepTight : ‖step‖ ≤ (32 / 33 : ℝ) := by
    dsimp only [step]
    rw [Complex.norm_exp, mul_comm, Complex.re_ofReal_mul, hRe]
    calc
      _ ≤ Real.exp (- (1 / 32 : ℝ)) := Real.exp_le_exp.mpr (by linarith only [hA])
      _ ≤ _ := by
        rw [Real.exp_neg, ← one_div, show (32 / 33 : ℝ) = 1 / (33 / 32) by norm_num]
        exact one_div_le_one_div_of_le (by norm_num)
          (by linarith only [Real.add_one_le_exp (1 / 32)])
  have hStart := gaussExpSeed_error ha ha' hb (gaussNodeNumerator_abs_le i)
  rw [gaussOffset_eq] at hStart
  have hStep := gaussExpSeed_error ha ha' hb (m := (10 : ℤ) ^ 30) (by norm_num)
  rw [show gaussOffset ((10 : ℤ) ^ 30) = 1 / 8 by norm_num [gaussOffset]] at hStep
  have hStepNorm : ‖gaussianScaled (gaussExpSeed a b (10 ^ 30)) gaussExpScale‖ ≤ 1 := by
    have h := norm_le_norm_sub_add (gaussianScaled (gaussExpSeed a b (10 ^ 30)) gaussExpScale) step
    rw [norm_sub_rev] at h
    exact h.trans ((add_le_add hStep hStepTight).trans (by norm_num))
  have hInput : Complex.exp (v * (gaussPanelNode p i : ℂ)) = step ^ p * start := by
    have h : v * (gaussPanelNode p i : ℂ) =
        (p : ℂ) * (v * ((1 / 8 : ℝ) : ℂ)) + v * (gaussPanelNode 0 i : ℂ) := by
      unfold gaussPanelNode
      push_cast
      ring
    rw [h, Complex.exp_add, Complex.exp_nat_mul]
  rw [hInput]
  exact norm_gaussianFixedPointProducts_error (s := gaussExpScale)
    (by norm_num [gaussExpScale]) (hStepTight.trans (by norm_num)) hStartNorm hStepNorm hStart hStep p

/-- A uniform enclosure for both Mellin phases and the real exponential on all 32 panels. -/
theorem discriminant23_gaussPanelExp_error {a b : ℤ} (ha : -4 ≤ a) (ha' : a ≤ -1)
    (hb : |b| ≤ 116) {p : ℕ} (hp : p < 32) (i : Fin 24) :
    ‖Complex.exp (gaussExpMultiplier a b * (gaussPanelNode p i : ℂ)) -
      gaussianScaled (gaussPanelExpNumerator a b p i) gaussExpScale‖ ≤ 1 / 10 ^ 51 := by
  have hP : (p : ℝ) ≤ 31 := by exact_mod_cast (show p ≤ 31 by omega)
  refine (gaussPanelExp_error_unbounded ha ha' hb p i).trans ?_
  have h := mul_le_mul_of_nonneg_right hP
    (show (0 : ℝ) ≤ 1 / 10 ^ 53 + 2 / (gaussExpScale : ℝ) by positivity)
  norm_num [gaussExpScale] at h ⊢
  linarith only [h]

#print axioms gaussPanelNode_le_four
#print axioms discriminant23_gaussPanelExp_error

end
end FieldTarget
