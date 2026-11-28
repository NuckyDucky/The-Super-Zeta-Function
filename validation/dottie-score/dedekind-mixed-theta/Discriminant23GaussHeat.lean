import Discriminant23GaussExponentials
import Discriminant23ThetaScaleDyadic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace FieldTarget

open Complex

noncomputable section

set_option exponentiation.threshold 512

def gaussExpGrid (n : ℤ) : ℝ := (n : ℝ) / (gaussExpScale : ℝ)

theorem gaussianScaled_re_eq (z : GaussianInt) (s : ℕ) :
    (gaussianScaled z s).re = (z.re : ℝ) / (s : ℝ) := by
  rw [gaussianScaled, ← Complex.ofReal_natCast, Complex.div_ofReal_re, GaussianInt.toComplex_def₂]

private def inverseExpNumerator (p : ℕ) (i : Fin 24) : ℤ :=
  (gaussPanelExpNumerator (-4) 0 p i).re

private theorem inverseExp_error {p : ℕ} (hp : p < 32) (i : Fin 24) :
    |Real.exp (-gaussPanelNode p i) - gaussExpGrid (inverseExpNumerator p i)| ≤ 1 / 10 ^ 51 := by
  have h := (Complex.abs_re_le_norm _).trans
    (discriminant23_gaussPanelExp_error (a := -4) (b := 0) (by norm_num) (by norm_num) (by norm_num) hp i)
  have hv : gaussExpMultiplier (-4) 0 = -1 := by norm_num [gaussExpMultiplier]
  simpa only [hv, neg_one_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.sub_re,
    gaussianScaled_re_eq, Complex.ofReal_re, gaussExpGrid, inverseExpNumerator] using h

theorem gaussPanelExp_le_sixtyFour {p : ℕ} (hp : p < 32) (i : Fin 24) :
    Real.exp (gaussPanelNode p i) ≤ 64 := by
  have h : Real.exp (4 : ℝ) = Real.exp 1 ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
  calc
    _ ≤ Real.exp 4 := Real.exp_le_exp.mpr (gaussPanelNode_le_four hp i)
    _ = _ := h
    _ ≤ (11 / 4 : ℝ) ^ 4 := pow_le_pow_left₀ (Real.exp_nonneg _) (by linarith only [Real.exp_one_lt_d9]) _
    _ ≤ _ := by norm_num

def gaussPanelPositiveExpNumerator (p : ℕ) (i : Fin 24) : ℤ :=
  (gaussExpScale : ℤ) * (gaussExpScale : ℤ) / (inverseExpNumerator p i).natAbs

theorem gaussPanelPositiveExpNumerator_eq (p : ℕ) (i : Fin 24) :
    gaussPanelPositiveExpNumerator p i =
      (gaussExpScale : ℤ) * (gaussExpScale : ℤ) /
        (gaussPanelExpNumerator (-4) 0 p i).re.natAbs := rfl

/-- The reciprocal formula uses a single integer division, on the same dyadic grid. -/
theorem discriminant23_gaussPanelPositiveExp_error {p : ℕ} (hp : p < 32) (i : Fin 24) :
    |Real.exp (gaussPanelNode p i) - gaussExpGrid (gaussPanelPositiveExpNumerator p i)| ≤
      1 / 10 ^ 47 := by
  let e := Real.exp (-gaussPanelNode p i)
  let n := inverseExpNumerator p i
  let r := gaussExpGrid n
  have hErr : |e - r| ≤ (1 / 10 ^ 51 : ℝ) := inverseExp_error hp i
  have hE : (1 / 64 : ℝ) ≤ e := by
    dsimp only [e]
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le (Real.exp_pos _) (gaussPanelExp_le_sixtyFour hp i)
  have hR : (1 / 128 : ℝ) ≤ r := by
    have h := (abs_le.mp hErr).2
    linarith only [h, hE]
  have hpE : 0 < e := lt_of_lt_of_le (by norm_num) hE
  have hpR : 0 < r := lt_of_lt_of_le (by norm_num) hR
  have hS : (0 : ℝ) < (gaussExpScale : ℝ) := by norm_num [gaussExpScale]
  have hn : 0 < n := by exact_mod_cast ((div_pos_iff_of_pos_right hS).mp hpR)
  have hRecip : Real.exp (gaussPanelNode p i) = 1 / e := by
    simp only [e, Real.exp_neg, one_div, inv_inv]
  have hExact : (Real.exp (gaussPanelNode p i) - 1 / r) * (e * r) = r - e := by
    rw [hRecip]
    field_simp [hpE.ne', hpR.ne']
  have hFraction : |Real.exp (gaussPanelNode p i) - 1 / r| ≤ (8192 / 10 ^ 51 : ℝ) := by
    have h := hErr
    rw [abs_sub_comm e r, ← hExact, abs_mul, abs_of_pos (mul_pos hpE hpR)] at h
    have hLower : (1 / 8192 : ℝ) ≤ e * r := by
      convert mul_le_mul hE hR (by norm_num) hpE.le using 1
      norm_num
    have h' := (mul_le_mul_of_nonneg_left hLower (abs_nonneg _)).trans h
    linarith only [h']
  let a : GaussianInt := ⟨(gaussExpScale : ℤ) * (gaussExpScale : ℤ), 0⟩
  let d : ℕ := n.natAbs
  have hD : 0 < d := Int.natAbs_pos.mpr hn.ne'
  have hDint : (d : ℤ) = n := Int.natAbs_of_nonneg hn.le
  have hDcast : (d : ℝ) = (n : ℝ) := by
    rw [← Int.cast_natCast, hDint]
  have hFloor := (Complex.abs_re_le_norm _).trans
    (norm_gaussianFloorDiv_error a (s := gaussExpScale) hD (by norm_num [gaussExpScale]))
  rw [Complex.sub_re, gaussianScaled_re_eq, gaussianScaled_re_eq, Nat.cast_mul] at hFloor
  have hOne : (a.re : ℝ) / ((gaussExpScale : ℝ) * (d : ℝ)) = 1 / r := by
    change (((gaussExpScale : ℤ) * (gaussExpScale : ℤ) : ℤ) : ℝ) /
      ((gaussExpScale : ℝ) * (d : ℝ)) = 1 / ((n : ℝ) / (gaussExpScale : ℝ))
    rw [hDcast]
    push_cast
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hn', hS.ne']
  rw [hOne] at hFloor
  have hRound : |1 / r - gaussExpGrid (gaussPanelPositiveExpNumerator p i)| ≤
      2 / (gaussExpScale : ℝ) := hFloor
  calc
    _ ≤ |Real.exp (gaussPanelNode p i) - 1 / r| +
        |1 / r - gaussExpGrid (gaussPanelPositiveExpNumerator p i)| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (Real.exp (gaussPanelNode p i) - 1 / r)
          (1 / r - gaussExpGrid (gaussPanelPositiveExpNumerator p i))
    _ ≤ _ := (add_le_add hFraction hRound).trans (by norm_num [gaussExpScale])

private theorem abs_exp_sub_exp_le_of_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  have ordered {a b : ℝ} (h : a ≤ b) (hb : b ≤ 0) : Real.exp b - Real.exp a ≤ b - a := by
    have hEq : Real.exp a = Real.exp b * Real.exp (a - b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hDiff : 0 ≤ 1 - Real.exp (a - b) :=
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (sub_nonpos.mpr h))
    rw [hEq, ← mul_one_sub]
    calc
      _ ≤ 1 - Real.exp (a - b) := mul_le_of_le_one_left hDiff (Real.exp_le_one_iff.mpr hb)
      _ ≤ _ := by linarith only [Real.add_one_le_exp (a - b)]
  rcases le_total x y with h | h
  · rw [abs_sub_comm (Real.exp x) (Real.exp y), abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered h hy
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr h)), abs_of_nonneg (sub_nonneg.mpr h)]
    exact ordered h hx

private def thetaScaleNumerator : ℕ := 445815737633141664182226312842035173730
private def thetaScaleDenominator : ℕ := 2 ^ 128

private def thetaScaleApprox : ℝ := (thetaScaleNumerator : ℝ) / (thetaScaleDenominator : ℝ)

private theorem thetaScaleApprox_le : thetaScaleApprox ≤ discriminant23ThetaScale := by
  simpa only [thetaScaleApprox, thetaScaleNumerator, thetaScaleDenominator, Nat.cast_ofNat, Nat.cast_pow]
    using discriminant23_thetaScale_dyadic_128.1

private theorem thetaScale_error :
    |discriminant23ThetaScale - thetaScaleApprox| ≤ 1 / 2 ^ 128 := by
  have hHi := discriminant23_thetaScale_dyadic_128.2
  rw [abs_of_nonneg (sub_nonneg.mpr thetaScaleApprox_le)]
  norm_num [thetaScaleApprox, thetaScaleNumerator, thetaScaleDenominator] at hHi ⊢
  linarith only [hHi]

private def heatExpArgument (p : ℕ) (i : Fin 24) : GaussianInt :=
  ⟨-(thetaScaleNumerator : ℤ) * gaussPanelPositiveExpNumerator p i, 0⟩

private def heatExpDenominator : ℕ := thetaScaleDenominator * gaussExpScale

def gaussPanelHeatNumerator (p : ℕ) (i : Fin 24) : ℤ :=
  (gaussianFixedPointExp (heatExpArgument p i) heatExpDenominator gaussExpScale 9 48).re

def gaussHeatOfPositiveExp (e : ℤ) : ℤ :=
  intFixedPointExp (-(thetaScaleNumerator : ℤ) * e) heatExpDenominator gaussExpScale 9 48

theorem gaussPanelHeatNumerator_eq (p : ℕ) (i : Fin 24) :
    gaussPanelHeatNumerator p i = gaussHeatOfPositiveExp (gaussPanelPositiveExpNumerator p i) := by
  rw [gaussPanelHeatNumerator, heatExpArgument, gaussianFixedPointExp_real_eq]
  rfl

private theorem heatExpArgument_eq (p : ℕ) (i : Fin 24) :
    gaussianScaled (heatExpArgument p i) heatExpDenominator =
      ((-thetaScaleApprox * gaussExpGrid (gaussPanelPositiveExpNumerator p i) : ℝ) : ℂ) := by
  simp only [gaussianScaled, heatExpArgument, heatExpDenominator, GaussianInt.toComplex_def',
    thetaScaleApprox, gaussExpGrid]
  push_cast
  ring

/-- Every heat value used by the finite theta polynomial has an integer evaluator and a common error. -/
theorem discriminant23_gaussPanelHeat_error {p : ℕ} (hp : p < 32) (i : Fin 24) :
    |Real.exp (-discriminant23ThetaScale * Real.exp (gaussPanelNode p i)) -
      gaussExpGrid (gaussPanelHeatNumerator p i)| ≤ 3 / 10 ^ 37 := by
  let E := Real.exp (gaussPanelNode p i)
  let v := gaussExpGrid (gaussPanelPositiveExpNumerator p i)
  have hEV : |E - v| ≤ (1 / 10 ^ 47 : ℝ) := discriminant23_gaussPanelPositiveExp_error hp i
  have hE : 1 ≤ E := Real.one_le_exp_iff.mpr (gaussPanelNode_nonneg p i)
  have hE' : E ≤ 64 := gaussPanelExp_le_sixtyFour hp i
  have hv : 0 ≤ v := by linarith only [(abs_le.mp hEV).2, hE]
  have hv' : v ≤ 65 := by linarith only [(abs_le.mp hEV).1, hE']
  have hScale : 0 ≤ thetaScaleApprox := by unfold thetaScaleApprox; positivity
  have hScale' : thetaScaleApprox ≤ 2 := by norm_num [thetaScaleApprox, thetaScaleNumerator, thetaScaleDenominator]
  have hScaleExact : 0 ≤ discriminant23ThetaScale := hScale.trans thetaScaleApprox_le
  let z := -thetaScaleApprox * v
  have hz : z ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hScale) hv
  have hz' : -130 ≤ z := by
    have h := mul_le_mul hScale' hv' hv (by norm_num : (0 : ℝ) ≤ 2)
    dsimp only [z]
    linarith only [h]
  have hArg : gaussianScaled (heatExpArgument p i) heatExpDenominator = (z : ℂ) := heatExpArgument_eq p i
  have hSmall : ‖gaussianScaled (heatExpArgument p i) (heatExpDenominator * 2 ^ 9)‖ ≤ 1 / 2 := by
    have h : gaussianScaled (heatExpArgument p i) (heatExpDenominator * 2 ^ 9) =
        gaussianScaled (heatExpArgument p i) heatExpDenominator / (2 : ℂ) ^ 9 := by
      simp only [gaussianScaled, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, div_div]
    rw [h, hArg, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hz]
    norm_num
    linarith only [hz']
  have hNumerical := norm_exp_sub_gaussianFixedPointExp (heatExpArgument p i) (s := gaussExpScale)
    (by norm_num [heatExpDenominator, thetaScaleDenominator, gaussExpScale])
    (by norm_num [gaussExpScale]) 9 48
    (by rw [hArg, Complex.ofReal_re]; exact hz) hSmall (by norm_num [Nat.factorial, gaussExpScale])
  rw [hArg, ← Complex.ofReal_exp] at hNumerical
  have hRound : |Real.exp z - gaussExpGrid (gaussPanelHeatNumerator p i)| ≤ (1 / 10 ^ 50 : ℝ) := by
    have h := (Complex.abs_re_le_norm _).trans hNumerical
    rw [Complex.sub_re, Complex.ofReal_re, gaussianScaled_re_eq] at h
    exact h.trans (by norm_num [Nat.factorial, gaussExpScale])
  have hTheta : |(-discriminant23ThetaScale * E) - z| ≤ (2 / 10 ^ 37 : ℝ) := by
    have h : (-discriminant23ThetaScale * E) - z =
        -((discriminant23ThetaScale - thetaScaleApprox) * E + thetaScaleApprox * (E - v)) := by
      dsimp only [z]
      ring
    rw [h, abs_neg]
    calc
      _ ≤ |(discriminant23ThetaScale - thetaScaleApprox) * E| +
          |thetaScaleApprox * (E - v)| := abs_add_le _ _
      _ = |discriminant23ThetaScale - thetaScaleApprox| * E + thetaScaleApprox * |E - v| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.exp_nonneg _), abs_of_nonneg hScale]
      _ ≤ 1 / 2 ^ 128 * 64 + 2 * (1 / 10 ^ 47) := add_le_add
        (mul_le_mul thetaScale_error hE' (Real.exp_nonneg _) (by norm_num))
        (mul_le_mul hScale' hEV (abs_nonneg _) (by norm_num))
      _ ≤ _ := by norm_num
  have hExp := (abs_exp_sub_exp_le_of_nonpos
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hScaleExact) (Real.exp_nonneg _)) hz).trans hTheta
  calc
    _ ≤ |Real.exp (-discriminant23ThetaScale * E) - Real.exp z| +
        |Real.exp z - gaussExpGrid (gaussPanelHeatNumerator p i)| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le (Real.exp (-discriminant23ThetaScale * E) - Real.exp z)
          (Real.exp z - gaussExpGrid (gaussPanelHeatNumerator p i))
    _ ≤ _ := (add_le_add hExp hRound).trans (by norm_num)

#print axioms discriminant23_gaussPanelPositiveExp_error
#print axioms discriminant23_gaussPanelHeat_error

end
end FieldTarget
