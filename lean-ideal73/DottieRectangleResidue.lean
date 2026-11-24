import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The finite rectangular contour shift across the pole at zero. -/

open Complex MeasureTheory Set
open scoped Topology

namespace QuarticModel

private noncomputable def rectPoint (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

private noncomputable def rectangleBoundary (a b H : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x in a..b, f (rectPoint x (-H))) - (∫ x in a..b, f (rectPoint x H)) +
    I * ((∫ y in -H..H, f (rectPoint b y)) - (∫ y in -H..H, f (rectPoint a y)))

private theorem lineIntegral_log {p q : ℂ} {a b : ℝ}
    (h : ∀ t ∈ uIcc a b, p + (t : ℂ) * q ∈ slitPlane) :
    (∫ t in a..b, q / (p + (t : ℂ) * q)) =
      log (p + (b : ℂ) * q) - log (p + (a : ℂ) * q) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    have hcast : HasDerivAt (fun u : ℝ => (u : ℂ)) (1 : ℂ) t := by
      simpa only [id_eq, ofReal_one] using (hasDerivAt_id t).ofReal_comp
    have hline : HasDerivAt (fun u : ℝ => p + (u : ℂ) * q) q t := by
      simpa only [one_mul] using (hcast.mul_const q).const_add p
    exact hline.clog_real (h t ht)
  · have hcont : Continuous (fun t : ℝ => p + (t : ℂ) * q) := by fun_prop
    exact (continuousOn_const.div hcont.continuousOn fun t ht =>
      slitPlane_ne_zero (h t ht)).intervalIntegrable

private theorem integral_reciprocal_horizontal {y : ℝ} (hy : y ≠ 0) (a b : ℝ) :
    (∫ x in a..b, 1 / rectPoint x y) = log (rectPoint b y) - log (rectPoint a y) := by
  have h := lineIntegral_log (p := (y : ℂ) * I) (q := 1) (a := a) (b := b)
    (fun x _ => mem_slitPlane_iff.mpr (Or.inr (by simpa using hy)))
  simpa only [rectPoint, mul_one, add_comm] using h

private theorem integral_reciprocal_vertical_pos {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    I * (∫ y in a..b, 1 / rectPoint x y) = log (rectPoint x b) - log (rectPoint x a) := by
  have h := lineIntegral_log (p := (x : ℂ)) (q := I) (a := a) (b := b)
    (fun y _ => mem_slitPlane_iff.mpr (Or.inl (by simpa using hx)))
  simpa only [rectPoint, div_eq_mul_inv, one_mul, intervalIntegral.integral_const_mul] using h

private theorem integral_reciprocal_vertical_neg {x : ℝ} (hx : x < 0) (a b : ℝ) :
    I * (∫ y in a..b, 1 / rectPoint x y) =
      log (-rectPoint x b) - log (-rectPoint x a) := by
  have h := lineIntegral_log (p := -(x : ℂ)) (q := -I) (a := a) (b := b)
    (fun y _ => mem_slitPlane_iff.mpr (Or.inl (by simpa using neg_pos.mpr hx)))
  have he (y : ℝ) : -(x : ℂ) + (y : ℂ) * (-I) = -rectPoint x y := by
    unfold rectPoint
    ring
  simp only [he, neg_div_neg_eq] at h
  simpa only [div_eq_mul_inv, one_mul, intervalIntegral.integral_const_mul] using h

private theorem log_sub_log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

private theorem log_sub_log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    log z - log (-z) = -(Real.pi : ℂ) * I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_add_pi_of_im_neg hz]

private theorem rectangle_reciprocal_boundary {a b H : ℝ}
    (ha : a < 0) (hb : 0 < b) (hH : 0 < H) :
    rectangleBoundary a b H (fun z => 1 / z) = 2 * (Real.pi : ℂ) * I := by
  have hBottom := integral_reciprocal_horizontal (neg_ne_zero.mpr hH.ne') a b
  have hTop := integral_reciprocal_horizontal hH.ne' a b
  have hRight := integral_reciprocal_vertical_pos hb (-H) H
  have hLeft := integral_reciprocal_vertical_neg ha (-H) H
  have hTopLeft := log_sub_log_neg_of_im_pos (z := rectPoint a H) (by simpa [rectPoint] using hH)
  have hBottomLeft := log_sub_log_neg_of_im_neg (z := rectPoint a (-H))
    (by simpa [rectPoint] using neg_neg_of_pos hH)
  unfold rectangleBoundary
  rw [hBottom, hTop, mul_sub, hRight, hLeft]
  linear_combination hTopLeft - hBottomLeft

private theorem integral_div_eq_dslope_add {F : ℂ → ℂ} {U : Set ℂ}
    (hd : ContinuousOn (dslope F 0) U) {p : ℝ → ℂ} (hp : Continuous p) {a b : ℝ}
    (hmap : MapsTo p (uIcc a b) U) (hne : ∀ t ∈ uIcc a b, p t ≠ 0) :
    (∫ t in a..b, F (p t) / p t) =
      (∫ t in a..b, dslope F 0 (p t)) + F 0 * (∫ t in a..b, 1 / p t) := by
  have hi : IntervalIntegrable (fun t => dslope F 0 (p t)) volume a b :=
    (hd.comp hp.continuousOn hmap).intervalIntegrable
  have hj : IntervalIntegrable (fun t => F 0 * (1 / p t)) volume a b :=
    (continuousOn_const.mul (continuousOn_const.div hp.continuousOn hne)).intervalIntegrable
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi hj]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [dslope_of_ne _ (hne t ht), slope_def_field, sub_zero]
  simp only [div_eq_mul_inv, one_mul]
  ring

/-- Across zero inside a finite rectangle, the upward right-minus-left
    integral equals `I` times the bottom-minus-top integral, plus `2π F(0)`. -/
theorem rectangular_div_residue_at_zero {F : ℂ → ℂ} {U : Set ℂ} {a b H : ℝ}
    (ha : a < 0) (hb : 0 < b) (hH : 0 < H) (hU : IsOpen U)
    (hrect : Complex.reProdIm (Icc a b) (Icc (-H) H) ⊆ U)
    (hF : DifferentiableOn ℂ F U) :
    (∫ y in -H..H, F ((b : ℂ) + (y : ℂ) * I) / ((b : ℂ) + (y : ℂ) * I)) -
      (∫ y in -H..H, F ((a : ℂ) + (y : ℂ) * I) / ((a : ℂ) + (y : ℂ) * I)) =
        I * ((∫ x in a..b, F ((x : ℂ) + ((-H : ℝ) : ℂ) * I) /
          ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) -
        (∫ x in a..b, F ((x : ℂ) + (H : ℂ) * I) / ((x : ℂ) + (H : ℂ) * I))) +
          2 * (Real.pi : ℂ) * F 0 := by
  have hab := ha.le.trans hb.le
  have hHH : -H ≤ H := by linarith
  have h0 : (0 : ℂ) ∈ U := hrect (Complex.mem_reProdIm.mpr ⟨
    ⟨by simpa using ha.le, by simpa using hb.le⟩,
    ⟨by simpa using neg_nonpos.mpr hH.le, by simpa using hH.le⟩⟩)
  have hd : DifferentiableOn ℂ (dslope F 0) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds h0)).mpr hF
  have hdslope : rectangleBoundary a b H (dslope F 0) = 0 := by
    have hD : DifferentiableOn ℂ (dslope F 0) (Complex.reProdIm (uIcc a b) (uIcc (-H) H)) := by
      rw [uIcc_of_le hab, uIcc_of_le hHH]
      exact hd.mono hrect
    have he := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (dslope F 0)
      ⟨a, -H⟩ ⟨b, H⟩ hD
    simpa only [rectangleBoundary, rectPoint, smul_eq_mul, mul_sub, ← add_sub_assoc] using he
  have hVert (x : ℝ) (hx : x ∈ Icc a b) (hx0 : x ≠ 0) :=
    integral_div_eq_dslope_add hd.continuousOn (p := rectPoint x) (a := -H) (b := H)
      (by unfold rectPoint; fun_prop)
      (fun y hy => hrect (Complex.mem_reProdIm.mpr ⟨by simpa [rectPoint] using hx,
        by simpa [rectPoint, uIcc_of_le hHH] using hy⟩))
      (fun y _ he => hx0 (by simpa [rectPoint] using congrArg Complex.re he))
  have hHoriz (y : ℝ) (hy : y ∈ Icc (-H) H) (hy0 : y ≠ 0) :=
    integral_div_eq_dslope_add hd.continuousOn (p := fun x => rectPoint x y) (a := a) (b := b)
      (by unfold rectPoint; fun_prop)
      (fun x hx => hrect (Complex.mem_reProdIm.mpr ⟨by simpa [rectPoint, uIcc_of_le hab] using hx,
        by simpa [rectPoint] using hy⟩))
      (fun x _ he => hy0 (by simpa [rectPoint] using congrArg Complex.im he))
  have hsplit : rectangleBoundary a b H (fun z => F z / z) =
      rectangleBoundary a b H (dslope F 0) + F 0 * rectangleBoundary a b H (fun z => 1 / z) := by
    unfold rectangleBoundary
    rw [hHoriz (-H) ⟨le_rfl, hHH⟩ (neg_ne_zero.mpr hH.ne'), hHoriz H ⟨hHH, le_rfl⟩ hH.ne',
      hVert b ⟨hab, le_rfl⟩ hb.ne', hVert a ⟨le_rfl, hab⟩ ha.ne]
    ring
  have he : rectangleBoundary a b H (fun z => F z / z) = I * (2 * (Real.pi : ℂ) * F 0) := by
    rw [hsplit, hdslope, rectangle_reciprocal_boundary ha hb hH]
    ring
  have rotate {V A R : ℂ} (h : A + I * V = I * R) : V = I * A + R := by
    linear_combination (-I) * h + (V - R) * Complex.I_sq
  exact rotate (by simpa only [rectangleBoundary, rectPoint] using he)

/-- Finite Dottie contour shift from the line at one to the line at minus seven. -/
theorem dottie_rectangle_residue {F : ℂ → ℂ} {U : Set ℂ} {H : ℝ}
    (hH : 0 < H) (hU : IsOpen U)
    (hrect : Complex.reProdIm (Icc (-7 : ℝ) 1) (Icc (-H) H) ⊆ U)
    (hF : DifferentiableOn ℂ F U) :
    (∫ y in -H..H, F (1 + (y : ℂ) * I) / (1 + (y : ℂ) * I)) -
      (∫ y in -H..H, F (-7 + (y : ℂ) * I) / (-7 + (y : ℂ) * I)) =
        I * ((∫ x in (-7 : ℝ)..1, F ((x : ℂ) + ((-H : ℝ) : ℂ) * I) /
          ((x : ℂ) + ((-H : ℝ) : ℂ) * I)) -
        (∫ x in (-7 : ℝ)..1, F ((x : ℂ) + (H : ℂ) * I) / ((x : ℂ) + (H : ℂ) * I))) +
          2 * (Real.pi : ℂ) * F 0 := by
  simpa only [ofReal_one, ofReal_neg, ofReal_ofNat] using
    rectangular_div_residue_at_zero (a := -7) (b := 1) (by norm_num) (by norm_num) hH hU hrect hF

#print axioms rectangular_div_residue_at_zero
#print axioms dottie_rectangle_residue

end QuarticModel
