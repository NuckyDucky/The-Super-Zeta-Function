import DottieDyadicGeometry
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith

namespace FieldTarget

open Complex SuperZeta.StirlingCorrection

/-- A pole term of residue scale `3/2`, a regular factor, and a squared
factor with small phase give a strict sign on the first measuring disk. -/
theorem re_completed_class_product_le {w A C : ℂ}
    (hhalf : 1 / 2 ≤ w.re) (hone : w.re < 1)
    (hdisk : ‖w - (3 / 4 : ℂ)‖ ≤ 1 / 4)
    (hregular : ‖A‖ ≤ 4 / 5) (hcusp : 1 / 8 ≤ C.re)
    (hphase : |C.im| ≤ |w.im| * (w.re - 1 / 2) / 4) :
    ((A - (3 / 2 : ℂ) / (w * (1 - w))) * C ^ 2).re ≤ -(1 / 400 : ℝ) := by
  let x : ℝ := w.re - 1 / 2
  let y : ℝ := |w.im|
  let z : ℂ := w * (1 - w)
  let a : ℝ := z.re
  let b : ℝ := z.im
  let u : ℝ := C.re
  let v : ℝ := C.im
  have hx0 : 0 ≤ x := sub_nonneg.mpr hhalf
  have hx1 : x ≤ 1 / 2 := by dsimp [x]; linarith only [hone]
  have hy0 : 0 ≤ y := abs_nonneg _
  have hySq : y ^ 2 = w.im ^ 2 := sq_abs _
  have hdgeom : (w.re - 3 / 4) ^ 2 + y ^ 2 ≤ 1 / 16 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hdisk 2
    have hcR : ((3 / 4 : ℂ)).re = 3 / 4 := by norm_num [Complex.div_re]
    have hcI : ((3 / 4 : ℂ)).im = 0 := by norm_num [Complex.div_im]
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hcR, hcI,
      sub_zero] at h
    rw [hySq]
    linarith only [h]
  have hySqBound : y ^ 2 ≤ 1 / 16 := by nlinarith only [hdgeom, sq_nonneg (w.re - 3 / 4)]
  have hy1 : y ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 4)]
  have hxSq : x ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ hx0 hx1 2
    nlinarith only [h]
  have ht : y ^ 2 ≤ (1 - w.re) * x := by
    dsimp [x]
    nlinarith only [hdgeom]
  have ha : a = w.re * (1 - w.re) + y ^ 2 := by
    dsimp [a, z]
    rw [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, hySq]
    ring
  have ha' : a = 1 / 4 - x ^ 2 + y ^ 2 := by dsimp [x]; linarith only [ha]
  have hapos : 0 < a := by
    rw [ha]
    exact add_pos_of_pos_of_nonneg (mul_pos (by linarith only [hhalf]) (sub_pos.mpr hone)) (sq_nonneg _)
  have hty : y ^ 2 ≤ a / 3 := by
    have hxle : x ≤ w.re / 2 := by dsimp [x]; linarith only [hone]
    have hmul := mul_le_mul_of_nonneg_left hxle (sub_nonneg.mpr hone.le)
    nlinarith only [ht, ha, hmul]
  have hb : b = -(2 * x) * w.im := by
    dsimp [b, z, x]
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hbAbs : |b| = 2 * y * x := by
    rw [hb, abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * x)]
    dsimp [y]
    ring
  have hbSq : b ^ 2 = 4 * x ^ 2 * y ^ 2 := by
    rw [← sq_abs b, hbAbs]
    ring
  have hzpos : 0 < Complex.normSq z := by
    apply Complex.normSq_pos.mpr
    intro hz
    have : a = 0 := by simp [a, hz]
    exact hapos.ne' this
  have hzBound : Complex.normSq z ≤ (19 / 48) * a := by
    have hbBound : b ^ 2 ≤ (4 / 3) * x ^ 2 * a := by
      rw [hbSq]
      have h := mul_le_mul_of_nonneg_left hty (by positivity : 0 ≤ 4 * x ^ 2)
      nlinarith only [h]
    have hsum : a + (4 / 3) * x ^ 2 ≤ 19 / 48 := by linarith only [ha', hxSq, hySqBound]
    have h := mul_le_mul_of_nonneg_left hsum hapos.le
    change a * a + b * b ≤ _
    nlinarith only [hbBound, h]
  have hu : 1 / 8 ≤ u := hcusp
  have hu0 : 0 ≤ u := by linarith only [hu]
  have huv : |v| ≤ 2 * u * (y * x) := by
    calc
      |v| ≤ y * x / 4 := hphase
      _ ≤ 2 * u * (y * x) := by
        have h := mul_le_mul_of_nonneg_right (show (1 / 4 : ℝ) ≤ 2 * u by linarith only [hu])
          (mul_nonneg hy0 hx0)
        linarith only [h]
  have hvsmall : |v| ≤ u / 4 := by
    have hxy : y * x ≤ 1 / 8 := by
      have h := mul_le_mul hy1 hx1 hx0 (by norm_num : (0 : ℝ) ≤ 1 / 4)
      linarith only [h]
    have h := mul_le_mul_of_nonneg_left hxy (by positivity : 0 ≤ 2 * u)
    linarith only [huv, h]
  have hvSq : v ^ 2 ≤ u ^ 2 / 16 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hvsmall 2
    rw [sq_abs] at h
    nlinarith only [h]
  have hcross : -(u * a / 3) ≤ v * b := by
    have habs : |v * b| ≤ u * a / 3 := by
      rw [abs_mul, hbAbs]
      calc
        |v| * (2 * y * x) ≤ (2 * u * (y * x)) * (2 * y * x) :=
          mul_le_mul_of_nonneg_right huv (by positivity)
        _ = (u * y ^ 2) * (4 * x ^ 2) := by ring
        _ ≤ (u * y ^ 2) * 1 := mul_le_mul_of_nonneg_left (by linarith only [hxSq]) (by positivity)
        _ = u * y ^ 2 := mul_one _
        _ ≤ u * a / 3 := by
          have h := mul_le_mul_of_nonneg_left hty hu0
          linarith only [h]
    exact (abs_le.mp habs).1
  have hquot : (13 / 19 : ℝ) * u ^ 2 ≤ (C ^ 2 / z).re := by
    rw [Complex.div_re, pow_two C, Complex.mul_re, Complex.mul_im, ← add_div]
    apply (le_div_iff₀ hzpos).mpr
    have hN := mul_le_mul_of_nonneg_left hzBound (by positivity : 0 ≤ (13 / 19 : ℝ) * u ^ 2)
    have hV := mul_le_mul_of_nonneg_right hvSq hapos.le
    have hB := mul_le_mul_of_nonneg_left hcross (by positivity : 0 ≤ 2 * u)
    change (13 / 19 : ℝ) * u ^ 2 * normSq z ≤ (u * u - v * v) * a + (u * v + v * u) * b
    nlinarith only [hN, hV, hB]
  have hnorm : ‖C ^ 2‖ ≤ (17 / 16 : ℝ) * u ^ 2 := by
    rw [Complex.norm_pow, Complex.sq_norm, Complex.normSq_apply]
    change u * u + v * v ≤ _
    nlinarith only [hvSq]
  have hA : (A * C ^ 2).re ≤ (17 / 20 : ℝ) * u ^ 2 := by
    calc
      _ ≤ ‖A * C ^ 2‖ := Complex.re_le_norm _
      _ = ‖A‖ * ‖C ^ 2‖ := norm_mul ..
      _ ≤ (4 / 5) * ((17 / 16) * u ^ 2) :=
        mul_le_mul hregular hnorm (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hEq : ((A - (3 / 2 : ℂ) / z) * C ^ 2).re =
      (A * C ^ 2).re - (3 / 2 : ℝ) * (C ^ 2 / z).re := by
    rw [show (A - (3 / 2 : ℂ) / z) * C ^ 2 =
        A * C ^ 2 - (3 / 2 : ℂ) * (C ^ 2 / z) by simp only [div_eq_mul_inv]; ring,
      Complex.sub_re, Complex.mul_re]
    norm_num [Complex.div_re, Complex.div_im]
  have huSq : (1 / 64 : ℝ) ≤ u ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8) hu 2
    nlinarith only [h]
  change ((A - (3 / 2 : ℂ) / z) * C ^ 2).re ≤ _
  rw [hEq]
  nlinarith only [hA, hquot, huSq]

#check @re_completed_class_product_le
#print axioms re_completed_class_product_le

/-- The same estimate on the archived disk with height parameter `1/512`
and scale index `0`. -/
theorem re_completed_class_product_le_on_first_dottie_disk {w A C : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter (1 / 512) 0) (dottieScaledRadius 0))
    (hregular : ‖A‖ ≤ 4 / 5) (hcusp : 1 / 8 ≤ C.re)
    (hphase : |C.im| ≤ |w.im| * (w.re - 1 / 2) / 4) :
    ((A - (3 / 2 : ℂ) / (w * (1 - w))) * C ^ 2).re ≤ -(1 / 400 : ℝ) := by
  have hstrip := dottieScaledRightDisk_strip hw
  have hcenter : dottieScaledRightCenter (1 / 512) 0 = (3 / 4 : ℂ) := by
    apply Complex.ext <;>
      norm_num [dottieScaledRightCenter, dottieRingScale, Complex.div_re, Complex.div_im]
  have hradius : dottieScaledRadius 0 = (31 / 128 : ℝ) := by
    norm_num [dottieScaledRadius, dottieRingScale]
  have hdist := Metric.mem_closedBall.mp hw
  rw [hcenter, hradius, dist_eq_norm] at hdist
  exact re_completed_class_product_le hstrip.1.le hstrip.2
    (hdist.trans (by norm_num)) hregular hcusp hphase

#check @re_completed_class_product_le_on_first_dottie_disk
#print axioms re_completed_class_product_le_on_first_dottie_disk

end FieldTarget
