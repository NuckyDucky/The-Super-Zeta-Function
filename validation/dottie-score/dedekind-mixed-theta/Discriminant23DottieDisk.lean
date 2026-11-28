import Discriminant23ThetaEnvelope
import DottieClassMellinBounds
import Mathlib.MeasureTheory.Constructions.Polish.Basic

namespace FieldTarget

open Complex SuperZeta.StirlingCorrection

noncomputable section

private def classHeat (t : ℝ) : ℝ :=
  Real.exp (-discriminant23ThetaScale * (1 + t))

private def principalTheta (t : ℝ) : ℝ :=
  classThetaStar discriminant23PrincipalForm (classHeat t)

private def otherTheta (t : ℝ) : ℝ :=
  classThetaStar discriminant23OtherForm (classHeat t)

private def summedTheta (t : ℝ) : ℝ := principalTheta t + 2 * otherTheta t

private def differencedTheta (t : ℝ) : ℝ := principalTheta t - otherTheta t

private theorem measurable_classTheta (Q : ℤ → ℤ → ℤ) :
    Measurable (fun t : ℝ ↦ classThetaStar Q (classHeat t)) := by
  have hm : Measurable classHeat := by unfold classHeat; fun_prop
  unfold classThetaStar
  refine Measurable.tsum (fun p : ℤ × ℤ ↦ ?_)
  by_cases hp : p = (0, 0)
  · simpa only [hp, ite_true] using (measurable_const : Measurable (fun _ : ℝ ↦ (0 : ℝ)))
  · simpa only [ite_eq_right hp] using hm.pow_const (Q p.1 p.2).toNat

private theorem classHeat_bounds {t : ℝ} (ht : 0 ≤ t) :
    (1 / 4) * Real.exp (-(4 / 3) * t) ≤ classHeat t ∧
      classHeat t ≤ (3 / 11) * Real.exp (-(13 / 10) * t) ∧ classHeat t ≤ 3 / 11 := by
  obtain ⟨hαl, hαu⟩ := discriminant23_thetaScale_interval
  obtain ⟨hel, heu⟩ := discriminant23_thetaExp_interval
  have hv1 := mul_le_mul_of_nonneg_right hαl ht
  have hv2 := mul_le_mul_of_nonneg_right hαu ht
  have hu := Real.exp_le_exp.mpr (show -discriminant23ThetaScale * t ≤ -(13 / 10) * t by
    linarith only [hv1])
  have hl := Real.exp_le_exp.mpr (show -(4 / 3) * t ≤ -discriminant23ThetaScale * t by
    linarith only [hv2])
  have hq : classHeat t = Real.exp (-discriminant23ThetaScale) *
      Real.exp (-discriminant23ThetaScale * t) := by
    unfold classHeat
    rw [← Real.exp_add]
    congr 1
    ring
  have hup : classHeat t ≤ (3 / 11) * Real.exp (-(13 / 10) * t) := by
    rw [hq]
    exact mul_le_mul heu hu (Real.exp_pos _).le (by norm_num)
  refine ⟨?_, hup, hup.trans ?_⟩
  · rw [hq]
    exact mul_le_mul hel hl (Real.exp_pos _).le (Real.exp_pos _).le
  · exact mul_le_of_le_one_right (by norm_num)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by norm_num) ht))

private theorem theta_bounds {t : ℝ} (ht : 0 ≤ t) :
    (0 ≤ summedTheta t ∧ summedTheta t ≤ (54 / 55) * Real.exp (-(13 / 10) * t)) ∧
    ((5 / 16) * Real.exp (-(4 / 3) * t) ≤ differencedTheta t ∧
      differencedTheta t ≤ (63 / 110) * Real.exp (-(13 / 10) * t)) := by
  obtain ⟨hl, hu, hq⟩ := classHeat_bounds ht
  have hq0 : 0 ≤ classHeat t := (Real.exp_pos _).le
  have ⟨hp1, hp2, ho1, ho2⟩ := discriminant23_classThetaStar_bounds hq0 hq
  change 2 * classHeat t ≤ principalTheta t at hp1
  change principalTheta t ≤ (21 / 10) * classHeat t at hp2
  change 0 ≤ otherTheta t at ho1
  change otherTheta t ≤ (3 / 4) * classHeat t at ho2
  unfold summedTheta differencedTheta
  exact ⟨⟨by linarith only [hp1, ho1, hq0], by linarith only [hp2, ho2, hu]⟩,
    ⟨by linarith only [hp1, ho2, hl], by linarith only [hp2, ho1, hu]⟩⟩

/-- The half-folded reading of the sum of the three ideal classes. -/
def discriminant23TotalClassReading : ℂ → ℂ := classMellinReading summedTheta

/-- The half-folded reading of the principal class minus either other class. -/
def discriminant23CharacterClassReading : ℂ → ℂ := classMellinReading differencedTheta

/-- The completed class-product formula from the two binary forms of
discriminant `-23`. The two nontrivial class characters give the squared factor. -/
def discriminant23CompletedClassProduct (w : ℂ) : ℂ :=
  (discriminant23TotalClassReading w - (3 / 2 : ℂ) / (w * (1 - w))) *
    discriminant23CharacterClassReading w ^ 2

/-- A uniform Cauchy bound for the completed field reading on the outer strip. -/
theorem discriminant23_completedClassProduct_norm_le_on_upper_strip {w : ℂ}
    (hlo : -2 ≤ w.re) (hhi : w.re ≤ 3) (him : 2 ≤ w.im) :
    ‖8 * discriminant23CompletedClassProduct w‖ ≤ 2 ^ 12 := by
  have hP := measurable_classTheta discriminant23PrincipalForm
  have hO := measurable_classTheta discriminant23OtherForm
  have hU : ‖discriminant23TotalClassReading w‖ ≤ 20 / 3 := by
    apply classMellinReading_norm_le_twenty_thirds (hP.add (hO.const_mul 2)) _ hlo hhi
    intro t ht
    obtain ⟨ht₀, ht₁⟩ := (theta_bounds ht.le).1
    change |summedTheta t| ≤ _
    rw [abs_of_nonneg ht₀]
    exact ht₁.trans (mul_le_of_le_one_left (Real.exp_pos _).le (by norm_num))
  have hV : ‖discriminant23CharacterClassReading w‖ ≤ 20 / 3 := by
    apply classMellinReading_norm_le_twenty_thirds (hP.sub hO) _ hlo hhi
    intro t ht
    obtain ⟨ht₀, ht₁⟩ := (theta_bounds ht.le).2
    change |differencedTheta t| ≤ _
    rw [abs_of_nonneg ((by positivity : 0 ≤ (5 / 16) * Real.exp (-(4 / 3) * t)).trans ht₀)]
    exact ht₁.trans (mul_le_of_le_one_left (Real.exp_pos _).le (by norm_num))
  have hw : 2 ≤ ‖w‖ := him.trans ((le_abs_self w.im).trans (abs_im_le_norm w))
  have hOne : 2 ≤ ‖1 - w‖ := by
    refine him.trans ?_
    have h := abs_im_le_norm (1 - w)
    simpa only [sub_im, one_im, zero_sub, abs_neg, abs_of_nonneg (by linarith : 0 ≤ w.im)] using h
  have hDen : 4 ≤ ‖w * (1 - w)‖ := by
    rw [norm_mul]
    exact (show (4 : ℝ) = 2 * 2 by norm_num) ▸
      mul_le_mul hw hOne (by norm_num) (norm_nonneg w)
  have hPole : ‖(3 / 2 : ℂ) / (w * (1 - w))‖ ≤ 1 := by
    rw [norm_div, div_le_iff₀ ((by norm_num : (0 : ℝ) < 4).trans_le hDen), one_mul]
    exact (show ‖(3 / 2 : ℂ)‖ ≤ 4 by norm_num [norm_div]).trans hDen
  have hUsub :
      ‖discriminant23TotalClassReading w - (3 / 2 : ℂ) / (w * (1 - w))‖ ≤ 23 / 3 := by
    refine (norm_sub_le _ _).trans ((add_le_add hU hPole).trans ?_)
    norm_num
  unfold discriminant23CompletedClassProduct
  rw [norm_mul, norm_mul, norm_pow, show ‖(8 : ℂ)‖ = 8 by norm_num]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul hUsub
    (pow_le_pow_left₀ (norm_nonneg _) hV 2) (by positivity) (by norm_num)) (by norm_num)).trans ?_
  norm_num

private theorem discriminant23_class_reading_bounds_right {w : ℂ}
    (hhalf : 1 / 2 ≤ w.re) (hone : w.re ≤ 1) :
    ‖discriminant23TotalClassReading w‖ ≤ 108 / 143 ∧
      15 / 88 - (225 / 1859) * w.im ^ 2 ≤ (discriminant23CharacterClassReading w).re ∧
      |(discriminant23CharacterClassReading w).im| ≤ |w.im| * (w.re - 1 / 2) / 4 := by
  have hP := measurable_classTheta discriminant23PrincipalForm
  have hO := measurable_classTheta discriminant23OtherForm
  exact classMellin_integral_bounds_with_height (hP.add (hO.const_mul 2)) (hP.sub hO)
    (fun t ht ↦ (theta_bounds ht.le).1) (fun t ht ↦ (theta_bounds ht.le).2) hhalf hone

private theorem discriminant23_class_reading_bounds {w : ℂ}
    (hhalf : 1 / 2 ≤ w.re) (hone : w.re ≤ 1) (him : |w.im| ≤ 1 / 2) :
    ‖discriminant23TotalClassReading w‖ ≤ 4 / 5 ∧
      1 / 8 ≤ (discriminant23CharacterClassReading w).re ∧
      |(discriminant23CharacterClassReading w).im| ≤ |w.im| * (w.re - 1 / 2) / 4 := by
  obtain ⟨hA, hC, hphase⟩ := discriminant23_class_reading_bounds_right hhalf hone
  have hi := pow_le_pow_left₀ (abs_nonneg _) him 2
  rw [sq_abs] at hi
  exact ⟨hA.trans (by norm_num), by nlinarith only [hi, hC], hphase⟩

theorem re_discriminant23_classProduct_le_on_first_dottie_disk {w : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter (1 / 512) 0) (dottieScaledRadius 0)) :
    (discriminant23CompletedClassProduct w).re ≤ -(1 / 400 : ℝ) := by
  have hstrip := dottieScaledRightDisk_strip hw
  have hd := Metric.mem_closedBall.mp hw
  rw [dist_eq_norm] at hd
  have hm := (Complex.abs_im_le_norm (w - dottieScaledRightCenter (1 / 512) 0)).trans hd
  norm_num [dottieScaledRightCenter, dottieScaledRadius, dottieRingScale] at hm
  have him : |w.im| ≤ 1 / 2 := hm.trans (by norm_num)
  obtain ⟨hA, hC, hphase⟩ := discriminant23_class_reading_bounds hstrip.1.le hstrip.2.le him
  exact re_completed_class_product_le_on_first_dottie_disk hw hA hC hphase

theorem discriminant23_classProduct_ne_zero_on_first_dottie_disk {w : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter (1 / 512) 0) (dottieScaledRadius 0)) :
    discriminant23CompletedClassProduct w ≠ 0 := by
  intro hz
  have h := re_discriminant23_classProduct_le_on_first_dottie_disk hw
  rw [hz, Complex.zero_re] at h
  norm_num at h

/-- The pole-clearing polynomial has a uniform norm envelope across the strip. -/
theorem norm_dottie_pole_weight_sq_le {w : ℂ} (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1) :
    ‖w * (1 - w)‖ ^ 2 ≤ 1 / 16 + w.im ^ 2 + w.im ^ 4 := by
  let u := w.re * (1 - w.re)
  have hu0 : 0 ≤ u := mul_nonneg h0 (sub_nonneg.mpr h1)
  have hu1 : u ≤ 1 / 4 := by
    dsimp [u]
    nlinarith only [sq_nonneg (w.re - 1 / 2)]
  have huSq := pow_le_pow_left₀ hu0 hu1 2
  have hcross : 0 ≤ 2 * u * w.im ^ 2 := by positivity
  calc
    ‖w * (1 - w)‖ ^ 2 = u ^ 2 + w.im ^ 2 + w.im ^ 4 - 2 * u * w.im ^ 2 := by
      rw [norm_mul, mul_pow, Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
        Complex.one_im, zero_sub]
      dsimp [u]
      ring
    _ ≤ _ := by nlinarith only [huSq, hcross]

private theorem norm_pole_denominator_le {w : ℂ}
    (hhalf : 1 / 2 ≤ w.re) (hone : w.re ≤ 1) (him : |w.im| ≤ 1 / 2) :
    ‖w * (1 - w)‖ ≤ 3 / 4 := by
  have h := norm_dottie_pole_weight_sq_le (by linarith only [hhalf]) hone
  have h2 := pow_le_pow_left₀ (abs_nonneg _) him 2
  have h4 := pow_le_pow_left₀ (abs_nonneg _) him 4
  rw [sq_abs] at h2
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, sq_abs] at h4
  apply (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 4)).mp
  nlinarith only [h, h2, h4]

private theorem re_weighted_classProduct_le_right {w : ℂ}
    (hhalf : 1 / 2 ≤ w.re) (hone : w.re < 1) (him : |w.im| ≤ 1 / 2) :
    (w * (1 - w) * discriminant23CompletedClassProduct w).re ≤ -(3 / 512 : ℝ) := by
  let z := w * (1 - w)
  let A := classMellinReading summedTheta w
  let C := classMellinReading differencedTheta w
  let u := C.re
  let v := C.im
  obtain ⟨hA, hu, hphase⟩ := discriminant23_class_reading_bounds hhalf hone.le him
  change ‖A‖ ≤ _ at hA
  change 1 / 8 ≤ u at hu
  have hxy := mul_le_mul him (show w.re - 1 / 2 ≤ 1 / 2 by linarith only [hone])
    (sub_nonneg.mpr hhalf) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hv : |v| ≤ u / 2 := by
    change |v| ≤ _ at hphase
    linarith only [hphase, hxy, hu]
  have hvSq : v ^ 2 ≤ u ^ 2 / 4 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) hv 2
    rw [sq_abs] at h
    nlinarith only [h]
  have huSq : (1 / 64 : ℝ) ≤ u ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 8) hu 2
    linarith only [h]
  have hCre : (3 / 4) * u ^ 2 ≤ (C ^ 2).re := by
    rw [pow_two C, Complex.mul_re]
    change (3 / 4) * u ^ 2 ≤ u * u - v * v
    nlinarith only [hvSq]
  have hCnorm : ‖C ^ 2‖ ≤ (5 / 4) * u ^ 2 := by
    rw [norm_pow, Complex.sq_norm, Complex.normSq_apply]
    change u * u + v * v ≤ _
    nlinarith only [hvSq]
  have hReg : (z * A * C ^ 2).re ≤ (3 / 4) * u ^ 2 := calc
    _ ≤ ‖z * A * C ^ 2‖ := Complex.re_le_norm _
    _ = (‖z‖ * ‖A‖) * ‖C ^ 2‖ := by rw [norm_mul, norm_mul]
    _ ≤ ((3 / 4) * (4 / 5)) * ((5 / 4) * u ^ 2) :=
      mul_le_mul (mul_le_mul (norm_pole_denominator_le hhalf hone.le him) hA
        (norm_nonneg _) (by norm_num)) hCnorm (norm_nonneg _) (by norm_num)
    _ = _ := by ring
  have hw0 : w ≠ 0 := by rintro rfl; norm_num at hhalf
  have hw1 : 1 - w ≠ 0 := by
    intro h
    rw [← sub_eq_zero.mp h] at hone
    norm_num at hone
  have hz : z ≠ 0 := mul_ne_zero hw0 hw1
  have heq : z * discriminant23CompletedClassProduct w =
      z * A * C ^ 2 - (3 / 2 : ℂ) * C ^ 2 := by
    change z * ((A - (3 / 2 : ℂ) / z) * C ^ 2) = _
    field_simp [hz]
  have hre : (z * discriminant23CompletedClassProduct w).re =
      (z * A * C ^ 2).re - (3 / 2 : ℝ) * (C ^ 2).re := by
    rw [heq, Complex.sub_re, Complex.mul_re (3 / 2 : ℂ)]
    norm_num [Complex.div_re, Complex.div_im]
  change (z * discriminant23CompletedClassProduct w).re ≤ _
  rw [hre]
  nlinarith only [hReg, hCre, huSq]

private theorem classMellinReading_one_sub (H : ℝ → ℝ) (w : ℂ) :
    classMellinReading H (1 - w) = classMellinReading H w := by
  have hweight (v : ℝ) : classMellinWeight (1 - w) v = classMellinWeight w v := by
    unfold classMellinWeight
    rw [show 1 - w - 1 = -w by ring, show -(1 - w) = w - 1 by ring, add_comm]
  simp only [classMellinReading, hweight]

private theorem discriminant23_classProduct_one_sub (w : ℂ) :
    discriminant23CompletedClassProduct (1 - w) = discriminant23CompletedClassProduct w := by
  simp only [discriminant23CompletedClassProduct, discriminant23TotalClassReading,
    discriminant23CharacterClassReading, classMellinReading_one_sub, sub_sub_cancel,
    mul_comm (1 - w) w]

/-- The norm allowance and the quadratic real-part bound hold throughout
the strip by the symmetry of the folded integrals. -/
theorem discriminant23_class_reading_bounds_on_strip {w : ℂ}
    (h0 : 0 ≤ w.re) (h1 : w.re ≤ 1) :
    ‖discriminant23TotalClassReading w‖ ≤ 108 / 143 ∧
      15 / 88 - (225 / 1859) * w.im ^ 2 ≤ (discriminant23CharacterClassReading w).re := by
  by_cases hhalf : 1 / 2 ≤ w.re
  · have h := discriminant23_class_reading_bounds_right hhalf h1
    exact ⟨h.1, h.2.1⟩
  · have hhalf' : 1 / 2 ≤ (1 - w).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith only [lt_of_not_ge hhalf]
    have h1' : (1 - w).re ≤ 1 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith only [h0]
    have h := discriminant23_class_reading_bounds_right hhalf' h1'
    simpa only [discriminant23TotalClassReading, discriminant23CharacterClassReading,
      classMellinReading_one_sub, Complex.sub_im, Complex.one_im, zero_sub, neg_sq] using
      And.intro h.1 h.2.1

/-- A polynomial weight clears the poles and keeps a signed margin across
the full width of the open strip up to height `1/2`. -/
theorem re_weighted_discriminant23_classProduct_le_on_low_strip {w : ℂ}
    (h0 : 0 < w.re) (h1 : w.re < 1) (him : |w.im| ≤ 1 / 2) :
    (w * (1 - w) * discriminant23CompletedClassProduct w).re ≤ -(3 / 512 : ℝ) := by
  by_cases hhalf : 1 / 2 ≤ w.re
  · exact re_weighted_classProduct_le_right hhalf h1 him
  · have hhalf' : 1 / 2 ≤ (1 - w).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith only [lt_of_not_ge hhalf]
    have h1' : (1 - w).re < 1 := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith only [h0]
    have him' : |(1 - w).im| ≤ 1 / 2 := by
      simpa only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using him
    simpa only [sub_sub_cancel, mul_comm (1 - w) w, discriminant23_classProduct_one_sub] using
      re_weighted_classProduct_le_right hhalf' h1' him'

#check @re_discriminant23_classProduct_le_on_first_dottie_disk
#check @discriminant23_classProduct_ne_zero_on_first_dottie_disk
#check @re_weighted_discriminant23_classProduct_le_on_low_strip
#print axioms re_discriminant23_classProduct_le_on_first_dottie_disk
#print axioms discriminant23_classProduct_ne_zero_on_first_dottie_disk
#print axioms norm_dottie_pole_weight_sq_le
#print axioms discriminant23_class_reading_bounds_on_strip
#print axioms re_weighted_discriminant23_classProduct_le_on_low_strip

end
#print axioms discriminant23_completedClassProduct_norm_le_on_upper_strip

end FieldTarget
