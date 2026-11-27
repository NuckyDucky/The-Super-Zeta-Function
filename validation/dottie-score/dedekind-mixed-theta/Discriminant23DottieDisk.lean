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

/-- The completed class-product formula from the two binary forms of
discriminant `-23`. The two nontrivial class characters give the squared factor. -/
def discriminant23CompletedClassProduct (w : ℂ) : ℂ :=
  let A := classMellinReading summedTheta w
  let C := classMellinReading differencedTheta w
  (A - (3 / 2 : ℂ) / (w * (1 - w))) * C ^ 2

theorem re_discriminant23_classProduct_le_on_first_dottie_disk {w : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter (1 / 512) 0) (dottieScaledRadius 0)) :
    (discriminant23CompletedClassProduct w).re ≤ -(1 / 400 : ℝ) := by
  have hstrip := dottieScaledRightDisk_strip hw
  have hd := Metric.mem_closedBall.mp hw
  rw [dist_eq_norm] at hd
  have hm := (Complex.abs_im_le_norm (w - dottieScaledRightCenter (1 / 512) 0)).trans hd
  norm_num [dottieScaledRightCenter, dottieScaledRadius, dottieRingScale] at hm
  have him : |w.im| ≤ 1 / 4 := hm.trans (by norm_num)
  have hP := measurable_classTheta discriminant23PrincipalForm
  have hO := measurable_classTheta discriminant23OtherForm
  have hU : Measurable summedTheta := hP.add (hO.const_mul 2)
  have hD : Measurable differencedTheta := hP.sub hO
  obtain ⟨hA, hC, hphase⟩ := classMellin_integral_bounds hU hD
    (fun t ht ↦ (theta_bounds ht.le).1) (fun t ht ↦ (theta_bounds ht.le).2)
    hstrip.1.le hstrip.2.le him
  exact re_completed_class_product_le_on_first_dottie_disk hw hA hC hphase

theorem discriminant23_classProduct_ne_zero_on_first_dottie_disk {w : ℂ}
    (hw : w ∈ Metric.closedBall (dottieScaledRightCenter (1 / 512) 0) (dottieScaledRadius 0)) :
    discriminant23CompletedClassProduct w ≠ 0 := by
  intro hz
  have h := re_discriminant23_classProduct_le_on_first_dottie_disk hw
  rw [hz, Complex.zero_re] at h
  norm_num at h

#check @re_discriminant23_classProduct_le_on_first_dottie_disk
#check @discriminant23_classProduct_ne_zero_on_first_dottie_disk
#print axioms re_discriminant23_classProduct_le_on_first_dottie_disk
#print axioms discriminant23_classProduct_ne_zero_on_first_dottie_disk

end
end FieldTarget
