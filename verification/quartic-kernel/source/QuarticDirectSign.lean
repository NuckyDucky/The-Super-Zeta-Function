import QuarticAbelEnvelope
import QuarticCertificateState
import QuarticMellinFold
import QuarticSlope

open MeasureTheory Set
open GaussianSideIntegral

namespace QuarticKernel

noncomputable def sineFloor (x : ℝ) : ℝ :=
  if 27*x/100 ≤ 4 then QuarticSlope.lowerPoly (27*x/100) else -(1/4)

private theorem sineFloor_le_sinc {t x : ℝ} (ht : |t| ≤ 27/100) (hx : 0 ≤ x) :
    sineFloor x ≤ sinc (t*x) := by
  rw [sineFloor]
  apply QuarticSlope.uniform_sinc_lower
  rw [abs_mul, abs_of_nonneg hx]
  linarith only [mul_le_mul_of_nonneg_right ht hx]

private theorem sinc_ge_neg_quarter (y : ℝ) : -(1/4:ℝ) ≤ sinc y := by
  have h := QuarticSlope.uniform_sinc_lower y (max 5 |y|) (le_max_right _ _)
  have h₄ : ¬ max 5 |y| ≤ 4 := not_le_of_gt
    ((by norm_num : (4:ℝ) < 5).trans_le (le_max_left _ _))
  simpa only [if_neg h₄] using h

private theorem average_eq (y : ℝ) : GaussianSideError.averageCosh y = sinhc y :=
  GaussianSideError.averageCosh_eq y

/-- On the compact part of the integral, the horizontal factor can only
lower the reading where the sine weight is negative. -/
theorem compact_weight_lower {a t x : ℝ} (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100)
    (hx : x ∈ Icc 0 18) :
    sineFloor x - 1/25 ≤ sinc (t*x) * sinhc (a*x) := by
  have habs : |a*x| ≤ |(9/10:ℝ)| := by
    rw [abs_mul, abs_of_nonneg hx.1, abs_of_pos (by norm_num : (0:ℝ) < 9/10)]
    have h := mul_le_mul_of_nonneg_right ha hx.1
    linarith [hx.2]
  have he := GaussianSideError.averageCosh_abs_mono habs
  rw [average_eq, average_eq] at he
  have he' : sinhc (a*x) ≤ 1 + 4/25 := by
    have hd : sinhc (9/10) ≤ (11407:ℝ)/10000 := by
      rw [sinhc, if_neg (by norm_num)]
      linarith [GaussianSideConstants.sinh_ratio]
    linarith only [he, hd]
  have h1 : 1 ≤ sinhc (a*x) := by
    rw [← average_eq]
    exact GaussianSideError.one_le_averageCosh _
  have hmul : -(1/4:ℝ) * (sinhc (a*x)-1) ≤ sinc (t*x) * (sinhc (a*x)-1) :=
    mul_le_mul_of_nonneg_right (sinc_ge_neg_quarter _) (sub_nonneg.mpr h1)
  have floorLe := sineFloor_le_sinc ht hx.1
  nlinarith only [hmul, he', floorLe]

private theorem floor_integrable :
    IntegrableOn (fun x => mass x * (sineFloor x - 1/25)) (Icc 0 18) := by
  have hm : IntegrableOn mass (Icc 0 18) := mass_integrable.mono_set fun _ h => h.1
  have hc : Continuous (fun x : ℝ => QuarticSlope.lowerPoly (27*x/100) - 1/25) := by
    unfold QuarticSlope.lowerPoly
    fun_prop
  have ha : IntegrableOn (fun x => mass x * (QuarticSlope.lowerPoly (27*x/100) - 1/25))
      (Icc 0 18) := hm.mul_continuousOn hc.continuousOn isCompact_Icc
  have hb : IntegrableOn (fun x => mass x * (-(1/4:ℝ) - 1/25)) (Icc 0 18) :=
    hm.mul_const _
  have hmeas : MeasurableSet {x : ℝ | 27*x/100 ≤ 4} :=
    measurableSet_le (by fun_prop) measurable_const
  change Integrable (fun x => mass x * (sineFloor x - 1/25)) (volume.restrict (Icc 0 18))
  convert Integrable.piecewise hmeas ha.integrableOn hb.integrableOn using 1
  funext x
  by_cases h : 27*x/100 ≤ 4 <;> simp [sineFloor, Set.piecewise, h]

/-- One fixed real integral suffices across the whole rectangle. The
coefficient-prefix premise supplies positivity on the integration domain. -/
theorem direct_slope_floor {a t : ℝ} (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100)
    (prefixPositive : ∀ j : ℕ, 0 < j → j ≤ 33554432 → 1 ≤ prefixSum j)
    (lower : 400000 + (1:ℝ)/10^10 < ∫ x in Icc (0:ℝ) 18, mass x * (sineFloor x - 1/25)) :
    400000 < GaussianSideIntegral.slope kernel a t := by
  let f (x : ℝ) := mass x * sinc (t*x) * sinhc (a*x)
  have hf : IntegrableOn f (Ici 0) := sinhc_sinc_mass_integrable ha t
  have hsub : Icc (0:ℝ) 18 ⊆ Ici 0 := fun _ hx => hx.1
  have hsub' : Ioi (18:ℝ) ⊆ Ici 0 :=
    fun _ hx => (by norm_num : (0:ℝ) ≤ 18).trans (mem_Ioi.mp hx).le
  have hmass (x : ℝ) (hx : 0 ≤ x) : 0 ≤ mass x := by
    unfold mass
    exact mul_nonneg (mul_nonneg (by norm_num) (kernel_pos_of_actual_prefix prefixPositive hx).le)
      (sq_nonneg x)
  have hcore : (∫ x in Icc (0:ℝ) 18, mass x * (sineFloor x - 1/25)) ≤
      ∫ x in Icc (0:ℝ) 18, f x := by
    apply setIntegral_mono_on floor_integrable (hf.mono_set hsub) measurableSet_Icc
    intro x hx
    simpa only [f, mul_assoc] using
      mul_le_mul_of_nonneg_left (compact_weight_lower ha ht hx) (hmass x hx.1)
  have htail : |∫ x in Ioi (18:ℝ), f x| < (1:ℝ)/10^10 := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm f).trans_lt ?_
    refine (setIntegral_mono_on (hf.mono_set hsub').norm weighted_tail.1 measurableSet_Ioi
      fun x hx => ?_).trans_lt weighted_tail.2
    have hx0 : 0 ≤ x := hsub' hx
    have hax : |a*x| ≤ x/20 := by
      rw [abs_mul, abs_of_nonneg hx0]
      linarith only [mul_le_mul_of_nonneg_right ha hx0]
    have h1 := GaussianSideError.one_le_averageCosh (a*x)
    have h2 := (GaussianSideError.averageCosh_le_exp_abs (a*x)).trans (Real.exp_le_exp.mpr hax)
    rw [average_eq] at h1 h2
    change ‖mass x * sinc (t*x) * sinhc (a*x)‖ ≤ mass x * Real.exp (x/20)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hmass x hx0),
      abs_of_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans h1)]
    calc
      _ ≤ (mass x * 1) * Real.exp (x/20) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (abs_sinc_le_one _) (hmass x hx0)) h2
          ((by norm_num : (0:ℝ) ≤ 1).trans h1) (by simpa only [mul_one] using hmass x hx0)
      _ = _ := by simp
  have hdis : Disjoint (Icc (0:ℝ) 18) (Ioi 18) :=
    Set.disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy)
  change 400000 < ∫ x in Ici (0:ℝ), f x
  rw [← Icc_union_Ioi_eq_Ici (by norm_num : (0:ℝ) ≤ 18),
    setIntegral_union hdis measurableSet_Ioi (hf.mono_set hsub) (hf.mono_set hsub')]
  linarith only [lower, hcore, (abs_lt.mp htail).1]

/-- The side reading for the Mellin transform of the actual quartic,
reduced to a prefix certificate and one scalar lower bound. -/
theorem direct_mellin_reading
    (reflection : ∀ t : ℝ, 0 < t → theta (t/scale) = t⁻¹ * theta (t⁻¹/scale))
    (prefixPositive : ∀ j : ℕ, 0 < j → j ≤ 33554432 → 1 ≤ prefixSum j)
    (lower : 400000 + (1:ℝ)/10^10 < ∫ x in Icc (0:ℝ) 18, mass x * (sineFloor x - 1/25))
    {a t : ℝ} (ha : |a| ≤ 1/20) (ht : |t| ≤ 27/100) :
    (mellin (fun x : ℝ => (theta (x/scale) : ℂ)) (GaussianSideSign.point a t)).im =
      a*t*GaussianSideIntegral.slope kernel a t ∧ 400000 < GaussianSideIntegral.slope kernel a t := by
  refine ⟨?_, direct_slope_floor ha ht prefixPositive lower⟩
  rw [mellin_fold_in_rectangle (theta_reflection_iff_kernel_even.mp reflection) a t ha]
  exact halfMellin_im_eq kernel a t (complex_integrable ha t)

#print axioms compact_weight_lower
#print axioms direct_slope_floor
#print axioms direct_mellin_reading

end QuarticKernel
