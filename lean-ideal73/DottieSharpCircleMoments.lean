import DottieMomentMass
import ArchivedDottieRetainedBudget

/-! The seventeen archived sharp-prefix moments give a uniform polynomial
approximation on the exact Dottie circle and its reflection. -/

open Complex Finset
open scoped ComplexConjugate

namespace QuarticModel

open SuperZeta.StirlingCorrection
open private dottieSharpSide from ArchivedDottieTailPartition
open private signedTerm from DottieSignedMoments

noncomputable def dottieSharpCenter : ℂ := 1/2 + (dottieHeight : ℂ)*I

noncomputable def dottieSharpFactor (w : ℂ) : ℂ :=
  (archivedThetaScale : ℂ)^w * Gamma w/(archivedDottieCompletionScale : ℂ)

noncomputable def dottieSharpMomentsPolynomial (w : ℂ) : ℂ :=
  ∑ k ∈ range 17, signedMoment archivedLatticeCoeff dottiePrefixEnd dottieSharpCenter k *
    (w-dottieSharpCenter)^k

noncomputable def dottieSharpMomentsCompletion (w : ℂ) : ℂ :=
  dottieSharpFactor w * dottieSharpMomentsPolynomial w +
    conj (dottieSharpFactor (1-conj w) * dottieSharpMomentsPolynomial (1-conj w))

private theorem sum_dottieSharpSide (N : ℕ) (w : ℂ) :
    (∑ n ∈ range (N+1), dottieSharpSide w n) =
      dottieSharpFactor w * signedDirichletPolynomial archivedLatticeCoeff N w := by
  rw [Finset.sum_range_succ', signedDirichletPolynomial, Finset.mul_sum,
    show dottieSharpSide w 0 = 0 from if_pos rfl, add_zero]
  apply sum_congr rfl
  intro n _
  rw [dottieSharpSide, if_neg (Nat.succ_ne_zero n), dottieSharpFactor, signedTerm,
    Complex.ofReal_div,
    Complex.div_cpow_ofReal_nonneg archivedThetaScale_pos.le (Nat.cast_nonneg (α := ℝ) (n+1)),
    Complex.ofReal_natCast, Complex.cpow_neg]
  ring

theorem dottie_sharp_prefix_eq_completed_dirichlet (w : ℂ) :
    dottieSharpPrefix w =
      dottieSharpFactor w * signedDirichletPolynomial archivedLatticeCoeff dottiePrefixEnd w +
      conj (dottieSharpFactor (1-conj w) *
        signedDirichletPolynomial archivedLatticeCoeff dottiePrefixEnd (1-conj w)) := by
  unfold dottieSharpPrefix
  rw [Finset.sum_add_distrib, ← map_sum, sum_dottieSharpSide, sum_dottieSharpSide]

theorem dottie_sharp_circle_offset {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖w-dottieSharpCenter‖ ≤ 67/2048 := by
  have hc : archivedRightCenter dottieHeight - dottieSharpCenter = 1/64 - (1/512 : ℂ)*I := by
    apply Complex.ext <;> norm_num [archivedRightCenter, dottieSharpCenter, Complex.mul_re, Complex.mul_im]
  have hr : ‖w-archivedRightCenter dottieHeight‖ = 31/2048 := by
    simpa only [dist_eq_norm] using Metric.mem_sphere.mp hw
  have hd : ‖archivedRightCenter dottieHeight - dottieSharpCenter‖ ≤ 36/2048 := by
    rw [hc]
    refine (norm_sub_le _ _).trans ?_
    norm_num [norm_mul, norm_div, Complex.norm_ofNat]
  rw [show w-dottieSharpCenter = (w-archivedRightCenter dottieHeight)+
    (archivedRightCenter dottieHeight-dottieSharpCenter) by ring]
  exact (norm_add_le _ _).trans (by linarith only [hr,hd])

private theorem dottie_sharp_center_reflected : 1-conj dottieSharpCenter = dottieSharpCenter := by
  apply Complex.ext <;> norm_num [dottieSharpCenter, Complex.mul_re, Complex.mul_im]

private theorem dottie_sharp_reflected_offset (w : ℂ) :
    ‖(1-conj w)-dottieSharpCenter‖ = ‖w-dottieSharpCenter‖ := by
  conv_lhs => rw [← dottie_sharp_center_reflected]
  rw [show (1-conj w)-(1-conj dottieSharpCenter) = -conj (w-dottieSharpCenter) by
    rw [map_sub]
    ring, norm_neg, Complex.norm_conj]

theorem dottie_sharp_moments_error {w : ℂ} (hw : ‖w-dottieSharpCenter‖ ≤ 67/2048) :
    ‖signedDirichletPolynomial archivedLatticeCoeff dottiePrefixEnd w - dottieSharpMomentsPolynomial w‖ ≤
      1/10^11 := by
  have hlog : Real.log (dottiePrefixEnd : ℝ) < 22 := by
    have hp : (2.7 : ℝ)^22 ≤ Real.exp 22 := by
      rw [show (22 : ℝ) = (22 : ℕ)*(1 : ℝ) by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
    exact (Real.log_lt_iff_lt_exp (by norm_num [dottiePrefixEnd])).mpr
      ((by norm_num [dottiePrefixEnd] : (dottiePrefixEnd : ℝ) < (2.7 : ℝ)^22).trans_le hp)
  have hl : 0 ≤ Real.log (dottiePrefixEnd : ℝ) := Real.log_nonneg (by norm_num [dottiePrefixEnd])
  let q := ‖w-dottieSharpCenter‖ * Real.log (dottiePrefixEnd : ℝ)
  have hq₀ : 0 ≤ q := mul_nonneg (norm_nonneg _) hl
  have hq : q ≤ 3/4 :=
    (mul_le_mul hw hlog.le hl (by norm_num)).trans (by norm_num)
  have he : Real.exp q ≤ 3 :=
    (Real.exp_le_exp.mpr (hq.trans (by norm_num : (3 : ℝ)/4 ≤ 1))).trans (by linarith [Real.exp_one_lt_d9])
  have hm : signedMomentMass archivedLatticeCoeff dottiePrefixEnd ≤ 76000 := by
    have h := archivedMomentMass_le_two_sqrt dottiePrefixEnd
    rw [show dottiePrefixEnd.sqrt = 37984 by decide +kernel] at h
    exact h.trans (by norm_num)
  have hf : q^17 / (17 : ℕ).factorial * Real.exp q ≤ 1/10^16 := by
    calc
      _ ≤ (3/4 : ℝ)^17 / (17 : ℕ).factorial * 3 := by gcongr
      _ ≤ _ := by norm_num [Nat.factorial]
  have ht := signed_dirichlet_taylor_bound (a := archivedLatticeCoeff) (N := dottiePrefixEnd)
    (s := dottieSharpCenter) (by norm_num [dottieSharpCenter, Complex.mul_re]) (w-dottieSharpCenter) 17
  dsimp only at ht
  rw [add_sub_cancel] at ht
  have htail : 0 ≤ q^17 / ((17 : ℕ).factorial : ℝ) * Real.exp q :=
    mul_nonneg (div_nonneg (pow_nonneg hq₀ _) (Nat.cast_nonneg _)) (Real.exp_pos _).le
  have hfinal : signedMomentMass archivedLatticeCoeff dottiePrefixEnd *
      (q^17 / ((17 : ℕ).factorial : ℝ) * Real.exp q) ≤ (1 : ℝ)/10^11 :=
    (mul_le_mul hm hf htail (by norm_num)).trans (by norm_num)
  unfold dottieSharpMomentsPolynomial
  exact ht.trans hfinal

theorem dottie_sharp_circle_completed_moments_error {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048)) :
    ‖dottieSharpPrefix w-dottieSharpMomentsCompletion w‖ ≤
      (‖dottieSharpFactor w‖ + ‖dottieSharpFactor (1-conj w)‖)/10^11 := by
  have hd := dottie_sharp_circle_offset hw
  have hd' : ‖(1-conj w)-dottieSharpCenter‖ ≤ 67/2048 := by rwa [dottie_sharp_reflected_offset]
  rw [dottie_sharp_prefix_eq_completed_dirichlet, dottieSharpMomentsCompletion, add_sub_add_comm, ← map_sub,
    ← mul_sub, ← mul_sub]
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_conj, norm_mul, norm_mul, div_eq_mul_inv, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (one_div (10^11 : ℝ) ▸ dottie_sharp_moments_error hd)
      (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (one_div (10^11 : ℝ) ▸ dottie_sharp_moments_error hd') (norm_nonneg _))

#print axioms dottie_sharp_prefix_eq_completed_dirichlet
#print axioms dottie_sharp_circle_offset
#print axioms dottie_sharp_moments_error
#print axioms dottie_sharp_circle_completed_moments_error

end QuarticModel
