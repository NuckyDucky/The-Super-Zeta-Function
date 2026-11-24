import DottieMomentMass
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Quantify how much the same signed polynomial moves when replacing the
exact Dottie reference height by a rational evaluation point. -/

open Complex Finset

namespace QuarticModel

open SuperZeta.StirlingCorrection
open private signedTerm signedTerm_shift signedTerm_norm from DottieSignedMoments

theorem dottie_unit_phase_distance (u t : ℝ) :
    ‖Complex.exp ((u : ℂ)*I) - Complex.exp ((t : ℂ)*I)‖ ≤ |u-t| := by
  have h : (t : ℂ)*I + I*((u-t : ℝ) : ℂ) = (u : ℂ)*I := by push_cast; ring
  have e : Complex.exp ((u : ℂ)*I) - Complex.exp ((t : ℂ)*I) =
      Complex.exp ((t : ℂ)*I) * (Complex.exp (I*((u-t : ℝ) : ℂ))-1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add, h]
  rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  simpa only [Real.norm_eq_abs] using Real.norm_exp_I_mul_ofReal_sub_one_le (x := u-t)

/-- A unit-height displacement costs at most the absolute mass times
`log N`, for the exact polynomial on the critical line. -/
theorem signed_dirichlet_height_bound (a : ℕ → ℤ) (N : ℕ) (u t : ℝ) :
    ‖signedDirichletPolynomial a N (1/2 + (u : ℂ)*I) -
      signedDirichletPolynomial a N (1/2 + (t : ℂ)*I)‖ ≤
      signedMomentMass a N * (Real.log N * |u-t|) := by
  unfold signedDirichletPolynomial
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  rw [signedMomentMass, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  let l := Real.log (n+1)
  have hphase (w : ℝ) : ((w : ℂ)*I) * ((-l : ℝ) : ℂ) = ((-(w*l) : ℝ) : ℂ)*I := by
    push_cast
    ring
  rw [signedTerm_shift a (1/2) ((u : ℂ)*I) n,
    signedTerm_shift a (1/2) ((t : ℂ)*I) n, hphase u, hphase t, ← mul_sub, norm_mul,
    signedTerm_norm (by norm_num : (1/2 : ℂ).re = 1/2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (dottie_unit_phase_distance (-(u*l)) (-(t*l))).trans ?_
  have hl : 0 ≤ l := by
    apply Real.log_nonneg
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hN : (n+1 : ℝ) ≤ N := by exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hn)
  have hlog := Real.log_le_log (by positivity : (0:ℝ) < n+1) hN
  rw [show -(u*l) - -(t*l) = -(l*(u-t)) by ring, abs_neg, abs_mul, abs_of_nonneg hl]
  exact mul_le_mul_of_nonneg_right hlog (abs_nonneg _)

/-- The rational input used for finite arithmetic on the original signed
reference polynomial. Its height lies within the proved Dottie enclosure. -/
noncomputable def dottieRationalReferencePoint : ℂ := 1/2 + (4526119322477.943440197603 : ℂ)*I

private theorem reference_mass_le : signedMomentMass archivedLatticeCoeff 276824064 ≤ 33276 := by
  have hr : Nat.sqrt 276824064 = 16638 := by decide +kernel
  have h := archivedMomentMass_le_two_sqrt 276824064
  rw [hr] at h
  norm_num at h
  exact h

theorem dottie_reference_rational_height_error :
    ‖signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieReferencePoint -
      signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieRationalReferencePoint‖ < 1/200 := by
  let t : ℝ := 4526119322477.943440197603
  have ht : |(dottieHeight-1/512)-t| ≤ 73/10^10 := by
    apply abs_le.mpr
    obtain ⟨hl,hu⟩ := dottieHeight_enclosure
    dsimp only [t]
    constructor <;> linarith
  have hlog : Real.log 276824064 ≤ 20 := by
    have hp : (2.7 : ℝ)^20 ≤ Real.exp 20 := by
      rw [show (20:ℝ) = (20:ℕ)*(1:ℝ) by norm_num, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) _
    exact ((Real.log_lt_iff_lt_exp (by norm_num)).mpr
      ((by norm_num : (276824064:ℝ) < 2.7^20).trans_le hp)).le
  have h := signed_dirichlet_height_bound archivedLatticeCoeff 276824064 (dottieHeight-1/512) t
  refine h.trans_lt ?_
  have hprod : Real.log 276824064 * |(dottieHeight-1/512)-t| ≤ 20*(73/10^10) :=
    mul_le_mul hlog ht (abs_nonneg _) (by norm_num)
  have hnonneg : 0 ≤ Real.log 276824064*|(dottieHeight-1/512)-t| :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (abs_nonneg _)
  exact (mul_le_mul reference_mass_le hprod hnonneg (by norm_num)).trans_lt (by norm_num)

theorem dottie_reference_rational_norm_bound :
    ‖signedDirichletPolynomial archivedLatticeCoeff 276824064 dottieRationalReferencePoint‖ ≤ 33276 := by
  have hs : dottieRationalReferencePoint.re = 1/2 := by
    norm_num [dottieRationalReferencePoint, Complex.mul_re]
  unfold signedDirichletPolynomial
  refine (norm_sum_le _ _).trans ?_
  simp_rw [signedTerm_norm hs]
  exact reference_mass_le

#print axioms archivedMomentMass_le_two_sqrt
#print axioms dottie_unit_phase_distance
#print axioms signed_dirichlet_height_bound
#print axioms dottie_reference_rational_height_error
#print axioms dottie_reference_rational_norm_bound

end QuarticModel
