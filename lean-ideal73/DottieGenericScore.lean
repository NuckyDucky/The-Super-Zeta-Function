import DottieReferenceScore

namespace QuarticModel

open Finset
open private referenceCosArgument rational_projection_gt_of_score from DottieReferenceScore
open private reference_mass_le from DottieHeightPerturbation

/-- Any weights with the certified per-norm accuracy give the same error
budget for the rational reference projection. -/
theorem dottie_generic_score_error (f : ℕ → ℤ)
    (hweight : ∀ n : ℕ, 0 < n → n ≤ 276824064 →
      |(f n : ℝ)/(fixedCosScale : ℝ)^5 -
        (1/Real.sqrt n)*Real.cos (referenceCosArgument n)| ≤ (1/900000)/Real.sqrt n) :
    |(dottieTriangleScore 276824064 f : ℝ)/(fixedCosScale : ℝ)^5 -
      dottieRationalReferenceProjection| ≤ 1/25 := by
  have hscore : (dottieTriangleScore 276824064 f : ℝ)/(fixedCosScale : ℝ)^5 =
      ∑ n ∈ range 276824064,
        (archivedLatticeCoeff (n+1) : ℝ)*((f (n+1) : ℝ)/(fixedCosScale : ℝ)^5) := by
    rw [dottieTriangleScore_eq_archivedLatticeCoeff, Int.cast_sum, Finset.sum_div]
    simp only [Int.cast_mul, mul_div_assoc]
  rw [hscore, dottieRationalReferenceProjection_eq_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ (1/900000) * signedMomentMass archivedLatticeCoeff 276824064 := by
      rw [signedMomentMass, Finset.mul_sum]
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hbound := hweight (n+1) (Nat.succ_pos n) (Nat.succ_le_of_lt (mem_range.mp hn))
      let c : ℝ := (archivedLatticeCoeff (n+1) : ℝ)
      have he : c * ((f (n+1) : ℝ)/(fixedCosScale : ℝ)^5) -
          c/Real.sqrt (n+1)*Real.cos (referenceCosArgument (n+1)) =
        c*((f (n+1) : ℝ)/(fixedCosScale : ℝ)^5 -
          (1/Real.sqrt (n+1))*Real.cos (referenceCosArgument (n+1))) := by ring
      change |c * ((f (n+1) : ℝ)/(fixedCosScale : ℝ)^5) -
          c/Real.sqrt (n+1)*Real.cos (referenceCosArgument (n+1))| ≤
        (1/900000)*(|c|/Real.sqrt (n+1))
      rw [he, abs_mul]
      simp only [Nat.cast_add, Nat.cast_one] at hbound
      exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg c)).trans_eq (by ring)
    _ ≤ (1/900000)*33276 := mul_le_mul_of_nonneg_left reference_mass_le (by norm_num)
    _ ≤ 1/25 := by norm_num

/-- The original integer threshold suffices for any weights with the same
per-norm error. -/
theorem dottieCircleReference_pos_of_generic_score (f : ℕ → ℤ)
    (hweight : ∀ n : ℕ, 0 < n → n ≤ 276824064 →
      |(f n : ℝ)/(fixedCosScale : ℝ)^5 -
        (1/Real.sqrt n)*Real.cos (referenceCosArgument n)| ≤ (1/900000)/Real.sqrt n)
    (hscore : 7*(fixedCosScale : ℤ)^5 < 50*dottieTriangleScore 276824064 f) :
    0 < dottieCircleReference :=
  dottieCircleReference_pos_of_rational_projection
    (rational_projection_gt_of_score (dottie_generic_score_error f hweight) hscore)

#print axioms dottie_generic_score_error
#print axioms dottieCircleReference_pos_of_generic_score

end QuarticModel
