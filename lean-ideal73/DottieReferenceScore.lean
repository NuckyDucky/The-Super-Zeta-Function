import DottieReferenceWeights
import DottieTriangleScore

/-! The exact reference projection and a common-denominator score whose
weights are computable by integer arithmetic. -/

open Complex Finset

namespace QuarticModel

open private signedTerm from DottieSignedMoments
open private reference_mass_le from DottieHeightPerturbation

private noncomputable def referenceCosArgument (n : ℕ) : ℝ :=
  3.9229252 - 4526119322477.943440197603 * Real.log n

theorem dottieRationalReferenceProjection_eq_sum :
    dottieRationalReferenceProjection = ∑ n ∈ range 276824064,
      ((archivedLatticeCoeff (n+1) : ℝ)/Real.sqrt (n+1))*Real.cos (referenceCosArgument (n+1)) := by
  unfold dottieRationalReferenceProjection signedDirichletPolynomial
  rw [Finset.mul_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n _
  let l : ℝ := Real.log (n+1)
  have he : (3.9229252 : ℂ)*I + ((l : ℝ) : ℂ)*(-dottieRationalReferencePoint) =
      ((-l/2 : ℝ) : ℂ)+((referenceCosArgument (n+1) : ℝ) : ℂ)*I := by
    dsimp only [dottieRationalReferencePoint, referenceCosArgument, l]
    push_cast
    ring
  have hz : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  unfold signedTerm
  rw [Complex.cpow_def_of_ne_zero hz, ← Complex.natCast_log,
    mul_left_comm, ← Complex.exp_add]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [he, Complex.exp_add]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Real.cos_zero, Real.sin_zero, mul_one,
    mul_zero, Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im, Complex.I_re, Complex.I_im, sub_zero, zero_mul, add_zero,
    Real.exp_zero, one_mul, Complex.intCast_re, Complex.intCast_im]
  have hr : Real.exp (-l/2) = 1/Real.sqrt (n+1) := by
    have hn : 0 < (n+1:ℝ) := by positivity
    rw [show -l/2 = Real.log (n+1)*(-(1/2):ℝ) by dsimp [l]; ring,
      ← Real.rpow_def_of_pos hn, Real.rpow_neg hn.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hr]
  ring

/-- Numerator of a single weight in denominator `fixedCosScale^5`. -/
def dottieWeightTicks (n : ℕ) : ℤ :=
  (inverseSqrtTicks fixedCosScale n : ℤ)*dottieCosineTicks n

private theorem reference_weight_error (n : ℕ) (hn : 0 < n) (hcap : n ≤ 276824064) :
    |(dottieWeightTicks n : ℝ)/(fixedCosScale : ℝ)^5 -
      (1/Real.sqrt n)*Real.cos (referenceCosArgument n)| ≤ (1/900000)/Real.sqrt n := by
  let x : ℝ := (inverseSqrtTicks fixedCosScale n : ℝ)/fixedCosScale
  let y : ℝ := (dottieCosineTicks n : ℝ)/(fixedCosScale : ℝ)^4
  let a : ℝ := 1/Real.sqrt n
  let b : ℝ := Real.cos (referenceCosArgument n)
  have hS : 0 < (fixedCosScale:ℝ) := by norm_num [fixedCosScale]
  obtain ⟨hxa, hxa'⟩ := inverseSqrtTicks_spec fixedCosScale n (by decide +kernel) hn
  change x ≤ a at hxa
  rw [add_div] at hxa'
  change a < x + 1/(fixedCosScale:ℝ) at hxa'
  have hxp : 0 ≤ x := by positivity
  have hbx : |b| ≤ 1 := Real.abs_cos_le_one _
  have hby : |y-b| ≤ 1/1000000 := dottieCosineTicks_spec n hn hcap
  have habs : |x-a| ≤ 1/(fixedCosScale:ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hxa)]
    linarith only [hxa']
  have hn' : 0 < Real.sqrt n := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsmall : 1/(fixedCosScale:ℝ) ≤ (1/1000000000)*a := by
    have hnCap : Real.sqrt n ≤ (2:ℝ)^15 := by
      apply (Real.sqrt_le_left (by positivity)).2
      have h : (n:ℝ) ≤ 276824064 := by exact_mod_cast hcap
      exact h.trans (by norm_num)
    calc
      1/(fixedCosScale:ℝ) ≤ (1/1000000000)*(1/(2:ℝ)^15) := by norm_num [fixedCosScale]
      _ ≤ (1/1000000000)*a := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hn' hnCap) (by norm_num)
  have herror₁ : |x*(y-b)| ≤ a*(1/1000000) := by
    rw [abs_mul, abs_of_nonneg hxp]
    exact mul_le_mul hxa hby (abs_nonneg _) (hxp.trans hxa)
  have herror₂ : |(x-a)*b| ≤ (1/1000000000)*a := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_left hbx (abs_nonneg _)).trans_eq (mul_one _)).trans (habs.trans hsmall)
  have hre : (dottieWeightTicks n : ℝ)/(fixedCosScale : ℝ)^5 = x*y := by
    simp only [dottieWeightTicks, Int.cast_mul, Int.cast_natCast, x, y, div_mul_div_comm, pow_succ']
  rw [hre]
  change |x*y-a*b| ≤ _
  rw [show x*y-a*b = x*(y-b)+(x-a)*b by ring]
  rw [show (1:ℝ)/900000/Real.sqrt n = (1/900000)*a by dsimp only [a]; ring]
  exact (abs_add_le _ _).trans ((add_le_add herror₁ herror₂).trans (by linarith only [show 0 ≤ a by positivity]))

/-- The score weighted by the original signed coefficients. Its exact
integer evaluation is a separate certificate. -/
noncomputable def dottieReferenceScore : ℤ :=
  ∑ n ∈ range 276824064, archivedLatticeCoeff (n+1)*dottieWeightTicks (n+1)

/-- Executable form of the score, grouped by the real coordinate of each
original Gaussian lattice point. -/
def dottieReferenceScoreRows : ℤ := dottieTriangleScore 276824064 dottieWeightTicks

theorem dottieReferenceScoreRows_eq : dottieReferenceScoreRows = dottieReferenceScore :=
  dottieTriangleScore_eq_archivedLatticeCoeff _ _

theorem dottie_reference_score_error :
    |(dottieReferenceScore : ℝ)/(fixedCosScale:ℝ)^5-dottieRationalReferenceProjection| ≤ 1/25 := by
  have hScore : (dottieReferenceScore : ℝ)/(fixedCosScale:ℝ)^5 = ∑ n ∈ range 276824064,
      (archivedLatticeCoeff (n+1) : ℝ)*((dottieWeightTicks (n+1) : ℝ)/(fixedCosScale:ℝ)^5) := by
    rw [dottieReferenceScore, Int.cast_sum, Finset.sum_div]
    simp only [Int.cast_mul, mul_div_assoc]
  rw [hScore, dottieRationalReferenceProjection_eq_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : signedMomentMass archivedLatticeCoeff 276824064 ≤ 33276 := reference_mass_le
  calc
    _ ≤ (1/900000) * signedMomentMass archivedLatticeCoeff 276824064 := by
      rw [signedMomentMass, Finset.mul_sum]
      refine Finset.sum_le_sum (fun n hn => ?_)
      have hbound := reference_weight_error (n+1) (by omega) (Nat.succ_le_of_lt (mem_range.mp hn))
      let u : ℝ := (archivedLatticeCoeff (n+1) : ℝ)
      have e : u * ((dottieWeightTicks (n+1) : ℝ)/(fixedCosScale:ℝ)^5) -
        u/Real.sqrt (n+1)*Real.cos (referenceCosArgument (n+1)) =
        u*((dottieWeightTicks (n+1) : ℝ)/(fixedCosScale:ℝ)^5 -
          (1/Real.sqrt (n+1))*Real.cos (referenceCosArgument (n+1))) := by ring
      change |u * ((dottieWeightTicks (n+1) : ℝ)/(fixedCosScale:ℝ)^5) -
        u/Real.sqrt (n+1)*Real.cos (referenceCosArgument (n+1))| ≤ (1/900000)*(|u|/Real.sqrt (n+1))
      rw [e, abs_mul]
      simp only [Nat.cast_add, Nat.cast_one] at hbound
      exact (mul_le_mul_of_nonneg_left hbound (abs_nonneg u)).trans_eq (by ring)
    _ ≤ (1/900000)*33276 := mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 1/25 := by norm_num

private theorem rational_projection_gt_of_score {score : ℤ} {p : ℝ}
    (he : |(score : ℝ)/(fixedCosScale:ℝ)^5-p| ≤ 1/25)
    (hs : 7*(fixedCosScale:ℤ)^5 < 50*score) : 1/10 < p := by
  have hb : (0:ℝ) < (fixedCosScale:ℝ)^5 := by norm_num [fixedCosScale]
  have hc : 7 * (fixedCosScale:ℝ)^5 < 50*(score:ℝ) := by exact_mod_cast hs
  have hd : (7:ℝ)/50 < (score:ℝ)/(fixedCosScale:ℝ)^5 := by
    apply (lt_div_iff₀ hb).2
    linarith only [hc]
  linarith only [hd, (abs_le.mp he).2]

/-- A single integer inequality certifies positivity of the original
reference unit, including phase reduction and all weight rounding. -/
theorem dottieCircleReference_pos_of_score
    (h : 7*(fixedCosScale:ℤ)^5 < 50*dottieReferenceScore) : 0 < dottieCircleReference :=
  dottieCircleReference_pos_of_rational_projection (rational_projection_gt_of_score dottie_reference_score_error h)

theorem dottieCircleReference_pos_of_row_score
    (h : 7*(fixedCosScale:ℤ)^5 < 50*dottieReferenceScoreRows) : 0 < dottieCircleReference :=
  dottieCircleReference_pos_of_score (dottieReferenceScoreRows_eq ▸ h)

#print axioms dottieRationalReferenceProjection_eq_sum
#print axioms dottieReferenceScoreRows_eq
#print axioms dottie_reference_score_error
#print axioms dottieCircleReference_pos_of_score
#print axioms dottieCircleReference_pos_of_row_score

end QuarticModel
