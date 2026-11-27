import ComplexMellinFoldEstimates
import DedekindDiscriminant23CharacterPolynomial
import DedekindDiscriminant23CompletedProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace FieldTarget

open Complex MeasureTheory NumberField Set
open scoped Interval NumberField

noncomputable section

private def heat (x : ℝ) : ℝ := Real.exp (-discriminant23ThetaScale * x)

private def thetaDifference (q : ℝ) : ℝ :=
  classThetaStar discriminant23PrincipalForm q - classThetaStar discriminant23OtherForm q

private def radialFold (w : ℂ) (x : ℝ) : ℂ :=
  foldedMellinWeight w x * (thetaDifference (heat x) : ℂ)

private def polynomialKernel (x : ℝ) : ℂ :=
  (discriminant23CharacterPolynomial (heat x) : ℂ)

private def radialModel (w : ℂ) (x : ℝ) : ℂ :=
  foldedMellinWeight w x * polynomialKernel x

private theorem radialFold_integrable_and_eq (w : ℂ) :
    IntegrableOn (radialFold w) (Ioi 1) ∧
      discriminant23CharacterFold w = ∫ x in Ioi 1, radialFold w x := by
  let F := (discriminant23QuadraticSubfield : Type)
  let c := discriminant23NormTwoClass
  let g (x : ℝ) :=
    discriminant23FoldWeight w x * discriminant23ClassKernel (1 : ClassGroup (𝓞 F)) x -
    discriminant23FoldWeight w x * discriminant23ClassKernel c x
  have hp := discriminant23_fold_integrable (1 : ClassGroup (𝓞 F)) w
  have hn := discriminant23_fold_integrable c w
  have hEq (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) : g x = radialFold w x := by
    dsimp only [g, c, F]
    rw [← mul_sub, radialFold, foldedMellinWeight_eq_cpow w (zero_lt_one.trans hx)]
    simp [discriminant23FoldWeight, discriminant23ClassKernel, discriminant23_normTwoClass_ne_one,
      thetaDifference, heat]
  refine ⟨(hp.sub hn).congr_fun hEq measurableSet_Ioi, ?_⟩
  rw [discriminant23CharacterFold, discriminant23_classLambdaZero_eq_fold,
    discriminant23_classLambdaZero_eq_fold, ← integral_sub hp hn]
  exact setIntegral_congr_fun measurableSet_Ioi hEq

private theorem heat_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ heat x ∧ heat x ≤ 3 / 11 ∧ heat x ≤ Real.exp (-(13 / 10 : ℝ) * x) := by
  have ha := discriminant23_thetaScale_interval.1
  have hax : -discriminant23ThetaScale * x ≤ -discriminant23ThetaScale := by
    nlinarith [mul_nonneg (show 0 ≤ discriminant23ThetaScale by linarith) (sub_nonneg.mpr hx)]
  exact ⟨(Real.exp_pos _).le, (Real.exp_le_exp.mpr hax).trans discriminant23_thetaExp_interval.2,
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg ha) (by linarith))⟩

private theorem weight_norm_le {w : ℂ} (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2)
    {x : ℝ} (hx : 1 ≤ x) : ‖foldedMellinWeight w x‖ ≤ 2 * x := by
  simpa only [Real.rpow_one] using
    foldedMellinWeight_norm_le hx hlo (by linarith only [hhi])

private theorem exp_one_lower : (8 / 3 : ℝ) ≤ Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

private theorem exp_neg_one_upper : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
  rw [Real.exp_neg, ← one_div, show (3 / 8 : ℝ) = 1 / (8 / 3) by norm_num]
  exact one_div_le_one_div_of_le (by norm_num) exp_one_lower

private theorem exp_three_lower : (18 : ℝ) ≤ Real.exp 3 := by
  have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith only [h]

private theorem decay_bound (x : ℝ) :
    x * Real.exp (-(13 / 10 : ℝ) * x) ≤ (5 / 4) * Real.exp (-x) := by
  have hLinear : (3 / 10 : ℝ) * x ≤ Real.exp ((3 / 10 : ℝ) * x - 1) := by
    linarith only [Real.add_one_le_exp ((3 / 10 : ℝ) * x - 1)]
  have hWeighted := mul_le_mul_of_nonneg_right hLinear (Real.exp_nonneg (-(13 / 10 : ℝ) * x))
  rw [← Real.exp_add, show (3 / 10 : ℝ) * x - 1 + -(13 / 10 : ℝ) * x = -1 + -x by ring,
    Real.exp_add] at hWeighted
  have hBound := mul_le_mul_of_nonneg_right exp_neg_one_upper (Real.exp_nonneg (-x))
  linarith only [hWeighted, hBound]

private theorem radialFold_norm_le_heat {w : ℂ} (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2)
    {x : ℝ} (hx : 1 ≤ x) : ‖radialFold w x‖ ≤ (21 / 5) * (x * Real.exp (-(13 / 10 : ℝ) * x)) := by
  obtain ⟨hq₀, hq₁, hq₂⟩ := heat_bounds hx
  obtain ⟨hp₀, hp₁, hn₀, hn₁⟩ := discriminant23_classThetaStar_bounds hq₀ hq₁
  have hθ₀ : 0 ≤ thetaDifference (heat x) := by dsimp [thetaDifference]; linarith only [hp₀, hn₁, hq₀]
  have hθ₁ : thetaDifference (heat x) ≤ (21 / 10) * heat x := by
    dsimp [thetaDifference]; linarith only [hp₁, hn₀]
  rw [radialFold, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hθ₀]
  calc
    _ ≤ (2 * x) * ((21 / 10) * heat x) :=
      mul_le_mul (weight_norm_le hlo hhi hx) hθ₁ hθ₀ (by linarith only [hx])
    _ ≤ (2 * x) * ((21 / 10) * Real.exp (-(13 / 10 : ℝ) * x)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq₂ (by norm_num)) (by linarith only [hx])
    _ = (21 / 5) * (x * Real.exp (-(13 / 10 : ℝ) * x)) := by ring

private theorem radialError_norm_le {w : ℂ} (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2)
    {P : ℝ → ℝ} {order : ℕ} (hOrder : 0 < order) {x : ℝ} (hx : 1 ≤ x)
    (hP : |thetaDifference (heat x) - P (heat x)| ≤ 16 * heat x ^ order) :
    ‖radialFold w x - foldedMellinWeight w x * (P (heat x) : ℂ)‖ ≤
      (40 * (3 / 11 : ℝ) ^ (order - 1)) * Real.exp (-x) := by
  obtain ⟨hq₀, hq₁, hq₂⟩ := heat_bounds hx
  have hqPower : heat x ^ order ≤ (3 / 11 : ℝ) ^ (order - 1) * Real.exp (-(13 / 10 : ℝ) * x) := by
    calc
      _ = heat x ^ (order - 1) * heat x := by rw [← pow_succ, Nat.sub_add_cancel hOrder]
      _ ≤ _ := mul_le_mul (pow_le_pow_left₀ hq₀ hq₁ _) hq₂ hq₀ (by positivity)
  rw [radialFold, ← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ (2 * x) * (16 * heat x ^ order) :=
      mul_le_mul (weight_norm_le hlo hhi hx) hP (abs_nonneg _) (by linarith only [hx])
    _ ≤ (32 * (3 / 11 : ℝ) ^ (order - 1)) * (x * Real.exp (-(13 / 10 : ℝ) * x)) := by
      have h := mul_le_mul_of_nonneg_left hqPower (show 0 ≤ (2 * x) * 16 by linarith only [hx])
      linarith only [h]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (decay_bound x)
        (by positivity : (0 : ℝ) ≤ 32 * (3 / 11) ^ (order - 1))
      convert h using 1
      ring

private theorem radialFold_far_norm_le {w : ℂ} (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2)
    {x : ℝ} (hx : 1 ≤ x) : ‖radialFold w x‖ ≤
      (63 / 2) * Real.exp (-(5 / 4 : ℝ) * x) := by
  have hInc : (1 / 20 : ℝ) * x ≤ Real.exp ((1 / 20 : ℝ) * x - 1) := by
    linarith only [Real.add_one_le_exp ((1 / 20 : ℝ) * x - 1)]
  have h := mul_le_mul_of_nonneg_right hInc (Real.exp_nonneg (-(13 / 10 : ℝ) * x))
  rw [← Real.exp_add, show (1 / 20 : ℝ) * x - 1 + -(13 / 10 : ℝ) * x =
    -1 + -(5 / 4 : ℝ) * x by ring, Real.exp_add] at h
  have hNeg := mul_le_mul_of_nonneg_right exp_neg_one_upper
    (Real.exp_nonneg (-(5 / 4 : ℝ) * x))
  have hf := radialFold_norm_le_heat hlo hhi hx
  linarith only [hf, h, hNeg]

private theorem polynomialKernel_continuous : Continuous polynomialKernel := by
  unfold polynomialKernel discriminant23CharacterPolynomial heat
  fun_prop

private theorem log_continuousOn_positive :
    ContinuousOn (fun x : ℝ ↦ (Real.log x : ℂ)) (Ioi 0) :=
  Complex.continuous_ofReal.comp_continuousOn fun _ hx ↦
    (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt

private theorem weightedKernel_continuousOn (w : ℂ) {K : ℝ → ℂ} (hK : Continuous K) :
    ContinuousOn (fun x ↦ foldedMellinWeight w x * K x) (Ioi 0) := by
  unfold foldedMellinWeight
  exact ((Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul log_continuousOn_positive)).add
    (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul log_continuousOn_positive))).mul
    hK.continuousOn

private theorem weightedKernel_integral_eq_log {f : ℝ → ℂ}
    (hf : ContinuousOn f (Ioi 0)) (L : ℝ) :
    (∫ x in (1 : ℝ)..Real.exp L, f x) =
      ∫ u in (0 : ℝ)..L, (Real.exp u : ℂ) * f (Real.exp u) := by
  have hc : ContinuousOn f (Real.exp '' [[(0 : ℝ), L]]) :=
    hf.mono (by rintro _ ⟨u, _, rfl⟩; exact Real.exp_pos u)
  have h := intervalIntegral.integral_deriv_smul_comp' (a := (0 : ℝ)) (b := L)
    (fun u _ ↦ Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn hc
  rw [Real.exp_zero] at h
  simpa only [Function.comp_apply, Complex.real_smul] using h.symm

private theorem exp_mul_foldedMellinWeight (w : ℂ) (u : ℝ) :
    (Real.exp u : ℂ) * foldedMellinWeight w (Real.exp u) =
      Complex.exp (w * (u : ℂ)) + Complex.exp ((1 - w) * (u : ℂ)) := by
  rw [foldedMellinWeight, Real.log_exp, Complex.ofReal_exp,
    mul_add, ← Complex.exp_add, ← Complex.exp_add,
    show (u : ℂ) + (w - 1) * (u : ℂ) = w * (u : ℂ) by ring,
    show (u : ℂ) + -w * (u : ℂ) = (1 - w) * (u : ℂ) by ring]

private theorem exp_mul_foldedMellinWeightDeriv (w : ℂ) (u : ℝ) :
    (Real.exp u : ℂ) * foldedMellinWeightDeriv w (Real.exp u) =
      (u : ℂ) * (Complex.exp (w * (u : ℂ)) - Complex.exp ((1 - w) * (u : ℂ))) := by
  rw [foldedMellinWeightDeriv, Real.log_exp, Complex.ofReal_exp,
    mul_left_comm (Complex.exp (u : ℂ)), mul_sub, ← Complex.exp_add, ← Complex.exp_add,
    show (u : ℂ) + (w - 1) * (u : ℂ) = w * (u : ℂ) by ring,
    show (u : ℂ) + -w * (u : ℂ) = (1 - w) * (u : ℂ) by ring]

/-- The compact logarithmic integrand for the complex character reading. -/
def discriminant23CharacterComplexIntegrand (w : ℂ) (u : ℝ) : ℂ :=
  (Complex.exp (w * (u : ℂ)) + Complex.exp ((1 - w) * (u : ℂ))) *
    (discriminant23CharacterPolynomial (heat (Real.exp u)) : ℂ)

/-- Retain the same theta polynomial as in the height bracket and integrate
it over the compact logarithmic interval. -/
def discriminant23CharacterComplexModel (w : ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..3, discriminant23CharacterComplexIntegrand w u

private theorem complexModel_eq_radial (w : ℂ) :
    discriminant23CharacterComplexModel w = ∫ x in (1 : ℝ)..Real.exp 3, radialModel w x := by
  have h := weightedKernel_integral_eq_log (weightedKernel_continuousOn w polynomialKernel_continuous) 3
  change (∫ u in (0 : ℝ)..3, discriminant23CharacterComplexIntegrand w u) =
    ∫ x in (1 : ℝ)..Real.exp 3, foldedMellinWeight w x * polynomialKernel x
  rw [h]
  apply intervalIntegral.integral_congr
  intro u _
  beta_reduce
  rw [← mul_assoc, exp_mul_foldedMellinWeight]
  rfl

private theorem complexModel_eq_folded :
    discriminant23CharacterComplexModel = foldedMellinTruncation polynomialKernel (Real.exp 3) :=
  funext complexModel_eq_radial

theorem discriminant23_characterComplexModel_differentiable :
    Differentiable ℂ discriminant23CharacterComplexModel := by
  rw [complexModel_eq_folded]
  exact foldedMellinTruncation_differentiable (by linarith only [exp_three_lower])
    (polynomialKernel_continuous.intervalIntegrable _ _)


private theorem exp_far_bound_sharp :
    Real.exp (-(5 / 4 : ℝ) * Real.exp 3) ≤ (3 / 8 : ℝ) ^ 25 := by
  have hR : (20 : ℝ) ≤ Real.exp 3 := by
    have h := Real.sum_le_exp_of_nonneg (x := (3 : ℝ)) (by norm_num) 9
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith only [h]
  refine (Real.exp_le_exp.mpr (by linarith only [hR] : -(5 / 4 : ℝ) * Real.exp 3 ≤ -25)).trans ?_
  rw [show (-25 : ℝ) = (25 : ℕ) * (-1) by norm_num, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_one_upper 25

private theorem integrableOn_exp_neg (R c : ℝ) :
    IntegrableOn (fun x : ℝ ↦ c * Real.exp (-x)) (Ioi R) := by
  unfold IntegrableOn
  simpa only [neg_one_mul] using
    (integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) R).const_mul c

private theorem integral_exp_neg (R c : ℝ) :
    (∫ x : ℝ in Ioi R, c * Real.exp (-x)) = c * Real.exp (-R) := by
  rw [integral_const_mul]
  congr 1
  simpa only [neg_one_mul, div_neg, div_one, neg_neg] using
    (integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) R)

private theorem radialTruncation_error {w : ℂ} {R A : ℝ} {K : ℝ → ℂ}
    (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2) (hR : 1 ≤ R) (hA : 0 ≤ A) (hK : Continuous K)
    (hLocal : ∀ x : ℝ, 1 ≤ x → ‖radialFold w x - foldedMellinWeight w x * K x‖ ≤ A * Real.exp (-x)) :
    ‖discriminant23CharacterFold w - foldedMellinTruncation K R w‖ ≤
      A * (3 / 8) + (126 / 5) * Real.exp (-(5 / 4 : ℝ) * R) := by
  obtain ⟨hFull, hEq⟩ := radialFold_integrable_and_eq w
  have hSubset : Ioc (1 : ℝ) R ⊆ Ioi 1 := fun _ hx ↦ hx.1
  have hFin := (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr (hFull.mono_set hSubset)
  have hPos : Icc (1 : ℝ) R ⊆ Ioi 0 := fun _ hx ↦ zero_lt_one.trans_le hx.1
  have hModel := ((weightedKernel_continuousOn w hK).mono hPos).intervalIntegrable_of_Icc (μ := volume) hR
  let major (x : ℝ) := A * Real.exp (-x)
  have hMajor : IntegrableOn major (Ioi 1) := integrableOn_exp_neg 1 _
  have hError : ‖(∫ x in (1 : ℝ)..R, radialFold w x) -
      (∫ x in (1 : ℝ)..R, foldedMellinWeight w x * K x)‖ ≤ A * (3 / 8) := by
    rw [← intervalIntegral.integral_sub hFin hModel, intervalIntegral.integral_of_le hR]
    have hBound := norm_integral_le_of_norm_le (f := fun x ↦ radialFold w x - foldedMellinWeight w x * K x)
      (hMajor.mono_set hSubset)
      ((ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦ hLocal x hx.1.le)
    have hSub := setIntegral_mono_set hMajor
      (ae_of_all _ (fun x ↦ mul_nonneg hA (Real.exp_nonneg (-x)))) (Filter.Eventually.of_forall hSubset)
    refine hBound.trans (hSub.trans ?_)
    change (∫ x in Ioi (1 : ℝ), A * Real.exp (-x)) ≤ _
    rw [integral_exp_neg]
    exact mul_le_mul_of_nonneg_left exp_neg_one_upper hA
  have hTail : ‖∫ x in Ioi R, radialFold w x‖ ≤ (126 / 5) * Real.exp (-(5 / 4 : ℝ) * R) := by
    have hi : IntegrableOn (fun x : ℝ ↦ (63 / 2 : ℝ) * Real.exp (-(5 / 4 : ℝ) * x)) (Ioi R) :=
      (integrableOn_exp_mul_Ioi (a := -(5 / 4 : ℝ)) (by norm_num) R).const_mul _
    refine (norm_integral_le_of_norm_le (f := radialFold w) hi
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦
        radialFold_far_norm_le hlo hhi (hR.trans hx.le))).trans_eq ?_
    rw [integral_const_mul, integral_exp_mul_Ioi (a := -(5 / 4 : ℝ)) (by norm_num) R]
    ring
  rw [hEq, foldedMellinTruncation,
    ← intervalIntegral.integral_interval_add_Ioi hFull (hFull.mono_set (Ioi_subset_Ioi hR)),
    add_sub_right_comm]
  exact (norm_add_le _ _).trans (add_le_add hError hTail)

private def characterKernelUpTo (N : ℕ) (x : ℝ) : ℂ :=
  (discriminant23CharacterPolynomialUpTo N (heat x) : ℝ)

private theorem characterKernelUpTo_continuous (N : ℕ) : Continuous (characterKernelUpTo N) := by
  unfold characterKernelUpTo discriminant23CharacterPolynomialUpTo heat
  fun_prop

/-- R is the radial cutoff and N is the largest retained lattice norm. -/
def discriminant23CharacterModelUpTo (N : ℕ) (R : ℝ) : ℂ → ℂ :=
  foldedMellinTruncation (characterKernelUpTo N) R

def discriminant23CharacterModelError (order : ℕ) (R : ℝ) : ℝ :=
  15 * (3 / 11) ^ (order - 1) + (126 / 5) * Real.exp (-(5 / 4 : ℝ) * R)

theorem discriminant23_characterModelUpTo_differentiable (N : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    Differentiable ℂ (discriminant23CharacterModelUpTo N R) :=
  foldedMellinTruncation_differentiable hR ((characterKernelUpTo_continuous N).intervalIntegrable _ _)

theorem discriminant23_characterModelUpTo_eq_logIntegral (N : ℕ) (L : ℝ) (w : ℂ) :
    discriminant23CharacterModelUpTo N (Real.exp L) w =
      ∫ u in (0 : ℝ)..L,
        (Complex.exp (w * (u : ℂ)) + Complex.exp ((1 - w) * (u : ℂ))) *
          (discriminant23CharacterPolynomialUpTo N (Real.exp (-discriminant23ThetaScale * Real.exp u)) : ℝ) := by
  rw [discriminant23CharacterModelUpTo, foldedMellinTruncation,
    weightedKernel_integral_eq_log (weightedKernel_continuousOn w (characterKernelUpTo_continuous N))]
  apply intervalIntegral.integral_congr
  intro u _
  beta_reduce
  rw [← mul_assoc, exp_mul_foldedMellinWeight]
  rfl

theorem discriminant23_characterModelUpTo_deriv_eq_logIntegral (N : ℕ) {L : ℝ} (hL : 0 ≤ L) (w : ℂ) :
    deriv (discriminant23CharacterModelUpTo N (Real.exp L)) w =
      ∫ u in (0 : ℝ)..L,
        (u : ℂ) * (Complex.exp (w * (u : ℂ)) - Complex.exp ((1 - w) * (u : ℂ))) *
          (discriminant23CharacterPolynomialUpTo N (Real.exp (-discriminant23ThetaScale * Real.exp u)) : ℝ) := by
  have hR : 1 ≤ Real.exp L := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hL
  have h := foldedMellinTruncation_hasDerivAt (f := characterKernelUpTo N) hR
    ((characterKernelUpTo_continuous N).intervalIntegrable _ _) w
  change deriv (foldedMellinTruncation (characterKernelUpTo N) (Real.exp L)) w = _
  rw [h.deriv]
  have hc : ContinuousOn (fun x ↦ foldedMellinWeightDeriv w x * characterKernelUpTo N x) (Ioi 0) := by
    unfold foldedMellinWeightDeriv
    have hLog := log_continuousOn_positive
    exact (hLog.mul ((Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hLog)).sub
      (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hLog)))).mul
      (characterKernelUpTo_continuous N).continuousOn
  rw [weightedKernel_integral_eq_log hc]
  apply intervalIntegral.integral_congr
  intro u _
  beta_reduce
  rw [← mul_assoc, exp_mul_foldedMellinWeightDeriv]
  rfl

theorem discriminant23_characterModelUpTo_error {N order : ℕ} {R : ℝ} {w : ℂ}
    (hOrder : 0 < order) (hCut : 18 * order + 9 ≤ 13 * (N + 1)) (hR : 1 ≤ R)
    (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2) :
    ‖discriminant23CharacterFold w - discriminant23CharacterModelUpTo N R w‖ ≤
      discriminant23CharacterModelError order R := by
  have h := radialTruncation_error (K := characterKernelUpTo N)
    (A := 40 * (3 / 11 : ℝ) ^ (order - 1)) hlo hhi hR (by positivity) (characterKernelUpTo_continuous N)
    (fun x hx ↦ by
      obtain ⟨hq, hqu, _⟩ := heat_bounds hx
      exact radialError_norm_le hlo hhi hOrder hx
        (discriminant23_characterPolynomialUpTo_error hOrder hCut hq hqu))
  exact h.trans_eq (by unfold discriminant23CharacterModelError; ring)

theorem discriminant23_characterModelUpTo_iteratedDeriv_error (n : ℕ) {N order : ℕ} {R : ℝ} {w : ℂ}
    (hOrder : 0 < order) (hCut : 18 * order + 9 ≤ 13 * (N + 1)) (hR : 1 ≤ R)
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖iteratedDeriv n discriminant23CharacterFold w -
      iteratedDeriv n (discriminant23CharacterModelUpTo N R) w‖ ≤
      n.factorial * discriminant23CharacterModelError order R := by
  have h := iteratedDeriv_error_le_of_strip discriminant23CharacterFold_differentiable
    (discriminant23_characterModelUpTo_differentiable N hR) n (ρ := 1) (by norm_num)
    (fun z h₀ h₁ ↦ discriminant23_characterModelUpTo_error hOrder hCut hR
      (w := z) h₀ (by linarith only [h₁])) hlo hhi
  simpa only [one_pow, div_one] using h

/-- The previous fixed error is recovered at norm 32 and log cutoff 3. -/
theorem discriminant23_characterComplexModel_error_sharp {w : ℂ}
    (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2) :
    ‖discriminant23CharacterFold w - discriminant23CharacterComplexModel w‖ ≤ 1 / 10 ^ 9 := by
  have hR : (1 : ℝ) ≤ Real.exp 3 := by linarith only [exp_three_lower]
  have h := discriminant23_characterModelUpTo_error (N := 32) (order := 23) (w := w)
    (by decide) (by decide) hR hlo hhi
  have hk : characterKernelUpTo 32 = polynomialKernel := by
    funext x
    simp only [characterKernelUpTo, polynomialKernel, discriminant23_characterPolynomialUpTo_thirtyTwo]
  have hOld : discriminant23CharacterModelUpTo 32 (Real.exp 3) w =
      discriminant23CharacterComplexModel w := by
    rw [discriminant23CharacterModelUpTo, hk, complexModel_eq_folded]
  rw [hOld] at h
  refine h.trans ?_
  unfold discriminant23CharacterModelError
  calc
    _ ≤ 15 * (3 / 11 : ℝ) ^ (23 - 1 : ℕ) + (126 / 5) * (3 / 8 : ℝ) ^ 25 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left exp_far_bound_sharp (by norm_num : (0 : ℝ) ≤ 126 / 5))
    _ ≤ _ := by norm_num

#print axioms discriminant23_characterModelUpTo_eq_logIntegral
#print axioms discriminant23_characterModelUpTo_deriv_eq_logIntegral
#print axioms discriminant23_characterModelUpTo_error
#print axioms discriminant23_characterModelUpTo_iteratedDeriv_error

theorem discriminant23_characterComplexModel_iteratedDeriv_error_sharp (n : ℕ) {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖iteratedDeriv n discriminant23CharacterFold w -
      iteratedDeriv n discriminant23CharacterComplexModel w‖ ≤ n.factorial / 10 ^ 9 := by
  have h := iteratedDeriv_error_le_of_strip discriminant23CharacterFold_differentiable
    discriminant23_characterComplexModel_differentiable n (ρ := 1) (by norm_num)
    (fun z h₀ h₁ ↦ discriminant23_characterComplexModel_error_sharp
      (w := z) h₀ (by linarith only [h₁])) hlo hhi
  simpa only [one_pow, div_one, mul_one_div] using h

theorem discriminant23_characterComplexModel_error {w : ℂ}
    (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2) :
    ‖discriminant23CharacterFold w - discriminant23CharacterComplexModel w‖ ≤ 1 / 100000 :=
  (discriminant23_characterComplexModel_error_sharp hlo hhi).trans (by norm_num)

theorem discriminant23_characterComplexModel_iteratedDeriv_error (n : ℕ) {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖iteratedDeriv n discriminant23CharacterFold w -
      iteratedDeriv n discriminant23CharacterComplexModel w‖ ≤ n.factorial / 100000 := by
  refine (discriminant23_characterComplexModel_iteratedDeriv_error_sharp n hlo hhi).trans ?_
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)

#print axioms discriminant23_characterComplexModel_error_sharp
#print axioms discriminant23_characterComplexModel_iteratedDeriv_error_sharp

#check @discriminant23_characterComplexModel_error
#check @discriminant23_characterComplexModel_iteratedDeriv_error
#print axioms discriminant23_characterComplexModel_error
#print axioms discriminant23_characterComplexModel_iteratedDeriv_error

end
end FieldTarget
