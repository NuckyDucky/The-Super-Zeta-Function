import DedekindDiscriminant23DottieReading
import ComplexMellinFoldEstimates
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace FieldTarget

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

private def classHeat (x : ℝ) : ℝ :=
  Real.exp (-discriminant23ThetaScale * x)

private def classKernel (b x : ℝ) : ℝ :=
  classThetaStar discriminant23PrincipalForm (classHeat x) +
    b * classThetaStar discriminant23OtherForm (classHeat x)

/-- The principal class and a real multiple of one nonprincipal class,
with the same normalization as the Dottie class readings. -/
def discriminant23ClassCombinationReading (b : ℝ) (w : ℂ) : ℂ :=
  classMellinReading (fun t ↦ classKernel b (1 + t)) w

theorem discriminant23_classCombinationReading_two (w : ℂ) :
    discriminant23ClassCombinationReading 2 w = discriminant23TotalClassReading w := rfl

theorem discriminant23_classCombinationReading_neg_one (w : ℂ) :
    discriminant23ClassCombinationReading (-1) w = discriminant23CharacterClassReading w := by
  change classMellinReading (fun t ↦ classKernel (-1) (1 + t)) w =
    classMellinReading (fun t ↦ classThetaStar discriminant23PrincipalForm (classHeat (1 + t)) -
      classThetaStar discriminant23OtherForm (classHeat (1 + t))) w
  simp only [classKernel, neg_one_mul, sub_eq_add_neg]

/-- Retain all nonzero lattice points of norm at most N. The complex argument
lets us use the same polynomial on the quadrature circles. -/
def discriminant23ClassCombinationPolynomial (b : ℝ) (N : ℕ) (q : ℂ) : ℂ :=
  (∑ p ∈ characterThetaTermsUpTo discriminant23PrincipalForm N,
    q ^ (discriminant23PrincipalForm p.1 p.2).toNat) +
  (b : ℂ) * (∑ p ∈ characterThetaTermsUpTo discriminant23OtherForm N,
    q ^ (discriminant23OtherForm p.1 p.2).toNat)

def discriminant23ClassCombinationIntegrand (b : ℝ) (N : ℕ) (w z : ℂ) : ℂ :=
  (Complex.exp ((w - 1) * z) + Complex.exp (-w * z)) *
    (Complex.exp z * discriminant23ClassCombinationPolynomial b N
      (Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)))

private theorem classCombination_as_radial (b : ℝ) (w : ℂ) :
    2 * discriminant23ClassCombinationReading b w =
      ∫ x : ℝ in Ioi 1, foldedMellinWeight w x * (classKernel b x : ℂ) := by
  let f : ℝ → ℂ := fun x ↦ foldedMellinWeight w x * (classKernel b x : ℂ)
  have h := (measurePreserving_add_right volume (1 : ℝ)).setIntegral_preimage_emb
    (Homeomorph.addRight (1 : ℝ)).measurableEmbedding f (Ioi 1)
  have hSet : (fun x : ℝ ↦ x + 1) ⁻¹' Ioi 1 = Ioi 0 := by
    ext x
    change 1 < x + 1 ↔ 0 < x
    constructor <;> intro hx <;> linarith
  rw [hSet] at h
  change _ = ∫ x : ℝ in Ioi 1, f x
  rw [← h, discriminant23ClassCombinationReading, classMellinReading, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [f, classMellinWeight, foldedMellinWeight, add_comm t 1]
  ring

private theorem classHeat_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ classHeat x ∧ classHeat x ≤ 3 / 11 ∧
      classHeat x ≤ Real.exp (-(13 / 10 : ℝ) * x) := by
  have hScale := discriminant23_thetaScale_interval.1
  have hPos : 0 ≤ discriminant23ThetaScale := by linarith only [hScale]
  have hLower := mul_le_mul_of_nonneg_left hx (show 0 ≤ discriminant23ThetaScale from hPos)
  refine ⟨(Real.exp_pos _).le, ?_, ?_⟩
  · exact (Real.exp_le_exp.mpr (by linarith only [hLower])).trans
      discriminant23_thetaExp_interval.2
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hScale)
      (zero_le_one.trans hx))

private theorem abs_classKernel_le {b x : ℝ} (hb : |b| ≤ 2) (hx : 1 ≤ x) :
    |classKernel b x| ≤ 4 * classHeat x := by
  obtain ⟨hq, hq', _⟩ := classHeat_bounds hx
  obtain ⟨hp₀, hp₁, ho₀, ho₁⟩ := discriminant23_classThetaStar_bounds hq hq'
  have hp : 0 ≤ classThetaStar discriminant23PrincipalForm (classHeat x) :=
    (by positivity : 0 ≤ 2 * classHeat x).trans hp₀
  unfold classKernel
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hp, abs_mul, abs_of_nonneg ho₀]
  have hOther := mul_le_mul hb ho₁ ho₀ (by norm_num)
  linarith only [hp₁, hOther, hq]

private theorem norm_classKernel_sub_polynomial_le {b x : ℝ} (hb : |b| ≤ 2) (hx : 1 ≤ x)
    {N order : ℕ} (hOrder : 0 < order) (hCut : 18 * order + 9 ≤ 13 * (N + 1)) :
    ‖(classKernel b x : ℂ) - discriminant23ClassCombinationPolynomial b N (classHeat x)‖ ≤
      48 * classHeat x ^ order := by
  let q := classHeat x
  obtain ⟨hq, hqu, _⟩ := classHeat_bounds hx
  have hGrowthP (m n : ℤ) : 9 * (m ^ 2 + n ^ 2) ≤ 10 * discriminant23PrincipalForm m n := by
    unfold discriminant23PrincipalForm
    nlinarith only [sq_nonneg (m + 5 * n), sq_nonneg n]
  have hGrowthO (m n : ℤ) : 9 * (m ^ 2 + n ^ 2) ≤ 10 * discriminant23OtherForm m n := by
    unfold discriminant23OtherForm
    nlinarith only [sq_nonneg (m + n), sq_nonneg m, sq_nonneg n]
  have hPrincipal := classThetaStar_sub_finiteUpTo_bounds discriminant23PrincipalForm
    hGrowthP hOrder hCut hq hqu
  have hOther := classThetaStar_sub_finiteUpTo_bounds discriminant23OtherForm
    hGrowthO hOrder hCut hq hqu
  let dP := classThetaStar discriminant23PrincipalForm q -
    ∑ p ∈ characterThetaTermsUpTo discriminant23PrincipalForm N,
      q ^ (discriminant23PrincipalForm p.1 p.2).toNat
  let dO := classThetaStar discriminant23OtherForm q -
    ∑ p ∈ characterThetaTermsUpTo discriminant23OtherForm N,
      q ^ (discriminant23OtherForm p.1 p.2).toNat
  have hEq : (classKernel b x : ℂ) - discriminant23ClassCombinationPolynomial b N q =
      ((dP + b * dO : ℝ) : ℂ) := by
    simp only [classKernel, discriminant23ClassCombinationPolynomial, dP, dO, q,
      Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_sum]
    ring
  change ‖(classKernel b x : ℂ) - discriminant23ClassCombinationPolynomial b N q‖ ≤ _
  rw [hEq, Complex.norm_real, Real.norm_eq_abs]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hPrincipal.1, abs_mul, abs_of_nonneg hOther.1]
  have hO := mul_le_mul hb hOther.2 hOther.1 (by norm_num)
  linarith only [hPrincipal.2, hO]

private theorem exp_neg_one_le_three_eighths : Real.exp (-1) ≤ 3 / 8 := by
  have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  rw [Real.exp_neg, ← one_div, show (3 / 8 : ℝ) = 1 / (8 / 3) by norm_num]
  exact one_div_le_one_div_of_le (by norm_num) (by linarith only [h])

private theorem radial_heat_decay (x : ℝ) :
    x * Real.exp (-(13 / 10 : ℝ) * x) ≤ (15 / 2) * Real.exp (-(5 / 4 : ℝ) * x) := by
  have hlin : (1 / 20 : ℝ) * x ≤ Real.exp ((1 / 20 : ℝ) * x - 1) := by
    linarith only [Real.add_one_le_exp ((1 / 20 : ℝ) * x - 1)]
  have h := mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg (-(13 / 10 : ℝ) * x))
  rw [← Real.exp_add, show (1 / 20 : ℝ) * x - 1 + -(13 / 10 : ℝ) * x =
    -1 + -(5 / 4 : ℝ) * x by ring, Real.exp_add] at h
  have h' := mul_le_mul_of_nonneg_right exp_neg_one_le_three_eighths
    (Real.exp_nonneg (-(5 / 4 : ℝ) * x))
  linarith only [h, h']

private theorem integral_radial_decay (a c : ℝ) :
    (∫ x : ℝ in Ioi a, c * Real.exp (-(5 / 4 : ℝ) * x)) =
      (4 / 5) * c * Real.exp (-(5 / 4 : ℝ) * a) := by
  rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(5 / 4 : ℝ) < 0)]
  ring

private theorem classKernel_measurable (b : ℝ) : Measurable (classKernel b) := by
  have hq : Measurable classHeat := by unfold classHeat; fun_prop
  have hTheta (Q : ℤ → ℤ → ℤ) :
      Measurable (fun x ↦ classThetaStar Q (classHeat x)) := by
    unfold classThetaStar
    refine Measurable.tsum (fun p : ℤ × ℤ ↦ ?_)
    by_cases hp : p = (0, 0)
    · simpa only [hp, ite_true] using (measurable_const : Measurable (fun _ : ℝ ↦ (0 : ℝ)))
    · simpa only [ite_eq_right hp] using hq.pow_const (Q p.1 p.2).toNat
  exact (hTheta _).add ((hTheta _).const_mul b)

private theorem norm_folded_weight_le {w : ℂ} (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2)
    {x : ℝ} (hx : 1 ≤ x) : ‖foldedMellinWeight w x‖ ≤ 2 * x := by
  simpa only [Real.rpow_one] using
    foldedMellinWeight_norm_le (ρ := 1) hx hlo (by linarith only [hhi])

private theorem classCombination_radial_error {b : ℝ} (hb : |b| ≤ 2)
    {N order : ℕ} (hOrder : 0 < order) (hCut : 18 * order + 9 ≤ 13 * (N + 1))
    {R : ℝ} (hR : 1 ≤ R) {w : ℂ} (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2) :
    ‖2 * discriminant23ClassCombinationReading b w -
      foldedMellinTruncation
        (fun x ↦ discriminant23ClassCombinationPolynomial b N (classHeat x)) R w‖ ≤
      576 * (3 / 11 : ℝ) ^ (order - 1) + 48 * Real.exp (-(5 / 4 : ℝ) * R) := by
  let f (x : ℝ) := foldedMellinWeight w x * (classKernel b x : ℂ)
  let g (x : ℝ) := foldedMellinWeight w x *
    discriminant23ClassCombinationPolynomial b N (classHeat x)
  let c : ℝ := 720 * (3 / 11 : ℝ) ^ (order - 1)
  have hi (a d : ℝ) : IntegrableOn (fun x ↦ d * Real.exp (-(5 / 4 : ℝ) * x)) (Ioi a) :=
    (integrableOn_exp_mul_Ioi (a := -(5 / 4 : ℝ)) (by norm_num) a).const_mul d
  have hfWeight : Measurable (foldedMellinWeight w) := by
    unfold foldedMellinWeight
    fun_prop
  have hfBound (x : ℝ) (hx : 1 ≤ x) : ‖f x‖ ≤ 60 * Real.exp (-(5 / 4 : ℝ) * x) := by
    obtain ⟨hq, _, hq'⟩ := classHeat_bounds hx
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (2 * x) * (4 * classHeat x) :=
        mul_le_mul (norm_folded_weight_le hlo hhi hx) (abs_classKernel_le hb hx)
          (abs_nonneg _) (by positivity)
      _ ≤ 8 * (x * Real.exp (-(13 / 10 : ℝ) * x)) := by
        have h := mul_le_mul_of_nonneg_left hq' (show 0 ≤ 8 * x by positivity)
        linarith only [h]
      _ ≤ _ := by linarith only [radial_heat_decay x]
  have hf : IntegrableOn f (Ioi 1) := by
    have hm : Measurable f :=
      hfWeight.mul (Complex.continuous_ofReal.measurable.comp (classKernel_measurable b))
    refine Integrable.mono' (hi 1 60) hm.aestronglyMeasurable ?_
    exact (ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ hfBound x hx.le
  have hLocal (x : ℝ) (hx : 1 ≤ x) :
      ‖f x - g x‖ ≤ c * Real.exp (-(5 / 4 : ℝ) * x) := by
    obtain ⟨hq, hqu, hq'⟩ := classHeat_bounds hx
    have hqPow : classHeat x ^ order ≤
        (3 / 11 : ℝ) ^ (order - 1) * Real.exp (-(13 / 10 : ℝ) * x) := by
      calc
        _ = classHeat x ^ (order - 1) * classHeat x := by
          rw [← pow_succ, Nat.sub_add_cancel hOrder]
        _ ≤ _ := mul_le_mul (pow_le_pow_left₀ hq hqu _) hq' hq (by positivity)
    dsimp only [f, g]
    rw [← mul_sub, norm_mul]
    calc
      _ ≤ (2 * x) * (48 * classHeat x ^ order) :=
        mul_le_mul (norm_folded_weight_le hlo hhi hx)
          (norm_classKernel_sub_polynomial_le hb hx hOrder hCut) (norm_nonneg _) (by positivity)
      _ ≤ 96 * (3 / 11 : ℝ) ^ (order - 1) * (x * Real.exp (-(13 / 10 : ℝ) * x)) := by
        have h := mul_le_mul_of_nonneg_left hqPow (show 0 ≤ 96 * x by positivity)
        linarith only [h]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left (radial_heat_decay x)
          (show 0 ≤ 96 * (3 / 11 : ℝ) ^ (order - 1) by positivity)
        dsimp only [c]
        linarith only [h]
  have hSub : Ioc (1 : ℝ) R ⊆ Ioi 1 := fun _ hx ↦ hx.1
  have hFin := (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr (hf.mono_set hSub)
  have hCont : ContinuousOn g (Ioi 0) := by
    have hLog : ContinuousOn (fun x : ℝ ↦ (Real.log x : ℂ)) (Ioi 0) :=
      Complex.continuous_ofReal.comp_continuousOn fun _ hx ↦
        (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
    have hP : Continuous (fun x : ℝ ↦
        discriminant23ClassCombinationPolynomial b N (classHeat x)) := by
      unfold discriminant23ClassCombinationPolynomial classHeat
      fun_prop
    unfold g foldedMellinWeight
    exact ((Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hLog)).add
      (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hLog))).mul hP.continuousOn
  have hModel := (hCont.mono (show Icc (1 : ℝ) R ⊆ Ioi 0 from
    fun _ hx ↦ zero_lt_one.trans_le hx.1)).intervalIntegrable_of_Icc (μ := volume) hR
  have hError : ‖(∫ x in (1 : ℝ)..R, f x) - ∫ x in (1 : ℝ)..R, g x‖ ≤
      576 * (3 / 11 : ℝ) ^ (order - 1) := by
    rw [← intervalIntegral.integral_sub hFin hModel, intervalIntegral.integral_of_le hR]
    have hBound := norm_integral_le_of_norm_le (f := fun x ↦ f x - g x)
      ((hi 1 c).mono_set hSub)
      ((ae_restrict_mem measurableSet_Ioc).mono fun x hx ↦ hLocal x hx.1.le)
    have hMono := setIntegral_mono_set (hi 1 c)
      (ae_of_all _ (fun x ↦ mul_nonneg (by dsimp only [c]; positivity) (Real.exp_nonneg _)))
      (Filter.Eventually.of_forall hSub)
    refine hBound.trans (hMono.trans ?_)
    rw [integral_radial_decay]
    have he : Real.exp (-(5 / 4 : ℝ) * 1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have h := mul_le_mul_of_nonneg_left he (show 0 ≤ (4 / 5) * c by dsimp only [c]; positivity)
    dsimp only [c] at h
    linarith only [h]
  have hTail : ‖∫ x in Ioi R, f x‖ ≤ 48 * Real.exp (-(5 / 4 : ℝ) * R) := by
    refine (norm_integral_le_of_norm_le (f := f) (hi R 60)
      ((ae_restrict_mem measurableSet_Ioi).mono fun x hx ↦ hfBound x (hR.trans hx.le))).trans_eq ?_
    rw [integral_radial_decay]
    ring
  rw [classCombination_as_radial, foldedMellinTruncation]
  change ‖(∫ x in Ioi 1, f x) - ∫ x in (1 : ℝ)..R, g x‖ ≤ _
  rw [← intervalIntegral.integral_interval_add_Ioi hf (hf.mono_set (Ioi_subset_Ioi hR)),
    add_sub_right_comm]
  exact (norm_add_le _ _).trans (add_le_add hError hTail)

/-- Both the omitted lattice terms and the infinite radial tail are bounded
before evaluating the finite quadrature. -/
theorem discriminant23_classCombination_integral_error {b : ℝ} (hb : |b| ≤ 2)
    {N order : ℕ} (hOrder : 0 < order) (hCut : 18 * order + 9 ≤ 13 * (N + 1))
    {L : ℝ} (hL : 0 ≤ L) {w : ℂ} (hlo : -1 ≤ w.re) (hhi : w.re ≤ 2) :
    ‖2 * discriminant23ClassCombinationReading b w -
      ∫ u in (0 : ℝ)..L, discriminant23ClassCombinationIntegrand b N w (u : ℂ)‖ ≤
      576 * (3 / 11 : ℝ) ^ (order - 1) + 48 * Real.exp (-(5 / 4 : ℝ) * Real.exp L) := by
  have hR : 1 ≤ Real.exp L := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr hL
  have h := classCombination_radial_error hb hOrder hCut hR hlo hhi
  let f (x : ℝ) := foldedMellinWeight w x *
    discriminant23ClassCombinationPolynomial b N (classHeat x)
  have hP : Continuous (fun x : ℝ ↦
      discriminant23ClassCombinationPolynomial b N (classHeat x)) := by
    unfold discriminant23ClassCombinationPolynomial classHeat
    fun_prop
  have hLog : ContinuousOn (fun x : ℝ ↦ (Real.log x : ℂ)) (Ioi 0) :=
    Complex.continuous_ofReal.comp_continuousOn fun _ hx ↦
      (Real.continuousAt_log (ne_of_gt hx)).continuousWithinAt
  have hf : ContinuousOn f (Ioi 0) := by
    unfold f foldedMellinWeight
    exact ((Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hLog)).add
      (Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul hLog))).mul hP.continuousOn
  have hc : ContinuousOn f (Real.exp '' [[(0 : ℝ), L]]) :=
    hf.mono (by rintro _ ⟨u, _, rfl⟩; exact Real.exp_pos u)
  have hChange := intervalIntegral.integral_deriv_smul_comp' (a := (0 : ℝ)) (b := L)
    (fun u _ ↦ Real.hasDerivAt_exp u) Real.continuous_exp.continuousOn hc
  rw [Real.exp_zero] at hChange
  unfold foldedMellinTruncation at h
  change ‖2 * discriminant23ClassCombinationReading b w - ∫ x in (1 : ℝ)..Real.exp L, f x‖ ≤ _ at h
  rw [← hChange] at h
  have hIntegrands :
      (∫ u in (0 : ℝ)..L, Real.exp u • f (Real.exp u)) =
        ∫ u in (0 : ℝ)..L, discriminant23ClassCombinationIntegrand b N w (u : ℂ) := by
    apply intervalIntegral.integral_congr
    intro u _
    simp only [Complex.real_smul, f, foldedMellinWeight, Real.log_exp, classHeat,
      Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
      discriminant23ClassCombinationIntegrand]
    ring
  simpa only [Function.comp_apply, hIntegrands] using h

#print axioms discriminant23_classCombinationReading_two
#print axioms discriminant23_classCombinationReading_neg_one
#print axioms discriminant23_classCombination_integral_error

end
end FieldTarget
