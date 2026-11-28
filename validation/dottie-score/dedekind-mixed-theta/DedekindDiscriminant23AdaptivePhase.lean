import DedekindDiscriminant23CharacterComplex
import DedekindDiscriminant23PhaseEvaluation

/-! Allow the norm cutoff, the logarithmic integration endpoint, and the
Taylor depth to vary together without a restriction on imaginary height. -/

namespace FieldTarget

open Finset MeasureTheory Metric Set Filter
open scoped Interval NNReal Topology

noncomputable section

def discriminant23PhaseDensityUpTo (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp z * discriminant23CharacterPolynomialUpTo N
    (Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z))

private def radialPhaseWeight (odd : Bool) (w : ℂ) (u : ℝ) : ℂ :=
  if odd then
    (u : ℂ) * (Complex.exp ((w - 1) * u) - Complex.exp (-w * u))
  else Complex.exp ((w - 1) * u) + Complex.exp (-w * u)

def discriminant23PhaseTaylorUpTo (N L depth : ℕ) (odd : Bool) (w : ℂ) : ℂ :=
  weightedContourTaylorComposite (discriminant23PhaseDensityUpTo N)
    (radialPhaseWeight odd w) 0 (1 / 8) (1 / 4) (4 * L) depth

private def densityMass (N : ℕ) : ℝ :=
  ((characterThetaTermsUpTo discriminant23PrincipalForm N).card : ℝ) +
    (characterThetaTermsUpTo discriminant23OtherForm N).card

def discriminant23PhaseQuadratureError (N L depth : ℕ) : ℝ :=
  4 * (L : ℝ) * ((L : ℝ) + 1) * densityMass N * (1 / 2) ^ depth

private theorem exp_mul_heat_power_norm_le {z : ℂ} (hy : |z.im| ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    ‖Complex.exp z * Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z) ^ k‖ ≤ 1 := by
  let q := Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)
  have hcos : (1 / 2 : ℝ) ≤ Real.cos z.im := by
    have hs : z.im ^ 2 ≤ (1 : ℝ) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hy 2
    linarith only [hs, Real.one_sub_sq_div_two_le_cos (x := z.im)]
  have hscale : (1 / 2 : ℝ) ≤ discriminant23ThetaScale * Real.cos z.im :=
    (by norm_num : (1 / 2 : ℝ) ≤ (13 / 10) * (1 / 2)).trans
      (mul_le_mul discriminant23_thetaScale_interval.1 hcos (by norm_num)
        (by linarith only [discriminant23_thetaScale_interval.1]))
  have hq : ‖q‖ ≤ Real.exp (-Real.exp z.re / 2) := by
    unfold q
    rw [Complex.norm_exp, ← Complex.ofReal_neg, Complex.re_ofReal_mul, Complex.exp_re]
    exact Real.exp_le_exp.mpr (by
      nlinarith only [mul_le_mul_of_nonneg_right hscale (Real.exp_nonneg z.re)])
  have hq₁ : ‖q‖ ≤ 1 := hq.trans
    ((Real.exp_le_exp.mpr (by linarith only [Real.exp_nonneg z.re])).trans_eq Real.exp_zero)
  have hpow : ‖q‖ ^ k ≤ ‖q‖ := by
    simpa only [pow_one] using pow_le_pow_of_le_one (norm_nonneg q) hq₁ hk
  have hlin : Real.exp z.re ≤ 2 * Real.exp (Real.exp z.re / 2 - 1) := by
    linarith only [Real.add_one_le_exp (Real.exp z.re / 2 - 1)]
  change ‖Complex.exp z * q ^ k‖ ≤ 1
  rw [norm_mul, Complex.norm_exp, norm_pow]
  calc
    _ ≤ Real.exp z.re * Real.exp (-Real.exp z.re / 2) :=
      mul_le_mul_of_nonneg_left (hpow.trans hq) (Real.exp_nonneg _)
    _ ≤ (2 * Real.exp (Real.exp z.re / 2 - 1)) * Real.exp (-Real.exp z.re / 2) :=
      mul_le_mul_of_nonneg_right hlin (Real.exp_nonneg _)
    _ = 2 * Real.exp (-1) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ 1 := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact (div_le_one (Real.exp_pos 1)).mpr (by linarith only [Real.add_one_le_exp (1 : ℝ)])

private theorem thetaDensity_im_norm_le (N : ℕ) {z : ℂ} (hy : |z.im| ≤ 1) :
    ‖discriminant23PhaseDensityUpTo N z‖ ≤ densityMass N := by
  let q := Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp z)
  have hSum (Q : ℤ → ℤ → ℤ) (hQ : ∀ m n, m ^ 2 + n ^ 2 ≤ 2 * Q m n) :
      ‖∑ p ∈ characterThetaTermsUpTo Q N, Complex.exp z * q ^ (Q p.1 p.2).toNat‖ ≤
        ((characterThetaTermsUpTo Q N).card : ℝ) := by
    refine (norm_sum_le _ _).trans ?_
    have hcard : (∑ _p ∈ characterThetaTermsUpTo Q N, (1 : ℝ)) =
        ((characterThetaTermsUpTo Q N).card : ℝ) := by simp
    rw [← hcard]
    apply Finset.sum_le_sum
    intro p hp
    have hne := (mem_filter.mp hp).2.1
    have hPos : 0 < p.1 ^ 2 + p.2 ^ 2 := by
      by_cases h₁ : p.1 = 0
      · have h₂ : p.2 ≠ 0 := fun h₂ ↦ hne (Prod.ext h₁ h₂)
        exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero h₂)
      · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero h₁) (sq_nonneg _)
    have hQp := hQ p.1 p.2
    exact exp_mul_heat_power_norm_le hy (by omega)
  unfold discriminant23PhaseDensityUpTo discriminant23CharacterPolynomialUpTo densityMass
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  exact (norm_sub_le _ _).trans
    (add_le_add (hSum _ discriminant23_principal_form_growth) (hSum _ discriminant23_other_form_growth))

theorem discriminant23_phaseDensity_norm_le_of_abs_im_le_one (N : ℕ) {z : ℂ} (hy : |z.im| ≤ 1) :
    ‖discriminant23PhaseDensityUpTo N z‖ ≤
      (((characterThetaTermsUpTo discriminant23PrincipalForm N).card +
        (characterThetaTermsUpTo discriminant23OtherForm N).card : ℕ) : ℝ) := by
  simpa only [densityMass, Nat.cast_add] using thetaDensity_im_norm_le N hy

theorem discriminant23_phaseDensity_norm_le (N : ℕ) {z : ℂ} (hy : |z.im| ≤ 1 / 2) :
    ‖discriminant23PhaseDensityUpTo N z‖ ≤
      (((characterThetaTermsUpTo discriminant23PrincipalForm N).card +
        (characterThetaTermsUpTo discriminant23OtherForm N).card : ℕ) : ℝ) :=
  discriminant23_phaseDensity_norm_le_of_abs_im_le_one N (hy.trans (by norm_num))

private theorem thetaDensity_norm_le (N : ℕ) {c : ℝ} {z : ℂ}
    (hz : z ∈ sphere (c : ℂ) (1 / 4 : ℝ)) :
    ‖discriminant23PhaseDensityUpTo N z‖ ≤ densityMass N := by
  have hd := mem_sphere.mp hz
  rw [dist_eq_norm] at hd
  have hy := (Complex.abs_im_le_norm (z - (c : ℂ))).trans_eq hd
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hy
  exact thetaDensity_im_norm_le N (hy.trans (by norm_num))

theorem discriminant23_phaseDensity_real_norm_le (N : ℕ) (u : ℝ) :
    ‖discriminant23PhaseDensityUpTo N (u : ℂ)‖ ≤
      (((characterThetaTermsUpTo discriminant23PrincipalForm N).card +
        (characterThetaTermsUpTo discriminant23OtherForm N).card : ℕ) : ℝ) := by
  exact discriminant23_phaseDensity_norm_le N (by simp)

private theorem radialPhaseWeight_norm_le (odd : Bool) {w : ℂ} {L u : ℝ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) (hu : u ∈ Icc (0 : ℝ) L) :
    ‖radialPhaseWeight odd w u‖ ≤ 2 * (L + 1) := by
  have he (v : ℂ) (hv : v.re ≤ 0) : ‖Complex.exp (v * (u : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    exact (Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg hv hu.1)).trans_eq Real.exp_zero
  have h₁ := he (w - 1) (by rw [Complex.sub_re, Complex.one_re]; linarith only [hhi])
  have h₂ := he (-w) (by rw [Complex.neg_re]; linarith only [hlo])
  cases odd
  · change ‖Complex.exp ((w - 1) * (u : ℂ)) + Complex.exp (-w * (u : ℂ))‖ ≤ _
    exact (norm_add_le _ _).trans (by linarith only [h₁, h₂, hu.1, hu.2])
  · change ‖(u : ℂ) * (Complex.exp ((w - 1) * (u : ℂ)) - Complex.exp (-w * (u : ℂ)))‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.1]
    exact (mul_le_mul hu.2 ((norm_sub_le _ _).trans (add_le_add h₁ h₂))
      (norm_nonneg _) (hu.1.trans hu.2)).trans (by linarith)

private theorem radialPhaseWeight_times_exp (odd : Bool) (w : ℂ) (u : ℝ) :
    radialPhaseWeight odd w u * Complex.exp (u : ℂ) = discriminant23PhaseWeight odd w u := by
  have h₁ : Complex.exp ((w - 1) * (u : ℂ)) * Complex.exp (u : ℂ) = Complex.exp (w * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have h₂ : Complex.exp (-w * (u : ℂ)) * Complex.exp (u : ℂ) = Complex.exp ((1 - w) * (u : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  cases odd
  · change (_ + _) * Complex.exp _ = _
    rw [add_mul, h₁, h₂]
    rfl
  · change ((u : ℂ) * (_ - _)) * Complex.exp _ = _
    rw [mul_assoc, sub_mul, h₁, h₂]
    rfl

private theorem radialPhase_integrand_eq (N : ℕ) (odd : Bool) (w : ℂ) (u : ℝ) :
    radialPhaseWeight odd w u * discriminant23PhaseDensityUpTo N (u : ℂ) =
      discriminant23PhaseWeight odd w u *
        (discriminant23CharacterPolynomialUpTo N (Real.exp (-discriminant23ThetaScale * Real.exp u)) : ℝ) := by
  have hHeat : Complex.exp (-(discriminant23ThetaScale : ℂ) * Complex.exp (u : ℂ)) =
      (Real.exp (-discriminant23ThetaScale * Real.exp u) : ℂ) := by
    simp only [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  rw [discriminant23PhaseDensityUpTo, hHeat, ← discriminant23_characterPolynomialUpTo_ofReal,
    ← mul_assoc, radialPhaseWeight_times_exp]

private theorem phaseTaylor_model_error (N L depth : ℕ) (odd : Bool) {w : ℂ}
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖(∫ u in (0 : ℝ)..L, radialPhaseWeight odd w u * discriminant23PhaseDensityUpTo N (u : ℂ)) -
      discriminant23PhaseTaylorUpTo N L depth odd w‖ ≤
      discriminant23PhaseQuadratureError N L depth := by
  have hEnd : (0 : ℝ) + 2 * ((4 * L : ℕ) : ℝ) * (1 / 8) = L := by push_cast; ring
  have hD : Differentiable ℂ (discriminant23PhaseDensityUpTo N) := by
    unfold discriminant23PhaseDensityUpTo discriminant23CharacterPolynomialUpTo
    fun_prop
  have hW : Continuous (radialPhaseWeight odd w) := by
    cases odd
    · change Continuous (fun x : ℝ ↦ Complex.exp ((w - 1) * x) + Complex.exp (-w * x))
      fun_prop
    · change Continuous (fun x : ℝ ↦ (x : ℂ) * (Complex.exp ((w - 1) * x) - Complex.exp (-w * x)))
      fun_prop
  have h := weightedContourTaylorComposite_error_le
    (F := discriminant23PhaseDensityUpTo N) (W := radialPhaseWeight odd w) (a := 0)
    (h := 1 / 8) (M := densityMass N) (B := 2 * ((L : ℝ) + 1)) (R := (1 / 4 : ℝ≥0))
    (4 * L) depth (by norm_num) (by norm_num) hD hW
    (fun _ _ _ hz ↦ thetaDensity_norm_le N hz) (by positivity)
    (fun u hu ↦ radialPhaseWeight_norm_le odd hlo hhi (by rwa [hEnd] at hu))
  rw [hEnd] at h
  refine h.trans_eq ?_
  unfold discriminant23PhaseQuadratureError
  push_cast
  norm_num; ring

theorem discriminant23_phaseTaylorUpTo_error {N L depth order : ℕ} {w : ℂ}
    (hOrder : 0 < order) (hCut : 18 * order + 9 ≤ 13 * (N + 1))
    (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖discriminant23CharacterFold w - discriminant23PhaseTaylorUpTo N L depth false w‖ ≤
      discriminant23CharacterModelError order (Real.exp L) + discriminant23PhaseQuadratureError N L depth ∧
    ‖deriv discriminant23CharacterFold w - discriminant23PhaseTaylorUpTo N L depth true w‖ ≤
      discriminant23CharacterModelError order (Real.exp L) + discriminant23PhaseQuadratureError N L depth := by
  have hL : (0 : ℝ) ≤ L := by positivity
  have hR : 1 ≤ Real.exp (L : ℝ) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hL
  let F := discriminant23CharacterModelUpTo N (Real.exp L)
  have hValue := discriminant23_characterModelUpTo_error hOrder hCut hR (w := w)
    (by linarith only [hlo]) (by linarith only [hhi])
  have hSlope := discriminant23_characterModelUpTo_iteratedDeriv_error 1 hOrder hCut hR hlo hhi
  simp only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul] at hSlope
  have hV : ‖F w - discriminant23PhaseTaylorUpTo N L depth false w‖ ≤ discriminant23PhaseQuadratureError N L depth := by
    change ‖discriminant23CharacterModelUpTo N (Real.exp L) w - _‖ ≤ _
    rw [discriminant23_characterModelUpTo_eq_logIntegral]
    have h := phaseTaylor_model_error N L depth false hlo hhi
    simp_rw [radialPhase_integrand_eq] at h
    exact h
  have hS : ‖deriv F w - discriminant23PhaseTaylorUpTo N L depth true w‖ ≤ discriminant23PhaseQuadratureError N L depth := by
    change ‖deriv (discriminant23CharacterModelUpTo N (Real.exp L)) w - _‖ ≤ _
    rw [discriminant23_characterModelUpTo_deriv_eq_logIntegral N hL]
    have h := phaseTaylor_model_error N L depth true hlo hhi
    simp_rw [radialPhase_integrand_eq] at h
    exact h
  exact ⟨(norm_sub_le_norm_sub_add_norm_sub _ (F w) _).trans (add_le_add hValue hV),
    (norm_sub_le_norm_sub_add_norm_sub _ (deriv F w) _).trans (add_le_add hSlope hS)⟩

private theorem exists_characterModelError_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ k L : ℕ, discriminant23CharacterModelError (k + 1) (Real.exp L) < ε := by
  have hp : Tendsto (fun k : ℕ ↦ 15 * (3 / 11 : ℝ) ^ k) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 3 / 11) (by norm_num)).const_mul (15 : ℝ)
  have hExp : Tendsto (fun L : ℕ ↦ Real.exp (L : ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hNeg : Tendsto (fun L : ℕ ↦ -(5 / 4 : ℝ) * Real.exp (L : ℝ)) atTop atBot :=
    hExp.const_mul_atTop_of_neg (by norm_num)
  have hTail : Tendsto (fun L : ℕ ↦ (126 / 5 : ℝ) * Real.exp (-(5 / 4 : ℝ) * Real.exp L)) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using (Real.tendsto_exp_atBot.comp hNeg).const_mul (126 / 5 : ℝ)
  have hb : 0 < ε / 2 := by positivity
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hp).2 _ hb).exists
  obtain ⟨L, hL⟩ := ((tendsto_order.1 hTail).2 _ hb).exists
  refine ⟨k, L, ?_⟩
  unfold discriminant23CharacterModelError
  rw [Nat.add_sub_cancel]
  have h := add_lt_add hk hL
  linarith only [h]

/-- One choice of finite data reaches any positive tolerance for both
readings on the entire closed critical strip. -/
theorem discriminant23_exists_uniform_phaseApproximation {ε : ℝ} (hε : 0 < ε) :
    ∃ N L depth : ℕ, ∀ w : ℂ, 0 ≤ w.re → w.re ≤ 1 →
      ‖discriminant23CharacterFold w - discriminant23PhaseTaylorUpTo N L depth false w‖ < ε ∧
      ‖deriv discriminant23CharacterFold w - discriminant23PhaseTaylorUpTo N L depth true w‖ < ε := by
  have hb : 0 < ε / 2 := by positivity
  obtain ⟨k, L, hModel⟩ := exists_characterModelError_lt hb
  let N := 2 * (k + 1)
  have hQuad : Tendsto (discriminant23PhaseQuadratureError N L) atTop (𝓝 0) := by
    change Tendsto (fun d : ℕ ↦ 4 * (L : ℝ) * ((L : ℝ) + 1) * densityMass N * (1 / 2)^d) atTop (𝓝 0)
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).const_mul
        (4 * (L : ℝ) * ((L : ℝ) + 1) * densityMass N)
  obtain ⟨depth, hDepth⟩ := ((tendsto_order.1 hQuad).2 _ hb).exists
  refine ⟨N, L, depth, fun w hlo hhi ↦ ?_⟩
  have h := discriminant23_phaseTaylorUpTo_error (N := N) (L := L) (depth := depth)
    (order := k + 1) (by omega) (by unfold N; omega) (w := w) hlo hhi
  have hTotal := add_lt_add hModel hDepth
  exact ⟨h.1.trans_lt (by linarith only [hTotal]), h.2.trans_lt (by linarith only [hTotal])⟩

private theorem densityMass_sixtyFour : densityMass 64 = 174 := by
  have hp : (characterThetaTermsUpTo discriminant23PrincipalForm 64).card = 90 := by decide +kernel
  have hn : (characterThetaTermsUpTo discriminant23OtherForm 64).card = 84 := by decide +kernel
  norm_num [densityMass, hp, hn]

private theorem phaseError_at_64_4_96 : discriminant23CharacterModelError 46 (Real.exp 4) +
    discriminant23PhaseQuadratureError 64 4 96 < 1 / 10 ^ 23 := by
  have h₄ : (50 : ℝ) ≤ Real.exp 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact (by norm_num : (50 : ℝ) ≤ (27 / 10 : ℝ) ^ 4).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith only [Real.exp_one_gt_d9]) 4)
  have hNeg : Real.exp (-1) ≤ (3 / 8 : ℝ) := by
    rw [Real.exp_neg, ← one_div, show (3 / 8 : ℝ) = 1 / (8 / 3) by norm_num]
    exact one_div_le_one_div_of_le (by norm_num) (by linarith only [Real.exp_one_gt_d9])
  have hTail : Real.exp (-(5 / 4 : ℝ) * Real.exp 4) ≤ (3 / 8 : ℝ) ^ 62 := by
    refine (Real.exp_le_exp.mpr (by linarith only [h₄] : -(5 / 4 : ℝ) * Real.exp 4 ≤ -62)).trans ?_
    rw [show (-62 : ℝ) = (62 : ℕ) * (-1) by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hNeg 62
  unfold discriminant23CharacterModelError discriminant23PhaseQuadratureError
  rw [densityMass_sixtyFour]
  calc
    _ ≤ (15 * (3 / 11 : ℝ) ^ (46 - 1 : ℕ) + (126 / 5) * (3 / 8 : ℝ) ^ 62) +
        4 * (4 : ℝ) * (4 + 1) * 174 * (1 / 2) ^ 96 :=
      add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hTail (by norm_num))) le_rfl
    _ < _ := by norm_num

theorem discriminant23_modelError_at_64_4 :
    discriminant23CharacterModelError 46 (Real.exp 4) < 1 / 10 ^ 23 :=
  (le_add_of_nonneg_right (by unfold discriminant23PhaseQuadratureError densityMass; positivity)).trans_lt
    phaseError_at_64_4_96

/-- A concrete parameter choice for a smaller analytic allowance. -/
theorem discriminant23_phaseTaylor_error_at_64_4_96 {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖discriminant23CharacterFold w - discriminant23PhaseTaylorUpTo 64 4 96 false w‖ < 1 / 10 ^ 23 ∧
    ‖deriv discriminant23CharacterFold w - discriminant23PhaseTaylorUpTo 64 4 96 true w‖ < 1 / 10 ^ 23 := by
  have h := discriminant23_phaseTaylorUpTo_error (N := 64) (L := 4) (depth := 96) (order := 46)
    (by decide) (by decide) (w := w) hlo hhi
  exact ⟨h.1.trans_lt phaseError_at_64_4_96, h.2.trans_lt phaseError_at_64_4_96⟩

private theorem radialPhaseWeight_eq_phaseWeight_neg (odd : Bool) (w : ℂ) (u : ℝ) :
    radialPhaseWeight odd w u = discriminant23PhaseWeight odd w (-u) := by
  have h₁ : w * ((-u : ℝ) : ℂ) = -w * (u : ℂ) := by push_cast; ring
  have h₂ : (1 - w) * ((-u : ℝ) : ℂ) = (w - 1) * (u : ℂ) := by push_cast; ring
  cases odd
  · change Complex.exp ((w - 1) * (u : ℂ)) + Complex.exp (-w * (u : ℂ)) =
      Complex.exp (w * ((-u : ℝ) : ℂ)) + Complex.exp ((1 - w) * ((-u : ℝ) : ℂ))
    rw [h₁, h₂, add_comm]
  · change (u : ℂ) * (Complex.exp ((w - 1) * (u : ℂ)) - Complex.exp (-w * (u : ℂ))) =
      ((-u : ℝ) : ℂ) * (Complex.exp (w * ((-u : ℝ) : ℂ)) - Complex.exp ((1 - w) * ((-u : ℝ) : ℂ)))
    rw [h₁, h₂, Complex.ofReal_neg]
    ring

private theorem radialPhase_power_integral (odd : Bool) (w : ℂ) (a b c : ℝ) (j : ℕ) :
    (∫ x in a..b, radialPhaseWeight odd w x * ((x - c : ℝ) : ℂ) ^ j) =
      (-1 : ℂ) ^ j * discriminant23PhaseMoment odd w (-b) (-a) (-c) j := by
  have hFlip := intervalIntegral.integral_comp_neg (a := a) (b := b)
    (f := fun x : ℝ ↦ discriminant23PhaseWeight odd w x * ((x - -c : ℝ) : ℂ) ^ j)
  rw [discriminant23_phaseMoment_eq_integral, ← hFlip, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  beta_reduce
  have hCoord : ((-u - -c : ℝ) : ℂ) = (-1 : ℂ) * ((u - c : ℝ) : ℂ) := by push_cast; ring
  rw [← radialPhaseWeight_eq_phaseWeight_neg, hCoord, mul_pow]
  have hUnit : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℂ) ^ j * (-1 : ℂ) ^ j) * (radialPhaseWeight odd w u * ((u - c : ℝ) : ℂ) ^ j) := by
      rw [hUnit, one_mul]
    _ = _ := by ring

/-- Reuse the endpoint-moment recurrence on the reflected panel. -/
theorem discriminant23_phaseTaylorUpTo_eq_moments (N L depth : ℕ) (odd : Bool) (w : ℂ) :
    discriminant23PhaseTaylorUpTo N L depth odd w =
      ∑ k ∈ Finset.range (4 * L), ∑ j ∈ Finset.range depth,
        let c : ℝ := (2 * (k : ℝ) + 1) * (1 / 8)
        contourTaylorCoeff (discriminant23PhaseDensityUpTo N) (c : ℂ) (1 / 4) j *
          ((-1 : ℂ) ^ j * discriminant23PhaseMoment odd w (-(c + 1 / 8)) (-(c - 1 / 8)) (-c) j) := by
  simp only [discriminant23PhaseTaylorUpTo, weightedContourTaylorComposite,
    weightedContourTaylorPanel, zero_add, radialPhase_power_integral]
  norm_num

end

#check @discriminant23_exists_uniform_phaseApproximation
#print axioms discriminant23_phaseTaylorUpTo_eq_moments
#print axioms discriminant23_phaseTaylor_error_at_64_4_96
#print axioms discriminant23_phaseTaylorUpTo_error
#print axioms discriminant23_exists_uniform_phaseApproximation
#print axioms discriminant23_phaseDensity_real_norm_le
#print axioms discriminant23_phaseDensity_norm_le
#print axioms discriminant23_modelError_at_64_4

end FieldTarget
