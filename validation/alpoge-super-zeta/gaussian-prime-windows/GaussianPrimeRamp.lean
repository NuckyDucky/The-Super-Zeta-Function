import GaussianRealPoles
import Mathlib.Analysis.Calculus.Deriv.Star
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.GchiGrowth
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.measurableGchi
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiOfNeOne

/-! Adapt the prime-power ramp of the window criterion to the archived Gaussian factor. -/

open scoped ComplexConjugate

namespace AlpogeSuperZeta

open Complex MeasureTheory Set QuarticModel FieldTarget ArtinPrimitiveRootsConjecture

noncomputable section

theorem gaussianFactor_conj (w : ℂ) :
    archivedGaussianFactor (conj w) = conj (archivedGaussianFactor w) := by
  have harg : (archivedThetaScale : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg archivedThetaScale_pos.le]
    exact Real.pi_pos.ne
  have hpower :
      (archivedThetaScale : ℂ) ^ conj w = conj ((archivedThetaScale : ℂ) ^ w) := by
    simpa using cpow_conj (archivedThetaScale : ℂ) w harg
  simp only [archivedGaussianFactor, archivedMellin_conj, Gamma_conj, hpower, map_mul, map_inv₀]

theorem gaussian_logDeriv_one_isReal :
    ((logDeriv archivedGaussianFactor 1).re : ℂ) = logDeriv archivedGaussianFactor 1 := by
  have hfun : conj ∘ archivedGaussianFactor ∘ conj = archivedGaussianFactor := by
    funext z
    simp [Function.comp_apply, gaussianFactor_conj]
  have hd := congrFun (deriv_conj_conj (f := archivedGaussianFactor)) (1 : ℂ)
  rw [hfun] at hd
  have hderiv : deriv archivedGaussianFactor 1 = conj (deriv archivedGaussianFactor 1) := by
    simpa only [Function.comp_apply, map_one] using hd
  have hval : archivedGaussianFactor 1 = conj (archivedGaussianFactor 1) := by
    simpa only [map_one] using gaussianFactor_conj 1
  have hfix : conj (logDeriv archivedGaussianFactor 1) = logDeriv archivedGaussianFactor 1 := by
    simp only [logDeriv_apply, map_div₀]
    rw [← hderiv, ← hval]
  apply Complex.ext
  · exact ofReal_re _
  · have hi := congrArg Complex.im hfix
    rw [conj_im] at hi
    simp only [ofReal_im]
    linarith

/-- The endpoint term is fixed by the archived factor at one. -/
def gaussianPrimeNormRamp (a : ℕ → ℝ) (y : ℝ) : ℝ :=
  (Deduction.ramp (fun n => (a n : ℂ)) y).re + (logDeriv archivedGaussianFactor 1).re * y

def gaussianLogCutoffRamp (a : ℕ → ℝ) (u : ℝ) : ℝ :=
  gaussianPrimeNormRamp a (Real.exp u)

private theorem gaussianPrimeNormRamp_coe (a : ℕ → ℝ) (y : ℝ) :
    (gaussianPrimeNormRamp a y : ℂ) =
      Deduction.ramp (fun n => (a n : ℂ)) y + logDeriv archivedGaussianFactor 1 * (y : ℂ) := by
  have hr : ((Deduction.ramp (fun n => (a n : ℂ)) y).re : ℂ) =
      Deduction.ramp (fun n => (a n : ℂ)) y := by
    apply Complex.ext
    · exact ofReal_re _
    · simp [Deduction.ramp, Complex.im_sum, Complex.mul_im]
  rw [gaussianPrimeNormRamp, ofReal_add, ofReal_mul, hr, gaussian_logDeriv_one_isReal]

theorem gaussianLogCutoffRamp_measurable (a : ℕ → ℝ) :
    Measurable (gaussianLogCutoffRamp a) := by
  have h := Complex.continuous_re.measurable.comp (Deduction.measurable_Gchi_ramp
    (fun n => (a n : ℂ)))
  exact (h.add (measurable_const.mul measurable_id)).comp Real.measurable_exp

theorem gaussianLogCutoffRamp_growth (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 2) :
    ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u →
      |gaussianLogCutoffRamp a u| ≤ C * Real.exp (2 * u) := by
  let c := (logDeriv archivedGaussianFactor 1).re
  refine ⟨4 + |c|, fun u hu => ?_⟩
  let y := Real.exp u
  have hy : 1 ≤ y := Real.one_le_exp hu
  have hy0 : 0 ≤ y := zero_le_one.trans hy
  have hy2 : y ≤ y ^ 2 := by nlinarith
  have hhalf (n : ℕ) : ‖((a n / 2 : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [ha n]
  have hscale : Deduction.ramp (fun n => (a n : ℂ)) y =
      2 * Deduction.ramp (fun n => ((a n / 2 : ℝ) : ℂ)) y := by
    unfold Deduction.ramp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    ring
  have hnorm : ‖Deduction.ramp (fun n => (a n : ℂ)) y‖ ≤ 4 * y ^ 2 := by
    have h := Deduction.Gchi_growth_ramp _ hhalf hy
    rw [hscale, norm_mul, Complex.norm_ofNat]
    linarith
  change |(Deduction.ramp (fun n => (a n : ℂ)) y).re + c * y| ≤
    (4 + |c|) * Real.exp (2*u)
  rw [show Real.exp (2 * u) = y ^ 2 by
    dsimp [y]
    rw [show 2 * u = u + u by ring, Real.exp_add, pow_two]]
  calc
    _ ≤ |(Deduction.ramp (fun n => (a n : ℂ)) y).re| + |c * y| := abs_add_le _ _
    _ ≤ 4 * y ^ 2 + |c| * y := by
      rw [abs_mul, abs_of_nonneg hy0]
      exact add_le_add ((abs_re_le_norm _).trans hnorm) le_rfl
    _ ≤ (4 + |c|) * y ^ 2 := by
      rw [add_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hy2 (abs_nonneg c))

private theorem weighted_vonMangoldt_summable (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 2)
    {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable (fun n => (a n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) w := by
  have hbase := (ArithmeticFunction.LSeriesSummable_vonMangoldt hw).norm.mul_left 2
  rw [LSeriesSummable, ← summable_norm_iff]
  refine hbase.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro n
  simp only [LSeries.norm_term_eq]
  split_ifs with hn
  · simp
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)) (by positivity)

theorem gaussianLogCutoffRamp_laplace (a : ℕ → ℝ) (ha : ∀ n, |a n| ≤ 2)
    {w : ℂ} (hw : 2 < w.re)
    (hcoeff : LSeries (fun n => (a n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) w =
      -logDeriv archivedGaussianFactor w) :
    gaussianPoleFormula w =
      ∫ u in Ioi (0 : ℝ), (gaussianLogCutoffRamp a u : ℂ) * exp (-w * u) := by
  have hw' : 1 < w.re := by linarith
  obtain ⟨h0, h1⟩ := Deduction.mellin_Gchi_of_ne_one_ne hw'
  let c := logDeriv archivedGaussianFactor 1
  have ha' : (-w).re < -1 := by simp; linarith
  have h := Deduction.mellin_Gchi_of_ne_one_ramp (fun n => (a n : ℂ)) w hw'
    (weighted_vonMangoldt_summable a ha hw') (fun y : ℝ => c * (y : ℂ) ^ (-w))
    ((integrableOn_Ioi_cpow_of_lt ha' one_pos).const_mul c)
  rw [hcoeff, integral_const_mul, integral_Ioi_cpow_of_lt ha' one_pos] at h
  change _ = ∫ u in Ioi (0 : ℝ),
    ((fun y => (gaussianPrimeNormRamp a y : ℂ)) (Real.exp u)) * exp (-w * u)
  rw [Deduction.poleData_change (fun y => (gaussianPrimeNormRamp a y : ℂ)) w]
  symm
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y : ℝ =>
    Deduction.ramp (fun n => (a n : ℂ)) y * (y : ℂ) ^ (-w - 1) + c * (y : ℂ) ^ (-w)), h]
  · rw [show -w + 1 = -(w - 1) by ring]
    simp only [ofReal_one, one_cpow]
    change _ = -(logDeriv archivedGaussianFactor w - w * c) / (w * (w - 1))
    field_simp
    ring
  · intro y hy
    have hy0 : (y : ℂ) ≠ 0 := by exact_mod_cast (lt_trans one_pos hy).ne'
    dsimp only
    rw [gaussianPrimeNormRamp_coe, add_mul, cpow_sub _ _ hy0, cpow_one]
    dsimp [c]
    field_simp

/-- A bounded coefficient sequence for the actual logarithmic derivative
and the one-sided estimate on its own norm windows give the quartic statement. -/
theorem quartic_rh_of_gaussian_prime_norm_windows (hD : DirichletLZerosOnLine)
    (a : ℕ → ℝ) (hweights : ∀ n, |a n| ≤ 2)
    (hcoeff : ∀ w : ℂ, 2 < w.re →
      LSeries (fun n => (a n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) w =
        -logDeriv archivedGaussianFactor w)
    (hwindows : GaussianWindows (gaussianLogCutoffRamp a)) :
    DedekindZetaRH K :=
  quartic_rh_of_gaussian_ramp_checked_real_poles hD _
    (gaussianLogCutoffRamp_measurable a) (gaussianLogCutoffRamp_growth a hweights)
    (fun w hw => gaussianLogCutoffRamp_laplace a hweights hw (hcoeff w hw)) hwindows

/-- A pointwise bound on norm windows gives the integrated bound on the
corresponding logarithmic windows. -/
theorem logWindow_of_pointwise_norm_windows (f : ℝ → ℝ) {θ δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (hcut : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      f y ≤ C * y ^ θ) :
    Deduction.WindowHypU (fun u => f (Real.exp u)) θ δ := by
  intro η hη U₀
  let start := max U₀ (max 0 (4 * C * δ / η ^ 2))
  obtain ⟨Y, hY, hW⟩ := hcut (Real.exp start)
  have hYpos := (Real.exp_pos start).trans_le hY
  let U := Real.log Y
  have hYexp : Real.exp U = Y := Real.exp_log hYpos
  have hsU : start ≤ U := Real.exp_le_exp.mp (by rwa [hYexp])
  have hU₀ : U₀ ≤ U := (le_max_left _ _).trans hsU
  have hU : 0 ≤ U := ((le_max_left _ _).trans (le_max_right _ _)).trans hsU
  have hstart : 4 * C * δ / η ^ 2 ≤ U :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hsU
  have hkernel (u : ℝ) : C * Real.exp (θ * u) * Real.exp (-θ * u) = C := by
    rw [mul_assoc, ← Real.exp_add, show θ * u + -θ * u = 0 by ring, Real.exp_zero, mul_one]
  refine ⟨U, hU₀, fun u => C * Real.exp (θ * u), ?_, ?_, ?_⟩
  · simp_rw [hkernel]
    exact integrableOn_const (by simp)
  · intro u hu
    refine ⟨mul_nonneg hC (Real.exp_nonneg _), ?_⟩
    have hub : Real.exp ((1 + δ) * U) = Y ^ (1 + δ) := by
      rw [Real.rpow_def_of_pos hYpos, mul_comm]
    have hymem : Real.exp u ∈ Icc Y (Y ^ (1 + δ)) :=
      ⟨hYexp ▸ Real.exp_le_exp.mpr hu.1, hub ▸ Real.exp_le_exp.mpr hu.2⟩
    simpa [Real.rpow_def_of_pos (Real.exp_pos u),
      Real.log_exp, mul_comm u θ] using hW _ hymem
  · have hwidth : U ≤ (1 + δ) * U := by nlinarith
    simp_rw [hkernel]
    rw [setIntegral_const, Real.volume_real_Icc_of_le hwidth, smul_eq_mul]
    have hlin := (div_le_iff₀ (sq_pos_of_pos hη)).mp hstart
    have hquad := mul_le_mul_of_nonneg_right hlin hU
    have hx : 0 ≤ η * U / 2 := by positivity
    have hb : η * U / 2 ≤ Real.exp (η * U / 2) := by
      linarith [Real.add_one_le_exp (η * U / 2)]
    calc
      _ ≤ (η * U / 2) ^ 2 := by nlinarith
      _ ≤ Real.exp (η * U / 2) ^ 2 :=
        (sq_le_sq₀ hx (Real.exp_nonneg _)).mpr hb
      _ = _ := by rw [pow_two, ← Real.exp_add]; congr 1; ring

theorem gaussianLogWindow_of_pointwise_norm_windows (a : ℕ → ℝ) {θ δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C)
    (hcut : ∀ Y₀ : ℝ, ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)),
      gaussianPrimeNormRamp a y ≤ C * y ^ θ) :
    Deduction.WindowHypU (gaussianLogCutoffRamp a) θ δ :=
  logWindow_of_pointwise_norm_windows (gaussianPrimeNormRamp a) hδ hC hcut

theorem quartic_rh_of_pointwise_gaussian_prime_norm_windows (hD : DirichletLZerosOnLine)
    (a : ℕ → ℝ) (hweights : ∀ n, |a n| ≤ 2)
    (hcoeff : ∀ w : ℂ, 2 < w.re →
      LSeries (fun n => (a n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) w =
        -logDeriv archivedGaussianFactor w)
    (hcut : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C ≥ 0, ∀ Y₀ : ℝ,
        ∃ Y ≥ Y₀, ∀ y ∈ Icc Y (Y ^ (1 + δ)), gaussianPrimeNormRamp a y ≤ C * y ^ θ) :
    DedekindZetaRH K := by
  apply quartic_rh_of_gaussian_prime_norm_windows hD a hweights hcoeff
  intro θ hθ hθ'
  obtain ⟨δ, hδ, C, hC, hW⟩ := hcut θ hθ hθ'
  exact ⟨δ, hδ, gaussianLogWindow_of_pointwise_norm_windows a hδ hC hW⟩

#check quartic_rh_of_gaussian_prime_norm_windows
#check quartic_rh_of_pointwise_gaussian_prime_norm_windows
#print axioms gaussian_logDeriv_one_isReal
#print axioms gaussianLogCutoffRamp_growth
#print axioms gaussianLogCutoffRamp_laplace
#print axioms quartic_rh_of_gaussian_prime_norm_windows
#print axioms logWindow_of_pointwise_norm_windows
#print axioms gaussianLogWindow_of_pointwise_norm_windows
#print axioms quartic_rh_of_pointwise_gaussian_prime_norm_windows

end
end AlpogeSuperZeta
