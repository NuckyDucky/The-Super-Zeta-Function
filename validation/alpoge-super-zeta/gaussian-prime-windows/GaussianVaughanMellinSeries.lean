import GaussianVaughanKernelBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The actual Gaussian coefficient sum has the claimed Mellin transform.
The absolutely convergent series supplies the half-plane identity used by
the pole criterion. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory Set QuarticModel FieldTarget ArtinPrimitiveRootsConjecture
open scoped ENNReal

noncomputable section

private theorem mellin_div_input (g : ℝ → ℂ) (z : ℂ) {a : ℝ} (ha : 0 < a) :
    mellin (fun x => g (a / x)) (-z) = (a : ℂ) ^ (-z) * mellin g z := by
  calc
    mellin (fun x => g (a / x)) (-z) =
        mellin (fun x => (fun t : ℝ => g (a * t)) x⁻¹) (-z) := by
      simp only [div_eq_mul_inv]
    _ = mellin (fun x => g (a * x)) z := by
      rw [mellin_comp_inv (fun t => g (a * t)), neg_neg]
    _ = _ := mellin_comp_mul_left g z ha

private theorem mellinConvergent_div_input {g : ℝ → ℂ} {z : ℂ}
    (hg : MellinConvergent g z) {a : ℝ} (ha : 0 < a) :
    MellinConvergent (fun x => g (a / x)) (-z) := by
  have hM := (MellinConvergent.comp_mul_left ha).2 hg
  have hInv := (MellinConvergent.comp_rpow (f := fun x => g (a * x)) (s := -z)
    (a := (-1 : ℝ)) (by norm_num)).2 (by simpa using hM)
  simpa only [Real.rpow_neg_one, div_eq_mul_inv] using hInv

private theorem mellin_integral_norm_cast (g : ℝ → ℂ) (z : ℂ) :
    (↑(∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (z - 1) * g x‖) : ℂ) =
      mellin (fun x => (‖g x‖ : ℂ)) (z.re : ℂ) := by
  rw [← integral_complex_ofReal, mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  change 0 < x at hx
  change (‖(x : ℂ) ^ (z - 1) * g x‖ : ℂ) = (x : ℂ) ^ ((z.re : ℂ) - 1) • (‖g x‖ : ℂ)
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, ofReal_mul, smul_eq_mul,
    ofReal_cpow hx.le, sub_re, one_re, ofReal_sub, ofReal_one]

private theorem mellin_div_input_norm (g : ℝ → ℂ) (z : ℂ) {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (-z - 1) * g (a / x)‖) =
      a ^ (-z.re) * ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (z - 1) * g x‖ := by
  apply Complex.ofReal_injective
  rw [mellin_integral_norm_cast (fun x => g (a / x)) (-z), neg_re, ofReal_neg,
    mellin_div_input (fun x => (‖g x‖ : ℂ)) (z.re : ℂ) ha, ofReal_mul,
    ofReal_cpow ha.le, ofReal_neg,
    mellin_integral_norm_cast]

def dirichletKernelSum (a : ArithmeticFunction ℂ) (H : ℝ → ℂ) (v : ℝ) : ℂ :=
  ∑' n : ℕ, a n * H (n * v)

private theorem dirichletKernelSum_div_hasMellin (a : ArithmeticFunction ℂ)
    {H : ℝ → ℂ} {z m : ℂ} (hH : HasMellin H z m)
    (ha : LSeriesSummable a (z.re : ℂ)) :
    HasMellin (fun x : ℝ => ∑' n : ℕ, a n * H (n / x)) (-z)
      (m * LSeries a z) := by
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let F (n : ℕ) (x : ℝ) : ℂ :=
    a n * ((x : ℂ) ^ (-z - 1) * H (n / x))
  have hInt (n : ℕ) : Integrable (F n) μ := by
    by_cases hn : n = 0
    · subst n
      simp [F]
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simpa only [F, μ, IntegrableOn, MellinConvergent, smul_eq_mul, mul_left_comm] using
      (mellinConvergent_div_input hH.1 hn₀).const_smul (a n)
  let I := ∫ x in Ioi (0 : ℝ), ‖(x : ℂ) ^ (z - 1) * H x‖
  have hNorm (n : ℕ) : (∫ x, ‖F n x‖ ∂μ) =
      ‖LSeries.term a (z.re : ℂ) n‖ * I := by
    by_cases hn : n = 0
    · subst n
      simp [F]
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    simp only [F, μ, norm_mul (a n), integral_const_mul]
    rw [mellin_div_input_norm H z hn₀, LSeries.term_of_ne_zero hn, norm_div,
      ← Complex.ofReal_natCast, norm_cpow_eq_rpow_re_of_pos hn₀, ofReal_re,
      Real.rpow_neg hn₀.le, div_eq_mul_inv]
    unfold I
    ring
  have hNormSum : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    simp_rw [hNorm]
    exact ha.norm.mul_right I
  have hENorm (n : ℕ) :
      (∫⁻ x, ‖F n x‖ₑ ∂μ) = ‖(∫ x, ‖F n x‖ ∂μ)‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hInt n).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F n x))]
    simp only [coe_nnnorm]
  have hSummableLIntegral : (∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ) ≠ ∞ := by
    simp_rw [hENorm]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hNormSum.abs)
  have hIntSum : Integrable (fun x => ∑' n, F n x) μ := by
    refine ⟨(AEMeasurable.tsum (fun n => (hInt n).1.aemeasurable)).aestronglyMeasurable,
      hasFiniteIntegral_iff_enorm.2 ?_⟩
    apply lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm (f := fun n => F n x))
    rw [lintegral_tsum (fun n => (hInt n).1.aemeasurable.enorm)]
    exact lt_top_iff_ne_top.mpr hSummableLIntegral
  have hPoint : EqOn (fun x => ∑' n, F n x)
      (fun x : ℝ => (x : ℂ) ^ (-z - 1) • (∑' n : ℕ, a n * H (n / x))) (Ioi 0) := by
    intro x _
    simp only [smul_eq_mul, ← tsum_mul_left, F, mul_left_comm]
  refine ⟨(show IntegrableOn (fun x => ∑' n, F n x) (Ioi (0 : ℝ)) volume from hIntSum).congr_fun
    hPoint measurableSet_Ioi, ?_⟩
  have hterm (n : ℕ) :
      (∫ x, F n x ∂μ) =
        m * LSeries.term a z n := by
    by_cases hn : n = 0
    · subst n
      simp [F]
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    change (∫ x in Ioi (0 : ℝ), a n *
      ((x : ℂ) ^ (-z - 1) * H (n / x))) = _
    rw [integral_const_mul]
    change a n * mellin (fun x => H ((n : ℝ) / x)) (-z) = _
    rw [mellin_div_input H z hn₀, hH.2, LSeries.term_of_ne_zero hn, Complex.ofReal_natCast,
      Complex.cpow_neg, div_eq_mul_inv]
    ring
  calc
    mellin (fun x : ℝ => ∑' n : ℕ, a n * H (n / x)) (-z) =
        ∫ x, (∑' n, F n x) ∂μ :=
      setIntegral_congr_fun measurableSet_Ioi hPoint.symm
    _ = ∑' n, ∫ x, F n x ∂μ := (integral_tsum_of_summable_integral_norm hInt hNormSum).symm
    _ = m * LSeries a z := by simp only [hterm, tsum_mul_left, LSeries]

/-- Absolute convergence lets the Mellin transform of a dilated kernel
sum read the full Dirichlet coefficient sequence. -/
theorem dirichletKernelSum_hasMellin (a : ArithmeticFunction ℂ)
    {H : ℝ → ℂ} {z m : ℂ} (hH : HasMellin H z m)
    (ha : LSeriesSummable a (z.re : ℂ)) :
    HasMellin (dirichletKernelSum a H) z (m * LSeries a z) := by
  let f (x : ℝ) := ∑' n : ℕ, a n * H (n / x)
  have hf : HasMellin f (-z) (m * LSeries a z) :=
    dirichletKernelSum_div_hasMellin a hH ha
  have hinv : HasMellin (fun x => f x⁻¹) (-(-z)) (m * LSeries a z) := by
    refine ⟨?_, ?_⟩
    · simpa only [one_div] using mellinConvergent_div_input hf.1 (a := 1) one_pos
    · rw [mellin_comp_inv, neg_neg]
      exact hf.2
  change HasMellin (fun x : ℝ => ∑' n : ℕ, a n * H (n * x)) z (m * LSeries a z)
  simpa only [f, div_inv_eq_mul, neg_neg] using hinv

private theorem archivedGaussianMangoldt_ofReal_re (n : ℕ) :
    ((archivedGaussianMangoldt n).re : ℂ) = archivedGaussianMangoldt n := by
  simp [archivedGaussianMangoldt, ← Complex.ofReal_mul]

theorem archivedGaussianVaughanSum_hasMellin {z : ℂ} (hz : 1 < z.re) :
    HasMellin (fun x => (archivedGaussianVaughanSum x : ℂ)) (-z)
      (archivedGaussianVaughanMellin z) := by
  let H (v : ℝ) : ℂ := archivedGaussianVaughanKernel v
  have hH : HasMellin H z (archivedGaussianVaughanMultiplier z) :=
    archivedGaussianVaughanKernel_hasMellin (zero_lt_one.trans hz)
  have h := dirichletKernelSum_div_hasMellin archivedGaussianMangoldt hH
    (archivedGaussianMangoldt_summable (by simpa using hz))
  have hEq : EqOn (fun x : ℝ => ∑' n : ℕ, archivedGaussianMangoldt n * H (n / x))
      (fun x => (archivedGaussianVaughanSum x : ℂ)) (Ioi 0) := by
    intro x hx
    change 0 < x at hx
    simp only [archivedGaussianVaughanSum, if_pos hx, Complex.ofReal_tsum, H,
      ofReal_mul, archivedGaussianMangoldt_ofReal_re]
  have hWeight : EqOn
      (fun x : ℝ => (x : ℂ) ^ (-z - 1) • (∑' n : ℕ, archivedGaussianMangoldt n * H (n / x)))
      (fun x : ℝ => (x : ℂ) ^ (-z - 1) • (archivedGaussianVaughanSum x : ℂ)) (Ioi 0) :=
    fun x hx => congrArg ((x : ℂ) ^ (-z - 1) • ·) (hEq hx)
  refine ⟨h.1.congr_fun hWeight measurableSet_Ioi, ?_⟩
  rw [archivedGaussianVaughanMellin_eq_series hz, ← h.2]
  exact setIntegral_congr_fun measurableSet_Ioi hWeight.symm

/-- Moving the lower endpoint to one subtracts the explicit entire
endpoint integral. -/
theorem archivedGaussianVaughanSum_mellin_above_one {z : ℂ} (hz : 1 < z.re) :
    (∫ x in Ioi (1 : ℝ), (archivedGaussianVaughanSum x : ℂ) * (x : ℂ) ^ (-z - 1)) =
      archivedGaussianVaughanMellin z - archivedGaussianVaughanEndpoint z := by
  have h := archivedGaussianVaughanSum_hasMellin hz
  let f (x : ℝ) := (archivedGaussianVaughanSum x : ℂ) * (x : ℂ) ^ (-z - 1)
  have hI : IntegrableOn f (Ioi 0) := by
    simpa only [f, MellinConvergent, smul_eq_mul, mul_comm] using h.1
  have hSplit :
      (∫ x in Ioc (0 : ℝ) 1, f x) + (∫ x in Ioi (1 : ℝ), f x) =
        ∫ x in Ioi (0 : ℝ), f x := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hI.mono_set fun _ hx => hx.1)
      (hI.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))),
      Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num)]
  have hFull : (∫ x in Ioi (0 : ℝ), f x) = archivedGaussianVaughanMellin z := by
    simpa only [mellin, f, smul_eq_mul, mul_comm] using h.2
  rw [hFull, ← archivedGaussianVaughanEndpoint_eq_integral] at hSplit
  exact eq_sub_of_add_eq (by rw [add_comm]; exact hSplit)

/-- The power bound and Mellin identity for the actual Gaussian sum are
supplied by proved lemmas. The analytic approximation and late signed
prime-window bound are explicit inputs. -/
theorem quartic_rh_of_archived_vaughan_prime_windows
    (hDir : DirichletLZerosOnLine)
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (W : ℝ → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hError : ∀ᶠ x in atTop, |archivedGaussianVaughanSum x -
      archivedGaussianVaughanLowerSum W x| ≤ C * (x ^ (3 / 8 : ℝ) *
        (Real.log x) ^ (8 / 3 : ℝ)))
    (hcut : GaussianCutoffWindowBound (archivedGaussianVaughanLowerSum W)) :
    DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_vaughan_lower_windows hDir hFree hpos W
    archivedGaussianVaughanEndpoint archivedGaussianVaughanEndpoint_entire
    archivedGaussianVaughanSum_growth
    (fun _ hz => archivedGaussianVaughanSum_mellin_above_one (by linarith))
    hC hError hcut

#print axioms dirichletKernelSum_hasMellin
#print axioms archivedGaussianVaughanSum_hasMellin
#print axioms archivedGaussianVaughanSum_mellin_above_one
#check quartic_rh_of_archived_vaughan_prime_windows
#print axioms quartic_rh_of_archived_vaughan_prime_windows

end
end AlpogeSuperZeta
