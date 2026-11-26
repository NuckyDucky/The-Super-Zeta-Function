import ArchivedGaussianEulerDerivative
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.LSeries.Deriv

/-! Identify the actual Gaussian arithmetic function with the logarithmic
derivative of the analytically continued Hecke factor in its convergence region. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Filter PowerSeries QuarticModel FieldTarget
open ArtinPrimitiveRootsConjecture
open scoped Classical Topology

noncomputable section

/-- The signed prime-power coefficients, including the von Mangoldt weight. -/
def archivedGaussianMangoldt : ArithmeticFunction ℂ :=
  ⟨fun n => (archivedGaussianPrimeWeight n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ), by simp⟩

private def gaussianLogTimesCoefficients : ArithmeticFunction ℂ :=
  ⟨LSeries.logMul signedIdealCoefficients, by simp [LSeries.logMul]⟩

private theorem gaussianLogTimesCoefficients_apply (n : ℕ) :
    gaussianLogTimesCoefficients n = Complex.log (n : ℂ) * signedIdealCoefficients n := rfl

private theorem coeff_signed_local {p : ℕ} (hp : p.Prime) (j : ℕ) :
    signedIdealCoefficients (p ^ j) = coeff j (signedLocalEulerSeries p) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← signedIdealNormSum_primePower p j]
  simp only [signedIdealCoefficients, toArithmeticFunction, ArithmeticFunction.coe_mk,
    if_neg (pow_ne_zero _ hp.ne_zero)]

private theorem mangoldt_at_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    archivedGaussianMangoldt (p ^ j) =
      coeff j (PowerSeries.C (Complex.log (p : ℂ)) * archivedGaussianEulerLogSeries p) := by
  cases j with
  | zero => simp [archivedGaussianMangoldt, coeff_C_mul]
  | succ j =>
    rw [coeff_C_mul, archivedGaussianEulerLogSeries_coeff p _ j.succ_ne_zero]
    change (archivedGaussianPrimeWeight (p ^ (j + 1)) : ℂ) *
      (ArithmeticFunction.vonMangoldt (p ^ (j + 1)) : ℂ) = _
    rw [archivedGaussianPrimeWeight_prime_power hp j.succ_ne_zero,
      ArithmeticFunction.vonMangoldt_apply_pow j.succ_ne_zero,
      ArithmeticFunction.vonMangoldt_apply_prime hp, Complex.natCast_log, mul_comm]

private theorem convolution_coeff_prime_power {p : ℕ} (hp : p.Prime) {j : ℕ}
    {f g : ArithmeticFunction ℂ} {F G : PowerSeries ℂ}
    (hf : ∀ k, f (p ^ k) = coeff k F) (hg : ∀ k, g (p ^ k) = coeff k G) :
    (f * g) (p ^ j) = coeff j (F * G) := by
  rw [← ofPowerSeries_apply_pow hp.one_lt, map_mul, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro pair hm
  have hd₁ := Nat.dvd_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hm)
  have hd₂ := Nat.dvd_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hm)
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow hp).mp hd₁
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow hp).mp hd₂
  rw [hi, hk, ofPowerSeries_apply_pow hp.one_lt, ofPowerSeries_apply_pow hp.one_lt, hf, hg]

private theorem complex_log_nat_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    Complex.log ((m * n : ℕ) : ℂ) = Complex.log (m : ℂ) + Complex.log (n : ℂ) := by
  rw [← Complex.natCast_log, ← Complex.natCast_log (n := m), ← Complex.natCast_log (n := n),
    Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hn),
    Complex.ofReal_add]

private theorem convolution_at_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    (archivedGaussianMangoldt * signedIdealCoefficients) (p ^ j) =
      gaussianLogTimesCoefficients (p ^ j) := by
  rw [convolution_coeff_prime_power hp (mangoldt_at_pow hp) (coeff_signed_local hp),
    mul_assoc, mul_comm (archivedGaussianEulerLogSeries p) (signedLocalEulerSeries p),
    ← signedLocalEulerSeries_derivative, coeff_C_mul, gaussianLogTimesCoefficients_apply,
    coeff_signed_local hp]
  have hD (F : PowerSeries ℂ) : coeff j (PowerSeries.X * PowerSeries.derivative ℂ F) =
      (j : ℂ) * coeff j F := by
    cases j with
    | zero => simp only [coeff_zero_X_mul, Nat.cast_zero, zero_mul]
    | succ j => rw [coeff_succ_X_mul, coeff_derivative, mul_comm, Nat.cast_succ]
  rw [hD, ← Complex.natCast_log, ← Complex.natCast_log (n := p ^ j),
    Nat.cast_pow, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast]
  ring

private abbrev ComplexDual := TrivSqZeroExt ℂ ℂ

private def withDerivative (f df : ArithmeticFunction ℂ) : ArithmeticFunction ComplexDual :=
  ⟨fun n => (f n, df n), by rw [f.map_zero, df.map_zero]; rfl⟩

@[simp] private theorem withDerivative_fst (f df : ArithmeticFunction ℂ) (n : ℕ) :
    (withDerivative f df n).fst = f n := rfl

@[simp] private theorem withDerivative_snd (f df : ArithmeticFunction ℂ) (n : ℕ) :
    (withDerivative f df n).snd = df n := rfl

private theorem withDerivative_mul_right (f df g : ArithmeticFunction ℂ) :
    withDerivative f df * withDerivative g 0 = withDerivative (f * g) (df * g) := by
  ext n : 1
  rw [ArithmeticFunction.mul_apply]
  apply TrivSqZeroExt.ext
  · simp [TrivSqZeroExt.fst_sum, ArithmeticFunction.mul_apply]
  · simp [TrivSqZeroExt.snd_sum, ArithmeticFunction.mul_apply, smul_eq_mul]

private theorem withDerivative_isMultiplicative {f df : ArithmeticFunction ℂ}
    (hf : f.IsMultiplicative) (h1 : df 1 = 0)
    (hprod : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n →
      df (m * n) = f m * df n + df m * f n) :
    (withDerivative f df).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨?_, ?_⟩
  · exact TrivSqZeroExt.ext hf.1 h1
  · intro m n hm hn hmn
    apply TrivSqZeroExt.ext
    · simpa using hf.map_mul_of_coprime hmn
    · simpa [smul_eq_mul] using hprod hm hn hmn

private theorem one_with_mangoldt_multiplicative :
    (withDerivative 1 archivedGaussianMangoldt).IsMultiplicative := by
  apply withDerivative_isMultiplicative ArithmeticFunction.isMultiplicative_one
  · simp [archivedGaussianMangoldt]
  · intro m n _ _ hmn
    by_cases hm : m = 1
    · subst m
      simp [archivedGaussianMangoldt]
    by_cases hn : n = 1
    · subst n
      simp [archivedGaussianMangoldt]
    have hnone : ¬ IsPrimePow (m * n) := by
      intro hp
      rcases (hmn.isPrimePow_dvd_mul hp).mp (dvd_refl _) with h | h
      · have hd : n ∣ m * n := ⟨m, mul_comm m n⟩
        exact hn (Nat.eq_one_of_dvd_coprimes hmn (hd.trans h) (dvd_refl n))
      · have hd : m ∣ m * n := ⟨n, rfl⟩
        exact hm (Nat.eq_one_of_dvd_coprimes hmn (dvd_refl m) (hd.trans h))
    simp [archivedGaussianMangoldt, ArithmeticFunction.one_apply_ne hm,
      ArithmeticFunction.one_apply_ne hn, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hnone]

private theorem gaussian_with_log_multiplicative :
    (withDerivative signedIdealCoefficients gaussianLogTimesCoefficients).IsMultiplicative := by
  apply withDerivative_isMultiplicative signedIdealCoefficients_multiplicative
  · simp [gaussianLogTimesCoefficients_apply]
  · intro m n hm hn hmn
    simp only [gaussianLogTimesCoefficients_apply, complex_log_nat_mul hm hn,
      signedIdealCoefficients_multiplicative.map_mul_of_coprime hmn]
    ring

/-- The signed prime-power sequence convolves with the quartic's actual
Gaussian coefficients to give the coefficientwise logarithmic weight. -/
theorem archivedGaussianMangoldt_convolution :
    ((archivedGaussianMangoldt * signedIdealCoefficients : ArithmeticFunction ℂ) : ℕ → ℂ) =
      LSeries.logMul signedIdealCoefficients := by
  have hconv : (withDerivative signedIdealCoefficients
      (archivedGaussianMangoldt * signedIdealCoefficients)).IsMultiplicative := by
    have hzero : (withDerivative signedIdealCoefficients 0).IsMultiplicative :=
      withDerivative_isMultiplicative signedIdealCoefficients_multiplicative
        (by simp) (by intros; simp)
    have hmul := one_with_mangoldt_multiplicative.mul hzero
    rwa [withDerivative_mul_right, one_mul] at hmul
  have h := (IsMultiplicative.eq_iff_eq_on_prime_powers _ hconv _
    gaussian_with_log_multiplicative).2 (fun p j hp =>
      TrivSqZeroExt.ext rfl (convolution_at_pow hp j))
  funext n
  exact congrArg (fun f : ArithmeticFunction ComplexDual => (f n).snd) h

theorem archivedGaussianMangoldt_summable {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable archivedGaussianMangoldt w := by
  have hbase := (ArithmeticFunction.LSeriesSummable_vonMangoldt hw).norm.mul_left (2 : ℝ)
  rw [LSeriesSummable, ← summable_norm_iff]
  refine hbase.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => ?_
  have ht : LSeries.term archivedGaussianMangoldt w n =
      (archivedGaussianPrimeWeight n : ℂ) *
        LSeries.term (fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) w n := by
    by_cases hn : n = 0
    · simp [hn]
    · simp only [LSeries.term_of_ne_zero hn, archivedGaussianMangoldt, ArithmeticFunction.coe_mk,
        mul_div_assoc]
  rw [ht, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (by simpa [Complex.norm_real, Real.norm_eq_abs] using archivedGaussianPrimeWeight_abs_le_two n)
    (norm_nonneg _)

theorem archivedGaussianFactor_deriv_eq_mangoldt_mul {w : ℂ} (hw : 1 < w.re) :
    deriv archivedGaussianFactor w = -(LSeries archivedGaussianMangoldt w * archivedGaussianFactor w) := by
  have hc : LSeries.abscissaOfAbsConv signedIdealCoefficients ≤ (1 : ℝ) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro z hz
    exact (archivedGaussianFactor_hasSum hz).LSeriesSummable
  have hnear : archivedGaussianFactor =ᶠ[𝓝 w] LSeries signedIdealCoefficients := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hz
    exact (archivedGaussianFactor_hasSum hz).LSeries_eq.symm
  have hconv := ArithmeticFunction.LSeries_mul' (archivedGaussianMangoldt_summable hw)
    (archivedGaussianFactor_hasSum hw).LSeriesSummable
  rw [archivedGaussianMangoldt_convolution, (archivedGaussianFactor_hasSum hw).LSeries_eq] at hconv
  rw [hnear.deriv_eq, LSeries_deriv (hc.trans_lt (EReal.coe_lt_coe_iff.mpr hw)), hconv]

/-- The derivative identity forces the actual factor to be zero-free in
the common half-plane of convergence. At a zero, the derivative would
have smaller order than a holomorphic multiple of the factor. -/
theorem archivedGaussianFactor_ne_zero_of_re_gt_one {w : ℂ} (hw : 1 < w.re) :
    archivedGaussianFactor w ≠ 0 := by
  intro hz
  have hG : AnalyticAt ℂ archivedGaussianFactor w := archivedGaussianFactor_entire.analyticAt w
  have hA : AnalyticAt ℂ (LSeries archivedGaussianMangoldt) w := by
    apply LSeries_analyticOnNhd
    have hc : LSeries.abscissaOfAbsConv archivedGaussianMangoldt ≤ (1 : ℝ) := by
      apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      intro σ hσ
      exact archivedGaussianMangoldt_summable (by simpa using hσ)
    exact hc.trans_lt (EReal.coe_lt_coe_iff.mpr hw)
  have hfinite : analyticOrderAt archivedGaussianFactor w ≠ ⊤ := by
    intro htop
    have hzero : archivedGaussianFactor =ᶠ[𝓝 w] fun _ => 0 :=
      analyticOrderAt_eq_top.mp htop
    have hall := AnalyticOnNhd.eq_of_eventuallyEq
      (fun z _ => archivedGaussianFactor_entire.analyticAt z) analyticOnNhd_const hzero
    exact quartic_gaussian_one_ne_zero (congrFun hall 1)
  have hnear : deriv archivedGaussianFactor =ᶠ[𝓝 w]
      (-LSeries archivedGaussianMangoldt) * archivedGaussianFactor := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hzw
    simpa only [Pi.mul_apply, Pi.neg_apply, neg_mul] using
      archivedGaussianFactor_deriv_eq_mangoldt_mul hzw
  have horder : analyticOrderAt (deriv archivedGaussianFactor) w + 1 =
      analyticOrderAt archivedGaussianFactor w := by
    simpa [hz] using hG.analyticOrderAt_deriv_add_one
  rw [analyticOrderAt_congr hnear, analyticOrderAt_mul hA.neg hG] at horder
  have hlt := (ENat.lt_add_one_iff hfinite).2 le_rfl
  have hle : analyticOrderAt archivedGaussianFactor w + 1 ≤
      (analyticOrderAt (-LSeries archivedGaussianMangoldt) w +
        analyticOrderAt archivedGaussianFactor w) + 1 :=
    add_le_add (le_add_of_nonneg_left zero_le) le_rfl
  exact (hlt.trans_le hle).not_ge horder.le

/-- The archived prime-power weights give the exact logarithmic derivative
of the quartic's Gaussian factor. -/
theorem archivedGaussianMangoldt_eq_neg_logDeriv {w : ℂ} (hw : 1 < w.re) :
    LSeries archivedGaussianMangoldt w = -logDeriv archivedGaussianFactor w := by
  rw [logDeriv_apply, ← neg_div, neg_eq_iff_eq_neg.mpr (archivedGaussianFactor_deriv_eq_mangoldt_mul hw),
    mul_div_cancel_right₀ _ (archivedGaussianFactor_ne_zero_of_re_gt_one hw)]

/-- The arithmetic estimate sufficient for the quartic via the
prime-norm window argument. The constants can depend on the exponent. -/
def ArchivedGaussianPrimeWindowBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C ≥ 0, ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)),
        gaussianPrimeNormRamp archivedGaussianPrimeWeight y ≤ C * y ^ θ

theorem quartic_rh_of_archived_gaussian_window_bound (hD : DirichletLZerosOnLine)
    (hcut : ArchivedGaussianPrimeWindowBound) : DedekindZetaRH K :=
  quartic_rh_of_archived_gaussian_prime_windows hD
    (fun _ hw => archivedGaussianMangoldt_eq_neg_logDeriv (by linarith)) hcut

#print axioms archivedGaussianMangoldt_convolution
#print axioms archivedGaussianFactor_deriv_eq_mangoldt_mul
#print axioms archivedGaussianFactor_ne_zero_of_re_gt_one
#print axioms archivedGaussianMangoldt_eq_neg_logDeriv
#check quartic_rh_of_archived_gaussian_window_bound
#print ArchivedGaussianPrimeWindowBound
#print axioms quartic_rh_of_archived_gaussian_window_bound

end
end AlpogeSuperZeta
