import GaussianVaughanRationalSquares
import GaussianVaughanFilteredDirichlet

/-! Continue the actual weighted Gaussian higher-power series to the
half-plane containing the logarithmic-window contour. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex DirichletCharacter Finset QuarticModel
open scoped Classical

noncomputable section

private theorem exceptional_support (n : ℕ)
    (hn : n ∉ archivedGaussianRationalLevel.primeFactors) :
    archivedGaussianExceptionalMangoldt n = 0 := by
  apply if_neg
  rintro ⟨hp, hd⟩
  exact hn (Nat.mem_primeFactors.mpr ⟨hp, hd, by norm_num⟩)

private theorem exceptional_LSeries (z : ℂ) :
    LSeries archivedGaussianExceptionalMangoldt z =
      ∑ p ∈ archivedGaussianRationalLevel.primeFactors, LSeries.term archivedGaussianExceptionalMangoldt z p := by
  unfold LSeries
  exact tsum_eq_sum (fun n hn => by
    simp only [LSeries.term, exceptional_support n hn, zero_div, ite_self])

private theorem exceptional_summable (z : ℂ) :
    LSeriesSummable archivedGaussianExceptionalMangoldt z :=
  summable_of_ne_finset_zero (s := archivedGaussianRationalLevel.primeFactors) (fun n hn => by
    simp only [LSeries.term, exceptional_support n hn, zero_div, ite_self])

private theorem exceptional_entire : Differentiable ℂ (LSeries archivedGaussianExceptionalMangoldt) := by
  have he : LSeries archivedGaussianExceptionalMangoldt =
      fun z => ∑ p ∈ archivedGaussianRationalLevel.primeFactors,
        LSeries.term archivedGaussianExceptionalMangoldt z p := funext exceptional_LSeries
  rw [he]
  apply Differentiable.fun_sum
  intro p hp
  have hp₀ : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
  let _ : NeZero p := ⟨hp₀⟩
  simp only [LSeries.term_of_ne_zero hp₀, div_eq_mul_inv, ← Complex.cpow_neg]
  fun_prop

private def mangoldtTwist {N : ℕ} (χ : DirichletCharacter ℂ N) : ℕ → ℂ :=
  fun n => χ (n : ZMod N) * (vonMangoldt n : ℂ)

private theorem mangoldtTwist_summable {N : ℕ} (χ : DirichletCharacter ℂ N)
    {w : ℂ} (hw : 1 < w.re) : LSeriesSummable (mangoldtTwist χ) w :=
  LSeriesSummable_twist_vonMangoldt χ hw

private theorem mangoldtTwist_LSeries {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {w : ℂ} (hw : 1 < w.re) :
    LSeries (mangoldtTwist χ) w = -logDeriv (LFunction χ) w := by
  rw [logDeriv_apply, ← neg_div, deriv_LFunction_eq_deriv_LSeries χ hw,
    LFunction_eq_LSeries χ hw]
  exact LSeries_twist_vonMangoldt_eq χ hw

private abbrev χ₁ : DirichletCharacter ℂ archivedGaussianRationalLevel := 1
private abbrev χ₂ := archivedGaussianRationalChi4
private abbrev χ₃ := archivedGaussianNormCharacter
private abbrev χ₄ := χ₂ * χ₃

private theorem rationalMangoldt_eq :
    (archivedGaussianRationalMangoldt : ℕ → ℂ) =
      mangoldtTwist χ₁ + mangoldtTwist χ₂ + mangoldtTwist χ₃ - mangoldtTwist χ₄ := by
  funext n
  simp only [archivedGaussianRationalMangoldt, ArithmeticFunction.coe_mk,
    archivedGaussianRationalSquareWeight, mangoldtTwist, Pi.sub_apply, Pi.add_apply]
  ring

private theorem rationalMangoldt_summable {w : ℂ} (hw : 1 < w.re) :
    LSeriesSummable archivedGaussianRationalMangoldt w := by
  rw [rationalMangoldt_eq]
  exact (((mangoldtTwist_summable χ₁ hw).add (mangoldtTwist_summable χ₂ hw)).add
    (mangoldtTwist_summable χ₃ hw)).sub (mangoldtTwist_summable χ₄ hw)

private theorem rationalMangoldt_LSeries {w : ℂ} (hw : 1 < w.re) :
    LSeries archivedGaussianRationalMangoldt w =
      -logDeriv (LFunction χ₁) w + -logDeriv (LFunction χ₂) w +
        -logDeriv (LFunction χ₃) w - -logDeriv (LFunction χ₄) w := by
  rw [rationalMangoldt_eq, LSeries_sub
    (((mangoldtTwist_summable χ₁ hw).add (mangoldtTwist_summable χ₂ hw)).add
      (mangoldtTwist_summable χ₃ hw)) (mangoldtTwist_summable χ₄ hw),
    LSeries_add ((mangoldtTwist_summable χ₁ hw).add (mangoldtTwist_summable χ₂ hw))
      (mangoldtTwist_summable χ₃ hw),
    LSeries_add (mangoldtTwist_summable χ₁ hw) (mangoldtTwist_summable χ₂ hw)]
  simp only [mangoldtTwist_LSeries _ hw]

private abbrev rationalTail := primePowerTail 2 archivedGaussianRationalMangoldt
private abbrev gaussianTail := primePowerTail 3 archivedGaussianMangoldt

private theorem rationalTail_summable {w : ℂ} (hw : 1 / 2 < w.re) :
    LSeriesSummable rationalTail w := by
  apply primePowerTail_summable 2 _ (by norm_num : (0 : ℝ) ≤ 4) archivedGaussianRationalMangoldt_norm_le
  · linarith
  · norm_num
    linarith

private theorem rationalTail_analyticAt {w : ℂ} (hw : 1 / 2 < w.re) :
    AnalyticAt ℂ (LSeries rationalTail) w := by
  have ha : LSeries.abscissaOfAbsConv rationalTail ≤ ((1 / 2 : ℝ) : EReal) := by
    apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
    intro t ht
    exact rationalTail_summable (by simpa using ht)
  exact LSeries_analyticOnNhd _ w (ha.trans_lt (EReal.coe_lt_coe_iff.mpr hw))

private theorem rationalPrimePart_sub :
    (primePart archivedGaussianRationalMangoldt : ℕ → ℂ) =
      (archivedGaussianRationalMangoldt : ℕ → ℂ) - (rationalTail : ℕ → ℂ) := by
  have h := primePart_add_tail_two archivedGaussianRationalMangoldt (fun n hn => by
    simp [archivedGaussianRationalMangoldt, vonMangoldt_eq_zero_iff.mpr hn])
  funext n
  apply eq_sub_of_add_eq
  exact congrArg (fun a : ArithmeticFunction ℂ => a n) h

private theorem higherPower_LSeries_eq {z : ℂ} (hz : 1 < z.re) :
    LSeries archivedGaussianVaughanHigherCoefficients z =
      LSeries archivedGaussianRationalMangoldt (2 * z) - LSeries rationalTail (2 * z) +
        LSeries archivedGaussianExceptionalMangoldt (2 * z) + LSeries gaussianTail z := by
  have hw : 1 < (2 * z).re := by simp [mul_re]; linarith
  have hw' : 1 / 2 < (2 * z).re := by linarith
  have hA := (rationalMangoldt_summable hw).sub (rationalTail_summable hw')
  have hE := exceptional_summable (2 * z)
  have hT : LSeriesSummable gaussianTail z := by
    apply primePowerTail_summable 3 _ (by norm_num : (0 : ℝ) ≤ 2) archivedGaussianMangoldt_norm_le
    · linarith
    · norm_num
      linarith
  have hSub : (archivedGaussianVaughanSquareCoefficients : ℕ → ℂ) =
      (archivedGaussianVaughanHigherCoefficients : ℕ → ℂ) - (gaussianTail : ℕ → ℂ) := by
    funext n
    apply eq_sub_of_add_eq
    exact (congrArg (fun a : ArithmeticFunction ℂ => a n) archivedGaussianVaughanHigher_eq_square_add_tail).symm
  have hSquare : LSeries archivedGaussianVaughanSquareCoefficients z =
      LSeries archivedGaussianVaughanHigherCoefficients z - LSeries gaussianTail z := by
    rw [hSub, LSeries_sub (archivedGaussianVaughanHigher_summable hz) hT]
  have hDilation := archivedGaussianVaughanSquare_LSeries z
  rw [rationalPrimePart_sub, LSeries_add hA hE,
    LSeries_sub (rationalMangoldt_summable hw) (rationalTail_summable hw')] at hDilation
  linear_combination hDilation + -hSquare

private def unfilteredThetaMellin (z : ℂ) : ℂ := archivedMellin (z / 7) / 7

def archivedGaussianVaughanHigherCorrection (z : ℂ) : ℂ :=
  -LSeries rationalTail (2 * z) + LSeries archivedGaussianExceptionalMangoldt (2 * z) +
    LSeries gaussianTail z

private theorem lseries_uniform_from_real {a : ℕ → ℂ} {σ : ℝ}
    (hs : LSeriesSummable a (σ : ℂ)) :
    ∃ C ≥ 0, ∀ z : ℂ, σ ≤ z.re → ‖LSeries a z‖ ≤ C := by
  refine ⟨∑' n, ‖LSeries.term a (σ : ℂ) n‖, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro z hz
  have h : ∀ n, ‖LSeries.term a z n‖ ≤ ‖LSeries.term a (σ : ℂ) n‖ :=
    fun _ => LSeries.norm_term_le_of_re_le_re _ (by simpa using hz) _
  have ht := hs.norm.of_nonneg_of_le (fun _ => norm_nonneg _) h
  exact (norm_tsum_le_tsum_norm ht).trans (ht.tsum_le_tsum h hs.norm)

/-- The corrections beyond the four Dirichlet logarithmic derivatives
have a uniform bound at all heights on and right of the contour. -/
theorem archivedGaussianVaughanHigherCorrection_uniform :
    ∃ C ≥ 0, ∀ z : ℂ, 3 / 8 ≤ z.re → ‖archivedGaussianVaughanHigherCorrection z‖ ≤ C := by
  obtain ⟨R, hR, hr⟩ := lseries_uniform_from_real
    (rationalTail_summable (w := ((3 / 4 : ℝ) : ℂ)) (by norm_num))
  obtain ⟨E, hE, he⟩ := lseries_uniform_from_real (exceptional_summable ((3 / 4 : ℝ) : ℂ))
  obtain ⟨G, hG, hg⟩ := archivedGaussianVaughanTail_uniform (σ := 3 / 8) (by norm_num)
  refine ⟨R + E + G, by positivity, fun z hz => ?_⟩
  have hw : 3 / 4 ≤ (2 * z).re := by simp [mul_re]; linarith
  unfold archivedGaussianVaughanHigherCorrection
  refine (norm_add_le _ _).trans (add_le_add ?_ (hg z hz))
  refine (norm_add_le _ _).trans (add_le_add ?_ (he (2 * z) hw))
  rw [norm_neg]
  exact hr (2 * z) hw

/-- The four filtered Dirichlet logarithmic derivatives and the two
absolutely convergent tails continue the actual weighted higher powers. -/
def archivedGaussianVaughanHigherMellin (z : ℂ) : ℂ :=
  unfilteredThetaMellin z *
      (archivedGaussianFilteredDirichletLog χ₁ z + archivedGaussianFilteredDirichletLog χ₂ z +
        archivedGaussianFilteredDirichletLog χ₃ z - archivedGaussianFilteredDirichletLog χ₄ z) +
    archivedGaussianVaughanMultiplier z * archivedGaussianVaughanHigherCorrection z

theorem archivedGaussianVaughanHigherMellin_analyticAt (hDir : DirichletLZerosOnLine)
    {z : ℂ} (hz : 1 / 3 < z.re) : AnalyticAt ℂ archivedGaussianVaughanHigherMellin z := by
  have hD (χ : DirichletCharacter ℂ archivedGaussianRationalLevel) :=
    archivedGaussianFilteredDirichletLog_analyticAt hDir χ (z := z) (by linarith)
  have h0 : AnalyticAt ℂ unfilteredThetaMellin z :=
    ((((archivedMellin_differentiable archivedTheta_reflection).comp
      (differentiable_id.div_const (7 : ℂ))).div_const 7)).analyticAt z
  have hw : 1 / 2 < (2 * z).re := by simp [mul_re]; linarith
  have hlin : AnalyticAt ℂ (fun w : ℂ => 2 * w) z := analyticAt_const.mul analyticAt_id
  have hT := (rationalTail_analyticAt hw).comp hlin
  have hE := (exceptional_entire.analyticAt (2 * z)).comp hlin
  have hG := archivedGaussianVaughanTail_analyticAt hz
  exact (h0.mul (((hD χ₁).add (hD χ₂)).add (hD χ₃) |>.sub (hD χ₄))).add
    ((archivedGaussianVaughanMultiplier_entire.analyticAt z).mul ((hT.neg.add hE).add hG))

theorem archivedGaussianVaughanHigherMellin_eq {z : ℂ} (hz : 1 < z.re) :
    archivedGaussianVaughanHigherMellin z =
      archivedGaussianVaughanMultiplier z * LSeries archivedGaussianVaughanHigherCoefficients z := by
  have hz' : 1 / 2 < z.re := by linarith
  have hw : 1 < (2 * z).re := by simp [mul_re]; linarith
  unfold archivedGaussianVaughanHigherMellin
  simp only [archivedGaussianFilteredDirichletLog_eq _ hz', higherPower_LSeries_eq hz,
    rationalMangoldt_LSeries hw, archivedGaussianVaughanMultiplier, unfilteredThetaMellin,
    archivedGaussianVaughanHigherCorrection]
  ring

/-- The completed prime transform continues to the intended 3/8 contour
under the rational Dirichlet critical-line input. -/
theorem archivedGaussianVaughanCompletedPrime_continues (hDir : DirichletLZerosOnLine) :
    (∀ z : ℂ, 1 / 3 < z.re → AnalyticAt ℂ
      (archivedGaussianVaughanPrimeContinuation archivedGaussianVaughanHigherMellin) z) ∧
    ∀ z : ℂ, 1 < z.re → HasMellin archivedGaussianVaughanCompletedPrimeKernel z
      (archivedGaussianVaughanPrimeContinuation archivedGaussianVaughanHigherMellin z) :=
  ⟨fun _ hz => archivedGaussianVaughanPrimeContinuation_analyticAt
      (archivedGaussianVaughanHigherMellin_analyticAt hDir hz),
    fun _ hz => archivedGaussianVaughanPrimeContinuation_hasMellin hz
      (archivedGaussianVaughanHigherMellin_eq hz)⟩

#print axioms archivedGaussianVaughanHigherCorrection_uniform
#print axioms archivedGaussianVaughanHigherMellin_analyticAt
#print axioms archivedGaussianVaughanHigherMellin_eq
#check archivedGaussianVaughanCompletedPrime_continues
#print axioms archivedGaussianVaughanCompletedPrime_continues

end
end AlpogeSuperZeta
