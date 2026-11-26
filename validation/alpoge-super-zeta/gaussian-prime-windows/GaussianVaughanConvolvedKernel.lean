import GaussianVaughanMellinSeries
import Mathlib.NumberTheory.LSeries.Linearity

/-! The Gaussian ideal kernel and the completed prime reading. Their exact
Mellin products separate the entire derivative from the higher prime powers. -/

namespace AlpogeSuperZeta

open Complex Set QuarticModel
open scoped Classical

noncomputable section

private theorem term_norm_eq {a : ArithmeticFunction ℂ} {n : ℕ} (hn : n ≠ 0) (s : ℝ) :
    ‖LSeries.term a (s : ℂ) n‖ = ‖a n‖ * (n : ℝ) ^ (-s) := by
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [LSeries.term_of_ne_zero hn, norm_div, ← Complex.ofReal_natCast,
    norm_cpow_eq_rpow_re_of_pos hn₀, ofReal_re, Real.rpow_neg hn₀.le, div_eq_mul_inv]

private theorem dilatedTerm_norm_le {a : ArithmeticFunction ℂ} {H : ℝ → ℂ}
    {s D v : ℝ} (hv : 0 < v) (hH : ∀ u > 0, ‖H u‖ ≤ D * u ^ (-s)) (n : ℕ) :
    ‖a n * H (n * v)‖ ≤ (D * v ^ (-s)) * ‖LSeries.term a (s : ℂ) n‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  calc
    _ ≤ ‖a n‖ * (D * ((n : ℝ) * v) ^ (-s)) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hH _ (mul_pos hn₀ hv)) (norm_nonneg _)
    _ = _ := by rw [Real.mul_rpow hn₀.le hv.le, term_norm_eq hn]; ring

theorem dirichletKernelSum_summable {a : ArithmeticFunction ℂ} {H : ℝ → ℂ}
    {s D v : ℝ} (hv : 0 < v) (hH : ∀ u > 0, ‖H u‖ ≤ D * u ^ (-s))
    (ha : LSeriesSummable a (s : ℂ)) :
    Summable (fun n : ℕ => ‖a n * H (n * v)‖) :=
  (ha.norm.mul_left (D * v ^ (-s))).of_nonneg_of_le (fun _ => norm_nonneg _)
    (dilatedTerm_norm_le hv hH)

theorem dirichletKernelSum_norm_le {a : ArithmeticFunction ℂ} {H : ℝ → ℂ}
    {s D v : ℝ} (hv : 0 < v) (hH : ∀ u > 0, ‖H u‖ ≤ D * u ^ (-s))
    (ha : LSeriesSummable a (s : ℂ)) :
    ‖dirichletKernelSum a H v‖ ≤ (D * ∑' n, ‖LSeries.term a (s : ℂ) n‖) * v ^ (-s) := by
  have hs := dirichletKernelSum_summable hv hH ha
  exact (norm_tsum_le_tsum_norm hs).trans
    ((hs.tsum_le_tsum (dilatedTerm_norm_le hv hH) (ha.norm.mul_left _)).trans_eq
      (by rw [tsum_mul_left]; ring))

/-- A single positive-scale power envelope justifies unfolding a Dirichlet
product inside a kernel sum. The two divisor addresses are retained. -/
theorem dirichletKernelSum_convolution {a b : ArithmeticFunction ℂ} {H : ℝ → ℂ}
    {v s D : ℝ} (hv : 0 < v) (hH : ∀ u > 0, ‖H u‖ ≤ D * u ^ (-s))
    (ha : LSeriesSummable a (s : ℂ)) (hb : LSeriesSummable b (s : ℂ)) :
    dirichletKernelSum (a * b) H v =
      ∑' m : ℕ, a m * dirichletKernelSum b H (m * v) := by
  let F (p : ℕ × ℕ) : ℂ := a p.1 * b p.2 * H ((p.1 : ℝ) * p.2 * v)
  let A (n : ℕ) := ‖LSeries.term a (s : ℂ) n‖
  let B (n : ℕ) := ‖LSeries.term b (s : ℂ) n‖
  have hprod : Summable (fun p : ℕ × ℕ => A p.1 * B p.2) :=
    ha.norm.mul_of_nonneg hb.norm (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hnorm : Summable (fun p => ‖F p‖) := by
    apply (hprod.mul_left (D * v ^ (-s))).of_nonneg_of_le (fun _ => norm_nonneg _)
    rintro ⟨m, n⟩
    by_cases hm : m = 0
    · subst m
      simp [F, A]
    by_cases hn : n = 0
    · subst n
      simp [F, B]
    have hm₀ : 0 < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
    have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hp : 0 < (m : ℝ) * n * v := mul_pos (mul_pos hm₀ hn₀) hv
    change ‖a m * b n * H ((m : ℝ) * n * v)‖ ≤ D * v ^ (-s) * (A m * B n)
    calc
      _ ≤ ‖a m * b n‖ * (D * ((m : ℝ) * n * v) ^ (-s)) := by
        rw [norm_mul (a m * b n)]
        exact mul_le_mul_of_nonneg_left (hH _ hp) (norm_nonneg _)
      _ = _ := by
        rw [norm_mul, Real.mul_rpow (mul_nonneg hm₀.le hn₀.le) hv.le,
          Real.mul_rpow hm₀.le hn₀.le]
        simp only [A, B, term_norm_eq hm, term_norm_eq hn]
        ring
  have hF : Summable F := hnorm.of_norm
  let index (p : ℕ × ℕ) := p.1 * p.2
  have hfiber (n : ℕ) :
      (∑' p : index ⁻¹' {n}, F p) = (a * b) n * H (n * v) := by
    by_cases hn : n = 0
    · subst n
      have hz (p : index ⁻¹' {0}) : F p = 0 := by
        have hp : p.val.1 * p.val.2 = 0 := p.property
        rcases Nat.mul_eq_zero.mp hp with hp | hp <;> simp [F, hp]
      simp only [hz, tsum_zero, ArithmeticFunction.map_zero, zero_mul]
    have he : index ⁻¹' {n} = ↑n.divisorsAntidiagonal := by
      ext p
      simp [index, hn]
    rw [he, Finset.tsum_subtype', ArithmeticFunction.mul_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := (Nat.mem_divisorsAntidiagonal.mp hp).1
    dsimp only [F]
    rw [← Nat.cast_mul, hp']
  have hIter :
      (∑' p : ℕ × ℕ, F p) = ∑' m : ℕ, ∑' n : ℕ, F (m, n) := by
    exact hF.tsum_prod' (fun _ => hF.comp_injective (fun _ _ h => congrArg Prod.snd h))
  calc
    dirichletKernelSum (a * b) H v = ∑' n : ℕ, ∑' p : index ⁻¹' {n}, F p := by
      simp only [hfiber, dirichletKernelSum]
    _ = ∑' p : ℕ × ℕ, F p := (hF.hasSum.tsum_fiberwise index).tsum_eq
    _ = _ := by
      rw [hIter]
      apply tsum_congr
      intro m
      unfold dirichletKernelSum
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      dsimp only [F]
      rw [show (m : ℝ) * n * v = (n : ℝ) * (m * v) by ring, mul_assoc]

def archivedGaussianVaughanPrimeCoefficients : ArithmeticFunction ℂ :=
  ⟨fun n => if n.Prime then archivedGaussianMangoldt n else 0, by simp⟩

def archivedGaussianVaughanHigherCoefficients : ArithmeticFunction ℂ :=
  archivedGaussianMangoldt - archivedGaussianVaughanPrimeCoefficients

theorem archivedGaussianVaughanPrime_summable {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable archivedGaussianVaughanPrimeCoefficients z := by
  apply (archivedGaussianMangoldt_summable hz).norm.of_norm_bounded
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  change ‖(if n.Prime then archivedGaussianMangoldt n else 0) / (n : ℂ) ^ z‖ ≤ _
  split_ifs
  · exact le_rfl
  · rw [zero_div, norm_zero]
    exact norm_nonneg _

theorem archivedGaussianVaughanHigher_summable {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable archivedGaussianVaughanHigherCoefficients z := by
  exact (archivedGaussianMangoldt_summable hz).sub (archivedGaussianVaughanPrime_summable hz)

theorem archivedGaussianVaughanHigher_supported {n : ℕ}
    (hn : archivedGaussianVaughanHigherCoefficients n ≠ 0) : IsPrimePow n ∧ ¬n.Prime := by
  change archivedGaussianMangoldt n -
    (if n.Prime then archivedGaussianMangoldt n else 0) ≠ 0 at hn
  by_cases hp : n.Prime
  · exact (hn (by rw [if_pos hp, sub_self])).elim
  refine ⟨?_, hp⟩
  by_contra hpow
  have hzero : archivedGaussianMangoldt n = 0 := by
    simp [archivedGaussianMangoldt, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpow]
  exact hn (by rw [if_neg hp, hzero, sub_zero])

private def complexVaughanKernel (v : ℝ) : ℂ := archivedGaussianVaughanKernel v

private theorem dirichletKernelSum_signedIdeal_eq (v : ℝ) :
    dirichletKernelSum signedIdealCoefficients complexVaughanKernel v =
      (archivedGaussianVaughanConvolvedKernel v : ℂ) := by
  unfold dirichletKernelSum archivedGaussianVaughanConvolvedKernel
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp only [complexVaughanKernel, signedIdealCoefficients_eq_archivedLatticeCoeff,
    ofReal_mul, intCast_re, ofReal_intCast]

/-- The same real kernel used by the complementary prime sum has Mellin
transform equal to the archived Gaussian factor times the two-scale weight. -/
theorem archivedGaussianVaughanConvolvedKernel_hasMellin {z : ℂ} (hz : 1 < z.re) :
    HasMellin (fun v => (archivedGaussianVaughanConvolvedKernel v : ℂ)) z
      (archivedGaussianVaughanMultiplier z * archivedGaussianFactor z) := by
  have h := dirichletKernelSum_hasMellin signedIdealCoefficients
    (archivedGaussianVaughanKernel_hasMellin (zero_lt_one.trans hz))
    ((archivedGaussianFactor_hasSum (by simpa using hz)).LSeriesSummable)
  rw [(archivedGaussianFactor_hasSum hz).LSeries_eq] at h
  exact (funext dirichletKernelSum_signedIdeal_eq) ▸ h

theorem archivedGaussianVaughanConvolvedKernel_powerBound {s : ℝ} (hs : 1 < s) :
    ∃ D ≥ 0, ∀ v > 0, |archivedGaussianVaughanConvolvedKernel v| ≤ D * v ^ (-s) := by
  obtain ⟨D, hD, hK⟩ := archivedGaussianVaughanKernel_powerBound (zero_lt_one.trans hs).le
  have hB := (archivedGaussianFactor_hasSum (w := (s : ℂ)) (by simpa using hs)).LSeriesSummable
  refine ⟨D * ∑' n, ‖LSeries.term signedIdealCoefficients (s : ℂ) n‖,
    mul_nonneg hD (tsum_nonneg fun _ => norm_nonneg _), fun v hv => ?_⟩
  rw [← Real.norm_eq_abs, ← Complex.norm_real, ← dirichletKernelSum_signedIdeal_eq]
  apply dirichletKernelSum_norm_le hv _ hB
  intro u hu
  simpa only [complexVaughanKernel, Complex.norm_real, Real.norm_eq_abs] using hK u hu

def archivedGaussianVaughanCompletedPrimeKernel (v : ℝ) : ℂ :=
  dirichletKernelSum (archivedGaussianVaughanPrimeCoefficients * signedIdealCoefficients)
    complexVaughanKernel v

theorem archivedGaussianVaughanCompletedPrimeKernel_eq {v : ℝ} (hv : 0 < v) :
    archivedGaussianVaughanCompletedPrimeKernel v =
      ∑' p : ℕ, archivedGaussianVaughanPrimeCoefficients p *
        (archivedGaussianVaughanConvolvedKernel (p * v) : ℂ) := by
  obtain ⟨D, _, hK⟩ := archivedGaussianVaughanKernel_powerBound (a := 2) (by norm_num)
  have hH : ∀ x > 0, ‖complexVaughanKernel x‖ ≤ D * x ^ (-(2 : ℝ)) := by
    intro x hx
    simpa only [complexVaughanKernel, Complex.norm_real, Real.norm_eq_abs] using hK x hx
  unfold archivedGaussianVaughanCompletedPrimeKernel
  rw [dirichletKernelSum_convolution hv hH
    (archivedGaussianVaughanPrime_summable (z := ((2 : ℝ) : ℂ)) (by norm_num))
    (archivedGaussianFactor_hasSum (w := ((2 : ℝ) : ℂ)) (by norm_num)).LSeriesSummable]
  simp only [dirichletKernelSum_signedIdeal_eq]

/-- The completed prime reading replaces the apparent logarithmic derivative
by the entire derivative. Its remaining factor is the higher-power series. -/
theorem archivedGaussianVaughanCompletedPrimeKernel_hasMellin {z : ℂ} (hz : 1 < z.re) :
    HasMellin archivedGaussianVaughanCompletedPrimeKernel z
      (archivedGaussianVaughanMultiplier z *
        (-deriv archivedGaussianFactor z - archivedGaussianFactor z *
          LSeries archivedGaussianVaughanHigherCoefficients z)) := by
  have hPrime := archivedGaussianVaughanPrime_summable hz
  have hG := archivedGaussianFactor_hasSum hz
  have h := dirichletKernelSum_hasMellin
    (archivedGaussianVaughanPrimeCoefficients * signedIdealCoefficients)
    (archivedGaussianVaughanKernel_hasMellin (zero_lt_one.trans hz))
    (ArithmeticFunction.LSeriesSummable_mul
      (archivedGaussianVaughanPrime_summable (by simpa using hz))
      (archivedGaussianFactor_hasSum (by simpa using hz)).LSeriesSummable)
  rw [ArithmeticFunction.LSeries_mul' hPrime hG.LSeriesSummable, hG.LSeries_eq] at h
  have he : LSeries archivedGaussianVaughanHigherCoefficients z =
      LSeries archivedGaussianMangoldt z - LSeries archivedGaussianVaughanPrimeCoefficients z := by
    exact LSeries_sub (archivedGaussianMangoldt_summable hz) hPrime
  have hValue : archivedGaussianVaughanMultiplier z *
        (LSeries archivedGaussianVaughanPrimeCoefficients z * archivedGaussianFactor z) =
      archivedGaussianVaughanMultiplier z * (-deriv archivedGaussianFactor z -
        archivedGaussianFactor z * LSeries archivedGaussianVaughanHigherCoefficients z) := by
    rw [he, archivedGaussianFactor_deriv_eq_mangoldt_mul hz, neg_neg]
    ring
  change HasMellin archivedGaussianVaughanCompletedPrimeKernel z
    (archivedGaussianVaughanMultiplier z *
      (LSeries archivedGaussianVaughanPrimeCoefficients z * archivedGaussianFactor z)) at h
  exact hValue ▸ h

/-- Supply a continuation of the filtered higher powers. The completed
prime reading inherits its analyticity, with no Gaussian denominator. -/
def archivedGaussianVaughanPrimeContinuation (U : ℂ → ℂ) (z : ℂ) : ℂ :=
  archivedGaussianVaughanMultiplier z * (-deriv archivedGaussianFactor z) -
    archivedGaussianFactor z * U z

theorem archivedGaussianVaughanPrimeContinuation_analyticAt {U : ℂ → ℂ} {z : ℂ}
    (hU : AnalyticAt ℂ U z) :
    AnalyticAt ℂ (archivedGaussianVaughanPrimeContinuation U) z := by
  have hG := archivedGaussianFactor_entire.analyticAt z
  exact ((archivedGaussianVaughanMultiplier_entire.analyticAt z).mul hG.deriv.neg).sub
    (hG.mul hU)

theorem archivedGaussianVaughanPrimeContinuation_hasMellin {U : ℂ → ℂ} {z : ℂ} (hz : 1 < z.re)
    (hU : U z = archivedGaussianVaughanMultiplier z *
      LSeries archivedGaussianVaughanHigherCoefficients z) :
    HasMellin archivedGaussianVaughanCompletedPrimeKernel z
      (archivedGaussianVaughanPrimeContinuation U z) := by
  have hValue : archivedGaussianVaughanMultiplier z *
      (-deriv archivedGaussianFactor z - archivedGaussianFactor z *
        LSeries archivedGaussianVaughanHigherCoefficients z) =
      archivedGaussianVaughanPrimeContinuation U z := by
    rw [archivedGaussianVaughanPrimeContinuation, hU]
    ring
  exact hValue ▸ archivedGaussianVaughanCompletedPrimeKernel_hasMellin hz

#print axioms dirichletKernelSum_convolution
#print axioms dirichletKernelSum_summable
#print axioms dirichletKernelSum_norm_le
#print axioms archivedGaussianVaughanPrime_summable
#print axioms archivedGaussianVaughanHigher_summable
#print axioms archivedGaussianVaughanHigher_supported
#print axioms archivedGaussianVaughanConvolvedKernel_hasMellin
#print axioms archivedGaussianVaughanConvolvedKernel_powerBound
#print axioms archivedGaussianVaughanCompletedPrimeKernel_eq
#print axioms archivedGaussianVaughanCompletedPrimeKernel_hasMellin
#print axioms archivedGaussianVaughanPrimeContinuation_analyticAt
#print axioms archivedGaussianVaughanPrimeContinuation_hasMellin

end
end AlpogeSuperZeta
