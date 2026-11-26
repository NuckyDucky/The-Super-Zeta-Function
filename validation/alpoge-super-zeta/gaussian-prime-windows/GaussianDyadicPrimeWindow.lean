import GaussianPrimeSquaredWindow

/-! The signed prime count in a single dyadic interval detects the quartic's Gaussian poles. -/

namespace AlpogeSuperZeta

open ArithmeticFunction ArtinPrimitiveRootsConjecture Complex FieldTarget Filter Finset MeasureTheory
  QuarticModel Set
open scoped Classical Topology

noncomputable section

private def dyadic (b : ℕ → ℝ) : ℝ → ℝ :=
  indexedCutoffSum .window (fun n => b (n + 1)) Nat.succ

private def fullWeight (n : ℕ) : ℝ :=
  -(vonMangoldt n * archivedGaussianPrimeWeight n)

/-- The full signed Mangoldt reading on the same dyadic interval. -/
def archivedGaussianDyadicMangoldtWindow : ℝ → ℝ := dyadic fullWeight

/-- The central-class excess. A prime is included exactly when x / 2 ≤ p < x. -/
def archivedGaussianDyadicPrimeWindow : ℝ → ℝ :=
  dyadic archivedGaussianSignedPrimeWeight

private theorem fullWeight_abs_summable {w : ℂ} (hw : 1 < w.re) :
    Summable (fun n : ℕ => |fullWeight (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ w.re) := by
  have hs := (archivedGaussianMangoldt_summable hw).norm
  refine ((summable_nat_add_iff 1).mpr hs).congr fun n => ?_
  simp only [LSeries.norm_term_eq, Nat.add_one_ne_zero, if_false, archivedGaussianMangoldt,
    ArithmeticFunction.coe_mk, norm_mul, norm_real, Real.norm_eq_abs, fullWeight, abs_neg,
    abs_mul, mul_comm (|archivedGaussianPrimeWeight (n + 1)|)]

private theorem dyadicDirichletSum_eq {w : ℂ} (hw : 1 < w.re) :
    indexedDirichletSum (fun n => fullWeight (n + 1)) Nat.succ w =
      -LSeries archivedGaussianMangoldt w := by
  unfold indexedDirichletSum LSeries
  rw [(archivedGaussianMangoldt_summable hw).tsum_eq_zero_add, LSeries.term_zero, zero_add,
    ← tsum_neg]
  apply tsum_congr
  intro n
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), cpow_neg]
  simp only [fullWeight, ofReal_neg, ofReal_mul, archivedGaussianMangoldt,
    ArithmeticFunction.coe_mk, div_eq_mul_inv, Nat.succ_eq_add_one]
  ring

theorem archivedGaussianDyadicMangoldtWindow_mellin {w : ℂ} (hw : 1 < w.re) :
    ∫ x in Ioi (1 : ℝ), (archivedGaussianDyadicMangoldtWindow x : ℂ) * (x : ℂ) ^ (-w - 1) =
      (1 - (2 : ℂ) ^ (-w)) * logDeriv archivedGaussianFactor w / w := by
  have h := (indexedCutoffSum_mellin .window (fun n => fullWeight (n + 1)) Nat.succ
    Nat.succ_pos hw (fullWeight_abs_summable hw)).2
  rw [dyadicDirichletSum_eq hw, archivedGaussianMangoldt_eq_neg_logDeriv hw, neg_neg] at h
  simpa [archivedGaussianDyadicMangoldtWindow, dyadic, IndexedCutoff.mellinNumerator,
    IndexedCutoff.mellinDenominator, mul_comm] using h

private theorem dyadic_full_growth :
    ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), |dyadic fullWeight x| ≤ C * x ^ (2 : ℝ) := by
  have h₂ : 1 < (2 : ℂ).re := by norm_num
  let C := ∑' n : ℕ, |fullWeight (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ (2 : ℝ)
  refine ⟨C, tsum_nonneg (fun _ => by positivity), fun x hx => ?_⟩
  have h := indexedCutoffSum_abs_le .window (fun n => fullWeight (n + 1)) Nat.succ
    Nat.succ_pos (by norm_num : 0 ≤ (2 : ℂ).re) hx (fullWeight_abs_summable h₂)
  simpa [dyadic, C, IndexedCutoff.maxWeight, mul_comm] using h

private theorem fullWeight_sub_prime (n : ℕ) :
    fullWeight n - archivedGaussianSignedPrimeWeight n = -gaussianHigherPrimeCoefficient n := by
  by_cases hp : n.Prime
  · simp [fullWeight, archivedGaussianSignedPrimeWeight, gaussianHigherPrimeCoefficient, hp]
  · simp [fullWeight, archivedGaussianSignedPrimeWeight, gaussianHigherPrimeCoefficient, hp]

theorem archivedGaussianDyadicPrimeWindow_error (θ : ℝ) (hθ : 1 / 2 < θ) (_ : θ < 1) :
    ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ),
      |archivedGaussianDyadicMangoldtWindow x - archivedGaussianDyadicPrimeWindow x| ≤ C * x ^ θ := by
  have hθ₀ : 0 ≤ θ := by linarith
  have h₂ : 1 < (2 : ℂ).re := by norm_num
  have hH := (summable_nat_add_iff 1).mpr (gaussianHigherPrime_summable hθ)
  let C := ∑' n : ℕ, |gaussianHigherPrimeCoefficient (n + 1)| / ((n + 1 : ℕ) : ℝ) ^ θ
  refine ⟨C, tsum_nonneg (fun _ => by positivity), fun x hx => ?_⟩
  let W (n : ℕ) := IndexedCutoff.window.weight x (n + 1)
  have hF := indexedCutoffSum_summable_at .window (fun n => fullWeight (n + 1)) Nat.succ
    Nat.succ_pos (by norm_num : 0 ≤ (2 : ℂ).re) hx (fullWeight_abs_summable h₂)
  have hHS := indexedCutoffSum_summable_at .window (fun n => gaussianHigherPrimeCoefficient (n + 1))
    Nat.succ Nat.succ_pos hθ₀ hx hH
  have hP : Summable (fun n : ℕ => archivedGaussianSignedPrimeWeight (n + 1) * W n) := by
    refine (hF.add hHS).congr fun n => ?_
    change fullWeight (n + 1) * W n + gaussianHigherPrimeCoefficient (n + 1) * W n = _
    rw [← add_mul, show fullWeight (n + 1) + gaussianHigherPrimeCoefficient (n + 1) =
      archivedGaussianSignedPrimeWeight (n + 1) by linarith [fullWeight_sub_prime (n + 1)]]
  have he : archivedGaussianDyadicMangoldtWindow x - archivedGaussianDyadicPrimeWindow x =
      -dyadic gaussianHigherPrimeCoefficient x := by
    unfold archivedGaussianDyadicMangoldtWindow archivedGaussianDyadicPrimeWindow dyadic indexedCutoffSum
    rw [← hF.tsum_sub hP, ← tsum_neg]
    apply tsum_congr
    intro n
    rw [← sub_mul, fullWeight_sub_prime, neg_mul]
  rw [he, abs_neg]
  have h := indexedCutoffSum_abs_le .window (fun n => gaussianHigherPrimeCoefficient (n + 1))
    Nat.succ Nat.succ_pos hθ₀ hx hH
  simpa [dyadic, C, IndexedCutoff.maxWeight, mul_comm] using h

theorem archivedGaussianDyadicPrimeWindow_eq_sum {x : ℝ} (hx : 0 ≤ x) :
    archivedGaussianDyadicPrimeWindow x =
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ x / 2 ≤ (p : ℝ) ∧ (p : ℝ) < x),
        -Real.log (p : ℝ) * archivedGaussianPrimeWeight p := by
  unfold archivedGaussianDyadicPrimeWindow dyadic indexedCutoffSum
  rw [tsum_eq_sum (s := range ⌊x⌋₊)]
  · have he (n : ℕ) : archivedGaussianSignedPrimeWeight (n + 1) *
        IndexedCutoff.window.weight x n.succ =
        if (n + 1).Prime ∧ x / 2 ≤ ((n + 1 : ℕ) : ℝ) ∧ ((n + 1 : ℕ) : ℝ) < x then
          -Real.log ((n + 1 : ℕ) : ℝ) * archivedGaussianPrimeWeight (n + 1) else 0 := by
      have h (p : ℕ) : x ≤ 2 * (p : ℝ) ↔ x / 2 ≤ (p : ℝ) := by
        rw [div_le_iff₀ (by norm_num : 0 < (2 : ℝ)), mul_comm (p : ℝ)]
      by_cases hp : (n + 1).Prime
      · rw [archivedGaussianSignedPrimeWeight, vonMangoldt_apply_prime hp, if_pos hp]
        simp only [Nat.succ_eq_add_one, IndexedCutoff.weight, h, hp, true_and,
          mul_ite, mul_one, mul_zero, neg_mul, and_comm]
      · simp [archivedGaussianSignedPrimeWeight, hp]
    simp_rw [he]
    rw [sum_filter, sum_range_succ']
    simp
  · intro n hn
    rw [IndexedCutoff.window.weight_zero_of_le (Nat.succ_pos n), mul_zero]
    exact ((Nat.floor_lt hx).mp (Nat.lt_succ_of_le (Nat.not_lt.mp (fun h => hn (mem_range.mpr h))))).le

private def windowFactor (w : ℂ) : ℂ := 1 - (2 : ℂ) ^ (-w)

private def dyadicContinuation (Φ : ℂ → ℂ) (w : ℂ) : ℂ :=
  (windowFactor w * (1 - w)) * Φ w + windowFactor w * logDeriv archivedGaussianFactor 1

private theorem dyadicContinuation_analytic {Φ : ℂ → ℂ} {w : ℂ} (hΦ : AnalyticAt ℂ Φ w) :
    AnalyticAt ℂ (dyadicContinuation Φ) w := by
  have hA : AnalyticAt ℂ windowFactor w := halfWindowFactor_analytic w
  have hM : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  exact ((hA.mul hM).mul hΦ).add (hA.mul analyticAt_const)

private theorem dyadicResidue_pos {ρ : ℂ} (hρ : 0 < ρ.re) (hi : ρ.im = 0) {m : ℕ}
    (hm : 0 < m) : 0 < (((m : ℂ) * windowFactor ρ) / ρ).re ∧
      (((m : ℂ) * windowFactor ρ) / ρ).im = 0 := by
  have hr : (ρ.re : ℂ) = ρ := Complex.ext (by simp) (by simpa using hi.symm)
  have hp : (2 : ℝ) ^ (-ρ.re) < 1 := by
    simpa only [Real.rpow_zero] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (neg_lt_zero.mpr hρ)
  let r := (m : ℝ) * (1 - (2 : ℝ) ^ (-ρ.re)) / ρ.re
  have hR : (r : ℂ) = (m : ℂ) * windowFactor ρ / ρ := by
    simp only [r, windowFactor, ofReal_div, ofReal_mul, ofReal_natCast, ofReal_sub, ofReal_one,
      ofReal_cpow (by norm_num : 0 ≤ (2 : ℝ)), ofReal_ofNat, ofReal_neg, hr]
  rw [← hR, ofReal_re, ofReal_im]
  exact ⟨div_pos (mul_pos (Nat.cast_pos.mpr hm) (sub_pos.mpr hp)) hρ, rfl⟩

private theorem dyadicContinuation_pole {Φ b : ℂ → ℂ} {ρ : ℂ} (hρ : ρ ∈ gaussianPoles)
    {m : ℕ} (hm : m ≠ 0) (hb : AnalyticAt ℂ b ρ)
    (he : ∀ᶠ w in 𝓝[≠] ρ,
      Φ w = (m : ℂ) * (-1 / (ρ * (ρ - 1))) / (w - ρ) + b w) :
    ∃ d : ℂ, d ≠ 0 ∧ (ρ.im = 0 → 0 < d.re ∧ d.im = 0) ∧
      ∃ b' : ℂ → ℂ, AnalyticAt ℂ b' ρ ∧
        ∀ᶠ w in 𝓝[≠] ρ, dyadicContinuation Φ w = d / (w - ρ) + b' w := by
  let M (w : ℂ) := windowFactor w * (1 - w)
  let c : ℂ := (m : ℂ) * (-1 / (ρ * (ρ - 1)))
  have h0 : ρ ≠ 0 := fun h => by have hp := hρ.1; simp [h] at hp
  have h1 : ρ ≠ 1 := fun h => quartic_gaussian_one_ne_zero (h ▸ hρ.2)
  have hM : AnalyticAt ℂ M ρ := (halfWindowFactor_analytic ρ).mul (analyticAt_const.sub analyticAt_id)
  have hd : M ρ * c = (m : ℂ) * windowFactor ρ / ρ := by
    dsimp only [M, c]
    field_simp [h0, sub_ne_zero.mpr h1]
    ring
  have hd₀ : M ρ * c ≠ 0 := by
    rw [hd]
    exact div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hm) (halfWindowFactor_ne_zero hρ.1)) h0
  refine ⟨M ρ * c, hd₀, fun hi => hd ▸ dyadicResidue_pos hρ.1 hi (Nat.pos_of_ne_zero hm),
    fun w => dslope M ρ w * c + M w * b w + windowFactor w * logDeriv archivedGaussianFactor 1,
    (((Deduction.poleData_dslope hM).mul analyticAt_const).add (hM.mul hb)).add
      ((halfWindowFactor_analytic ρ).mul analyticAt_const), ?_⟩
  filter_upwards [he, self_mem_nhdsWithin] with w hw hne
  change w ≠ ρ at hne
  change M w * Φ w + _ = _
  rw [hw, dslope_of_ne _ hne, slope_def_field]
  change M w * (c / (w - ρ) + b w) + _ = _
  ring

private theorem quartic_rh_of_dyadic_full_windows (hD : DirichletLZerosOnLine)
    (hWindow : GaussianCutoffWindowBound archivedGaussianDyadicMangoldtWindow) :
    DedekindZetaRH QuarticModel.K := by
  obtain ⟨Φ, hΦ, ha, hp, _⟩ := gaussian_regularized_transform
  refine quartic_rh_of_gaussian_mellin_windows hD (Φ := dyadicContinuation Φ)
    (A := archivedGaussianDyadicMangoldtWindow)
    (indexedCutoffSum_measurable .window _ _) dyadic_full_growth ?_ ?_ ?_ hWindow
  · intro w hw hn
    exact dyadicContinuation_analytic (ha w (fun h => by norm_num [h] at hw) hn)
  · intro ρ hρ _
    have h0 : ρ ≠ 0 := fun h => by have hpos := hρ.1; simp [h] at hpos
    obtain ⟨m, hm, b, hb, he⟩ := hp ρ h0
    exact dyadicContinuation_pole hρ (fun h => hm.mp h hρ.2) hb he
  · intro w hw
    have h0 : w ≠ 0 := fun h => by norm_num [h] at hw
    have h1 : w ≠ 1 := fun h => by norm_num [h] at hw
    rw [archivedGaussianDyadicMangoldtWindow_mellin (by linarith), dyadicContinuation, hΦ w h1,
      gaussianPoleFormula]
    change windowFactor w * logDeriv archivedGaussianFactor w / w = _
    field_simp [h0, sub_ne_zero.mpr h1]
    ring

/-- A cofinal estimate for the prime-only central-class excess implies Dedekind RH
for the archived quartic. The real-pole residue is positive with this sign. -/
theorem quartic_rh_of_archived_gaussian_dyadic_prime_windows (hD : DirichletLZerosOnLine)
    (hWindow : GaussianCutoffWindowBound archivedGaussianDyadicPrimeWindow) :
    DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_dyadic_full_windows hD
    ((gaussianCutoffWindowBound_iff_of_error (X₀ := 1)
      archivedGaussianDyadicPrimeWindow_error).mpr hWindow)

#print axioms archivedGaussianDyadicMangoldtWindow_mellin
#print axioms dyadicContinuation_pole
#print axioms archivedGaussianDyadicPrimeWindow_eq_sum
#print axioms archivedGaussianDyadicPrimeWindow_error
#check quartic_rh_of_archived_gaussian_dyadic_prime_windows
#print axioms quartic_rh_of_archived_gaussian_dyadic_prime_windows

end

end AlpogeSuperZeta
