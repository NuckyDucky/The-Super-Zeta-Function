import GaussianVaughanUpperError

/-! The two endpoints of the original theta kernel localize the full
prime reading. The original signed window and this finite prime band
have the same one-sided late-window condition. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Filter Finset QuarticModel ArtinPrimitiveRootsConjecture
open scoped Classical

noncomputable section

private abbrev logRadius (X : ℝ) : ℝ := (Real.log X) ^ (1 / 6 : ℝ)

/-- The rational primes from the lower to the upper logarithmic edge. -/
def archivedGaussianVaughanBandPrimes (X : ℝ) : Finset ℕ :=
  (Icc (Nat.ceil (X / logRadius X)) (Nat.floor (X * logRadius X))).filter Nat.Prime

private def primeTerm (X : ℝ) (p : ℕ) : ℝ :=
  (archivedGaussianVaughanPrimeCoefficients p).re * archivedGaussianVaughanKernel (p / X)

/-- The original signed prime weights, at the original theta kernel, on
the logarithmic band about the scale X. -/
def archivedGaussianVaughanPrimeBand (X : ℝ) : ℝ :=
  if 1 < X then ∑ p ∈ archivedGaussianVaughanBandPrimes X, primeTerm X p else 0

theorem mem_archivedGaussianVaughanBandPrimes {X : ℝ} (hX : 1 < X) (p : ℕ) :
    p ∈ archivedGaussianVaughanBandPrimes X ↔
      (X / (Real.log X) ^ (1 / 6 : ℝ) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ X * (Real.log X) ^ (1 / 6 : ℝ)) ∧ p.Prime := by
  have hL : 0 ≤ logRadius X := Real.rpow_nonneg (Real.log_pos hX).le _
  have hXL : 0 ≤ X * logRadius X := mul_nonneg (zero_le_one.trans hX.le) hL
  simp only [archivedGaussianVaughanBandPrimes, mem_filter, mem_Icc, Nat.ceil_le,
    Nat.le_floor_iff hXL]

theorem archivedGaussianVaughanPrimeBand_eq_sum {X : ℝ} (hX : 1 < X) :
    archivedGaussianVaughanPrimeBand X =
      ∑ p ∈ archivedGaussianVaughanBandPrimes X, archivedGaussianPrimeWeight p *
        (Real.log (p : ℝ) * archivedGaussianVaughanKernel (p / X)) := by
  rw [archivedGaussianVaughanPrimeBand, if_pos hX]
  refine sum_congr rfl fun p hp => ?_
  have hprime := ((mem_archivedGaussianVaughanBandPrimes hX p).mp hp).2
  simp only [primeTerm, archivedGaussianVaughanPrimeCoefficients, coe_mk, if_pos hprime,
    archivedGaussianMangoldt, vonMangoldt_apply_prime hprime, ← Complex.ofReal_mul, ofReal_re]
  ring

private theorem gaussianTheta_term_summable {a : ArithmeticFunction ℂ} {X : ℝ}
    (hx : 0 < X) (ha : LSeriesSummable a (2 : ℂ)) :
    Summable (fun p : ℕ => a p * (archivedGaussianVaughanKernel (p / X) : ℂ)) := by
  obtain ⟨D, _, hD⟩ := archivedGaussianVaughanKernel_powerBound (a := 2) (by norm_num)
  have hK (v : ℝ) (hv : 0 < v) :
      ‖(archivedGaussianVaughanKernel v : ℂ)‖ ≤ D * v ^ (-(2 : ℝ)) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hD v hv
  have hs := dirichletKernelSum_summable (a := a)
    (H := fun u => (archivedGaussianVaughanKernel u : ℂ))
    (s := 2) (v := X⁻¹) (inv_pos.mpr hx) hK ha
  simpa only [← div_eq_mul_inv] using hs.of_norm

private theorem primeTerm_summable {X : ℝ} (hx : 0 < X) : Summable (primeTerm X) := by
  have h := gaussianTheta_term_summable hx
    (archivedGaussianVaughanPrime_summable (z := (2 : ℂ)) (by norm_num))
  change Summable (fun p => (archivedGaussianVaughanPrimeCoefficients p).re *
    archivedGaussianVaughanKernel (p / X))
  simpa only [Complex.reCLM_apply, mul_re, ofReal_re, ofReal_im, mul_zero,
    sub_zero] using Complex.reCLM.summable h

private theorem archivedGaussianVaughanSum_eq_primes_add_higher {X : ℝ} (hx : 0 < X) :
    archivedGaussianVaughanSum X =
      (∑' p : ℕ, primeTerm X p) + (archivedGaussianVaughanHigherKernel X⁻¹).re := by
  let a := archivedGaussianVaughanHigherCoefficients
  let f (n : ℕ) : ℂ := a n * (archivedGaussianVaughanKernel (n / X) : ℂ)
  have hf : Summable f := gaussianTheta_term_summable hx
    (archivedGaussianVaughanHigher_summable (z := (2 : ℂ)) (by norm_num))
  have hfr : Summable (fun n => (f n).re) := Complex.reCLM.summable hf
  have hre : (archivedGaussianVaughanHigherKernel X⁻¹).re = ∑' n, (f n).re := by
    simp only [archivedGaussianVaughanHigherKernel, dirichletKernelSum, ← div_eq_mul_inv]
    exact Complex.re_tsum hf
  rw [archivedGaussianVaughanSum, if_pos hx, hre, ← (primeTerm_summable hx).tsum_add hfr]
  apply tsum_congr
  intro n
  have hsub : a n = archivedGaussianMangoldt n - archivedGaussianVaughanPrimeCoefficients n := rfl
  simp only [primeTerm, f, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, a,
    archivedGaussianVaughanHigherCoefficients]
  rw [show (archivedGaussianMangoldt - archivedGaussianVaughanPrimeCoefficients : ArithmeticFunction ℂ) n =
    archivedGaussianMangoldt n - archivedGaussianVaughanPrimeCoefficients n from hsub, sub_re]
  ring

private theorem gaussianKernel_logBand_tail :
    ∃ D ≥ 0, ∀ᶠ X : ℝ in atTop,
      ∀ v > (0 : ℝ), (v < (logRadius X)⁻¹ ∨ logRadius X < v) →
        |archivedGaussianVaughanKernel v| ≤ D / (X ^ (3 : ℕ) * v ^ (2 : ℕ)) := by
  obtain ⟨A, hA, a, ha, hSmall⟩ := archivedGaussianVaughanKernel_small_exp
  obtain ⟨B, hB, b, hb, T, hT, hLarge⟩ := archivedGaussianVaughanKernel_large_exp
  obtain ⟨E, hE, hPow⟩ := archivedGaussianVaughanKernel_powerBound (a := 4) (by norm_num)
  let M := A + B
  let D := M + E + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hL := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop T)
  have hThreshold := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 6)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop a⁻¹)
  have hExpA := gaussian_exp_log_power_eventually_inverse (a := a) (b := 7 / 6) ha (by norm_num) 6
  have hExpB := gaussian_exp_log_power_eventually_inverse (a := b) (b := 7 / 6) hb (by norm_num) 6
  filter_upwards [eventually_gt_atTop (1 : ℝ), hLog, hL, hThreshold, hExpA, hExpB]
    with X hX hLog hL hThreshold hExpA hExpB v hv hvBand
  have hx := zero_lt_one.trans hX
  let L := logRadius X
  have hL₀ : 0 < L := Real.rpow_pos_of_pos (Real.log_pos hX) _
  have hPower : L ^ (7 : ℕ) = (Real.log X) ^ (7 / 6 : ℝ) := by
    dsimp only [L, logRadius]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hLog)]
    norm_num
  have hBare : |archivedGaussianVaughanKernel v| ≤ M / X ^ (6 : ℕ) := by
    rcases hvBand with hlt | hgt
    · have hInv : v ^ (7 : ℕ) ≤ ((Real.log X) ^ (7 / 6 : ℝ))⁻¹ := by
        rw [← hPower, ← inv_pow]
        exact pow_le_pow_left₀ hv.le hlt.le _
      change a⁻¹ ≤ (Real.log X) ^ (7 / 6 : ℝ) at hThreshold
      have hCut : v ^ (7 : ℕ) ≤ a := hInv.trans (by
        simpa only [inv_inv] using (inv_anti₀ (inv_pos.mpr ha) hThreshold))
      have hInverse : (Real.log X) ^ (7 / 6 : ℝ) ≤ (v ^ (7 : ℕ))⁻¹ := by
        simpa only [inv_inv] using (inv_anti₀ (pow_pos hv 7) hInv)
      have hRatio : a * (Real.log X) ^ (7 / 6 : ℝ) ≤ a / v ^ (7 : ℕ) := by
        simpa only [div_eq_mul_inv a _] using mul_le_mul_of_nonneg_left hInverse ha.le
      have hExp := (Real.exp_le_exp.mpr (neg_le_neg hRatio)).trans hExpA
      calc
        _ ≤ A * Real.exp (-(a / v ^ (7 : ℕ))) := hSmall v hv hCut
        _ ≤ M * (X ^ (6 : ℕ))⁻¹ :=
          mul_le_mul (by dsimp [M]; linarith) hExp (Real.exp_pos _).le hM
        _ = _ := (div_eq_mul_inv _ _).symm
    · have hLargeV : T ≤ v := hL.trans hgt.le
      have hRatio : b * (Real.log X) ^ (7 / 6 : ℝ) ≤ b * v ^ (7 : ℕ) := by
        rw [← hPower]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL₀.le hgt.le _) hb.le
      have hExp := (Real.exp_le_exp.mpr (neg_le_neg hRatio)).trans hExpB
      calc
        _ ≤ B * Real.exp (-(b * v ^ (7 : ℕ))) := hLarge v hLargeV
        _ ≤ M * (X ^ (6 : ℕ))⁻¹ :=
          mul_le_mul (by dsimp [M]; linarith) hExp (Real.exp_pos _).le hM
        _ = _ := (div_eq_mul_inv _ _).symm
  have hWeighted : |archivedGaussianVaughanKernel v| ≤ E / v ^ (4 : ℕ) := by
    have h := hPow v hv
    rw [Real.rpow_neg hv.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
    simpa only [div_eq_mul_inv] using h
  have hConst : M * E ≤ D ^ (2 : ℕ) := by
    dsimp [D]
    nlinarith [sq_nonneg M, sq_nonneg E, mul_nonneg hM hE]
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  calc
    _ = |archivedGaussianVaughanKernel v| * |archivedGaussianVaughanKernel v| := sq _
    _ ≤ (M / X ^ (6 : ℕ)) * (E / v ^ (4 : ℕ)) :=
      mul_le_mul hBare hWeighted (abs_nonneg _) (by positivity)
    _ = (M * E) / ((X ^ (3 : ℕ) * v ^ (2 : ℕ)) ^ (2 : ℕ)) := by
      rw [div_mul_div_comm, mul_pow, ← pow_mul, ← pow_mul]
    _ ≤ _ := by
      rw [div_pow]
      exact div_le_div_of_nonneg_right hConst (by positivity)

private theorem primeTerm_bound_at_two {X : ℝ} (hx : 0 < X) {D : ℝ}
    {p : ℕ} (hp : p ≠ 0)
    (hK : |archivedGaussianVaughanKernel (p / X)| ≤
       D / (X ^ (3 : ℕ) * ((p : ℝ) / X) ^ (2 : ℕ))) :
    |primeTerm X p| ≤ (D / X) * ‖LSeries.term archivedGaussianVaughanPrimeCoefficients (2 : ℂ) p‖ := by
  have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
  have hN : ‖LSeries.term archivedGaussianVaughanPrimeCoefficients (2 : ℂ) p‖ =
      ‖archivedGaussianVaughanPrimeCoefficients p‖ / (p : ℝ) ^ (2 : ℕ) := by
    rw [LSeries.term_of_ne_zero hp, norm_div, ← Complex.ofReal_natCast,
      Complex.norm_cpow_eq_rpow_re_of_pos hp₀]
    norm_num [Real.rpow_two]
  rw [primeTerm, abs_mul, hN]
  calc
    _ ≤ ‖archivedGaussianVaughanPrimeCoefficients p‖ *
        (D / (X ^ (3 : ℕ) * ((p : ℝ) / X) ^ (2 : ℕ))) :=
      mul_le_mul (abs_re_le_norm _) hK (abs_nonneg _) (norm_nonneg _)
    _ = _ := by field_simp [hx.ne', hp₀.ne']

set_option maxHeartbeats 1000000 in
private theorem primeBand_error :
    ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop,
      |(∑' p : ℕ, primeTerm X p) - archivedGaussianVaughanPrimeBand X| ≤ C / X := by
  obtain ⟨D, hD, hTail⟩ := gaussianKernel_logBand_tail
  let b (p : ℕ) := ‖LSeries.term archivedGaussianVaughanPrimeCoefficients (2 : ℂ) p‖
  have hb : Summable b := (archivedGaussianVaughanPrime_summable (by norm_num)).norm
  have hB : 0 ≤ ∑' p, b p := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨D * ∑' p, b p, mul_nonneg hD hB, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), hTail] with X hX hTail
  have hx := zero_lt_one.trans hX
  let S := archivedGaussianVaughanBandPrimes X
  let f := ((S : Set ℕ)ᶜ).indicator (primeTerm X)
  have hSplit := (primeTerm_summable hx).sum_add_tsum_compl (s := S)
  rw [_root_.tsum_subtype] at hSplit
  have hDiff : (∑' p : ℕ, primeTerm X p) - archivedGaussianVaughanPrimeBand X = ∑' p, f p := by
    rw [archivedGaussianVaughanPrimeBand, if_pos hX]
    change (∑' p : ℕ, primeTerm X p) - (∑ p ∈ S, primeTerm X p) = ∑' p, f p
    change (∑ p ∈ S, primeTerm X p) + (∑' p, f p) = ∑' p : ℕ, primeTerm X p at hSplit
    linarith
  let M := D / X
  have hM : 0 ≤ M := div_nonneg hD hx.le
  have hTerm (p : ℕ) : ‖f p‖ ≤ M * b p := by
    by_cases hmem : p ∈ S
    · have hp : p ∉ (S : Set ℕ)ᶜ := by simpa using hmem
      simp only [f, Set.indicator_of_notMem hp, norm_zero]
      exact mul_nonneg hM (norm_nonneg _)
    have hp : p ∈ (S : Set ℕ)ᶜ := by simpa using hmem
    rw [show f p = primeTerm X p from Set.indicator_of_mem hp _, Real.norm_eq_abs]
    by_cases hpp : p.Prime
    · have hL : 0 < logRadius X := Real.rpow_pos_of_pos (Real.log_pos hX) _
      have hps : ¬ ((X / logRadius X ≤ (p : ℝ)) ∧ (p : ℝ) ≤ X * logRadius X) :=
        fun h => hmem ((mem_archivedGaussianVaughanBandPrimes hX p).mpr ⟨h, hpp⟩)
      have hArgument : (p : ℝ) / X < (logRadius X)⁻¹ ∨ logRadius X < (p : ℝ) / X := by
        rcases not_and_or.mp hps with hl | hr
        · left
          apply (div_lt_iff₀ hx).mpr
          simpa only [div_eq_mul_inv, mul_comm] using (lt_of_not_ge hl)
        · right
          apply (lt_div_iff₀ hx).mpr
          simpa only [mul_comm] using (lt_of_not_ge hr)
      have hPos : 0 < (p : ℝ) / X := div_pos (Nat.cast_pos.mpr hpp.pos) hx
      exact primeTerm_bound_at_two hx hpp.ne_zero (hTail _ hPos hArgument)
    · rw [show primeTerm X p = 0 by simp [primeTerm, archivedGaussianVaughanPrimeCoefficients, hpp],
        abs_zero]
      exact mul_nonneg hM (norm_nonneg _)
  have hf : Summable (fun p => ‖f p‖) :=
    (hb.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) hTerm
  rw [hDiff, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' p, ‖f p‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' p, M * b p := hf.tsum_le_tsum hTerm (hb.mul_left M)
    _ = _ := by rw [tsum_mul_left]; dsimp only [M]; ring

theorem archivedGaussianVaughanPrimeBand_approx (hDir : DirichletLZerosOnLine) :
    ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop,
      |archivedGaussianVaughanSum X - archivedGaussianVaughanPrimeBand X| ≤ C * X ^ (3 / 8 : ℝ) := by
  obtain ⟨A, hA, hHigher⟩ := archivedGaussianVaughanHigherKernel_left_powerBound hDir
  obtain ⟨B, hB, hBand⟩ := primeBand_error
  refine ⟨A + B, by positivity, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), hBand] with X hX hBand
  have hx := zero_lt_one.trans hX
  have hH := hHigher X⁻¹ (inv_pos.mpr hx)
  rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv] at hH
  have hE : 1 ≤ X ^ (3 / 8 : ℝ) := Real.one_le_rpow hX.le (by norm_num)
  rw [archivedGaussianVaughanSum_eq_primes_add_higher hx,
    add_sub_right_comm]
  calc
    _ ≤ |(∑' p : ℕ, primeTerm X p) - archivedGaussianVaughanPrimeBand X| +
        |(archivedGaussianVaughanHigherKernel X⁻¹).re| := abs_add_le _ _
    _ ≤ B * X ^ (3 / 8 : ℝ) + A * X ^ (3 / 8 : ℝ) :=
      add_le_add (hBand.trans ((div_le_self hB hX.le).trans
        (le_mul_of_one_le_right hB hE))) ((abs_re_le_norm _).trans hH)
    _ = _ := by ring

/-- The cofactor-free prime band gives exactly the original signed-window
premise, with the same exponents and window widths. -/
theorem archivedGaussianVaughanPrimeBand_window_iff (hDir : DirichletLZerosOnLine)
    (W : ℝ → ℝ) (hW : ∀ u ≥ 0, |W u| ≤ 1)
    (hUnit : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → W u = 1) (hSupport : ∀ u ≥ 2, W u = 0) :
    GaussianCutoffWindowBound (archivedGaussianVaughanLowerSum W) ↔
      GaussianCutoffWindowBound archivedGaussianVaughanPrimeBand := by
  obtain ⟨A, hA, hLeft⟩ := archivedGaussianVaughanLowerPrimeSum_error hDir W hW hUnit hSupport
  obtain ⟨B, hB, hRight⟩ := archivedGaussianVaughanPrimeBand_approx hDir
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hDiff : ∀ᶠ X : ℝ in atTop,
      |archivedGaussianVaughanLowerSum W X - archivedGaussianVaughanPrimeBand X| ≤
        (A + B) * (X ^ (3 / 8 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ)) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), hLog, hLeft, hRight] with X hX hLog hLeft hRight
    let v := X ^ (3 / 8 : ℝ)
    let L := (Real.log X) ^ (8 / 3 : ℝ)
    have hV : 0 ≤ v := by dsimp [v]; positivity
    have hL : 1 ≤ L := Real.one_le_rpow hLog (by norm_num)
    calc
      _ ≤ |archivedGaussianVaughanLowerSum W X - archivedGaussianVaughanSum X| +
          |archivedGaussianVaughanSum X - archivedGaussianVaughanPrimeBand X| := abs_sub_le _ _ _
      _ ≤ A * (v * L) + B * (v * L) := add_le_add
        (by rwa [abs_sub_comm])
        (hRight.trans ((mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hV hL) hB)))
      _ = _ := by dsimp [v, L]; ring
  have hDiff' : ∀ᶠ X : ℝ in atTop,
      |archivedGaussianVaughanPrimeBand X - archivedGaussianVaughanLowerSum W X| ≤
        (A + B) * (X ^ (3 / 8 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ)) :=
    hDiff.mono fun X h => by rwa [abs_sub_comm]
  exact ⟨gaussianLogWindow_error_transfer (add_nonneg hA hB) hDiff',
    gaussianLogWindow_error_transfer (add_nonneg hA hB) hDiff⟩

theorem quartic_rh_of_archived_vaughan_prime_band
    (hDir : DirichletLZerosOnLine)
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hBand : GaussianCutoffWindowBound archivedGaussianVaughanPrimeBand) :
    DedekindZetaRH QuarticModel.K := by
  let W (u : ℝ) : ℝ := if u ≤ 1 then 1 else 0
  have hW : ∀ u ≥ 0, |W u| ≤ 1 := by
    intro u _
    by_cases hu : u ≤ 1 <;> simp [W, hu]
  have hUnit : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → W u = 1 := by
    intro u _ hu
    simp [W, hu]
  have hSupport : ∀ u ≥ 2, W u = 0 := by
    intro u hu
    have h : ¬u ≤ 1 := by linarith
    simp [W, h]
  exact quartic_rh_of_archived_vaughan_signed_windows hDir hFree hpos W hW hUnit hSupport
    ((archivedGaussianVaughanPrimeBand_window_iff hDir W hW hUnit hSupport).mpr hBand)

#check archivedGaussianVaughanPrimeBand_approx
#check archivedGaussianVaughanPrimeBand_window_iff
#check quartic_rh_of_archived_vaughan_prime_band
#print axioms archivedGaussianVaughanPrimeBand_eq_sum
#print axioms archivedGaussianVaughanPrimeBand_approx
#print axioms archivedGaussianVaughanPrimeBand_window_iff
#print axioms quartic_rh_of_archived_vaughan_prime_band

end
end AlpogeSuperZeta
