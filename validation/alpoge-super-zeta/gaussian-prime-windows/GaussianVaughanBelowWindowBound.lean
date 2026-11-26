import GaussianVaughanKernelAtZero
import GaussianVaughanCompletedPrimeBound
import GaussianVaughanPrimePowers
import GaussianVaughanPrimeComplement

/-! Bound the exact contribution below the complementary prime window.
Every nonzero term samples the convolved kernel at a small argument. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Filter Finset QuarticModel FieldTarget ArtinPrimitiveRootsConjecture
open scoped Classical

noncomputable section

private theorem convolvedKernel_below_log_cutoff :
    ∃ C > 0, ∀ᶠ X : ℝ in atTop, ∀ v > 0, v ≤ (Real.log X) ^ (-(7 / 3 : ℝ)) →
      |archivedGaussianVaughanConvolvedKernel v| ≤ C / X ^ (5 : ℕ) := by
  obtain ⟨C, hC, c, hc, v₀, hv₀, hKernel⟩ := archivedGaussianVaughanConvolvedKernel_small_argument
  refine ⟨C, hC, ?_⟩
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hV := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 3)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop v₀⁻¹)
  have hRate := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 45)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop (5 / c))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hLog, hV, hRate]
    with X hX hLog hV hRate v hv hvle
  let ℓ := Real.log X
  have hℓ : 0 < ℓ := zero_lt_one.trans_le hLog
  have hLarge : v₀⁻¹ ≤ ℓ ^ (7 / 3 : ℝ) := hV
  have hSmall : v ≤ v₀ := hvle.trans (by
    change ℓ ^ (-(7 / 3 : ℝ)) ≤ v₀
    rw [Real.rpow_neg hℓ.le]
    exact (inv_le_comm₀ (Real.rpow_pos_of_pos hℓ _) hv₀).mpr hLarge)
  have hPower : ℓ ^ (49 / 45 : ℝ) ≤ v ^ (-(7 / 15 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos hv hvle (by norm_num : -(7 / 15 : ℝ) ≤ 0)
    change (ℓ ^ (-(7 / 3 : ℝ))) ^ (-(7 / 15 : ℝ)) ≤ _ at h
    rw [← Real.rpow_mul hℓ.le,
      show (-(7 / 3 : ℝ)) * (-(7 / 15 : ℝ)) = 49 / 45 by norm_num] at h
    exact h
  have hRate' : (5 : ℝ) ≤ c * ℓ ^ (4 / 45 : ℝ) := by
    rw [mul_comm]
    exact (div_le_iff₀ hc).mp hRate
  have hCost : 5 * ℓ ≤ c * v ^ (-(7 / 15 : ℝ)) := by
    calc
      _ ≤ (c * ℓ ^ (4 / 45 : ℝ)) * ℓ := mul_le_mul_of_nonneg_right hRate' hℓ.le
      _ = c * ℓ ^ (49 / 45 : ℝ) := by
        rw [show (49 / 45 : ℝ) = 4 / 45 + 1 by norm_num, Real.rpow_add hℓ, Real.rpow_one]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hPower hc.le
  have hExp : Real.exp (-(5 * ℓ)) = (X ^ (5 : ℕ))⁻¹ := by
    rw [Real.exp_neg, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.exp_nat_mul,
      show Real.exp ℓ = X from Real.exp_log (zero_lt_one.trans hX)]
  calc
    _ ≤ C * Real.exp (-c * v ^ (-(7 / 15 : ℝ))) := hKernel v hv hSmall
    _ ≤ C * Real.exp (-(5 * ℓ)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      linarith
    _ = _ := by rw [hExp, div_eq_mul_inv]

theorem archivedGaussianVaughanBelowWindowSum_inv_bound (W : ℝ → ℝ)
    (hW : ∀ u ≥ 0, |W u| ≤ 1) :
    ∃ C > 0, ∀ᶠ X : ℝ in atTop, |archivedGaussianVaughanBelowWindowSum W X| ≤ C / X := by
  obtain ⟨C, hC, hKernel⟩ := convolvedKernel_below_log_cutoff
  refine ⟨32 * C, by positivity, ?_⟩
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hLogCut := (isLittleO_log_rpow_rpow_atTop (8 / 3 : ℝ)
    (show (0 : ℝ) < 1 by norm_num)).def (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hLog, hLogCut, hKernel]
    with X hX hLog hLogCut hKernel
  have hX₀ := zero_lt_one.trans_le hX
  let ℓ := Real.log X
  have hℓ := zero_lt_one.trans_le hLog
  let L := ℓ ^ (8 / 3 : ℝ)
  let V := X / ℓ ^ (5 / 2 : ℝ)
  let q := X / ℓ ^ (5 : ℕ)
  have hL₀ : 0 ≤ L := Real.rpow_nonneg hℓ.le _
  have hL : L ≤ X := by
    change ‖L‖ ≤ _ at hLogCut
    rw [Real.norm_of_nonneg hL₀, Real.rpow_one, Real.norm_of_nonneg hX₀.le, one_mul] at hLogCut
    exact hLogCut
  have hV : 0 < V := div_pos hX₀ (Real.rpow_pos_of_pos hℓ _)
  have hq : q ≤ X := div_le_self hX₀.le (one_le_pow₀ hLog)
  let ms := Icc 1 (Nat.floor L)
  let ps := (range (Nat.floor (2 * V) + 1)).filter (fun p : ℕ => (p : ℝ) ≤ q)
  have hmCount : (ms.card : ℝ) ≤ X := by
    simpa [ms, Nat.card_Icc] using (Nat.floor_le hL₀).trans hL
  have hpBound (p : ℕ) (hp : p ∈ ps) : (p : ℝ) ≤ X :=
    (mem_filter.mp hp).2.trans hq
  have hpSub : ps ⊆ range (Nat.floor X + 1) := by
    intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hX₀.le).mpr (hpBound p hp)))
  have hpCount : (ps.card : ℝ) ≤ 2 * X := by
    have hn : ps.card ≤ Nat.floor X + 1 := by
      simpa only [card_range] using card_le_card hpSub
    have h : (ps.card : ℝ) ≤ ((Nat.floor X + 1 : ℕ) : ℝ) := by exact_mod_cast hn
    push_cast at h
    linarith [Nat.floor_le hX₀.le]
  let f (m p : ℕ) : ℝ := (archivedGaussianMoebiusCoefficients m).re *
    ((archivedGaussianVaughanPrimeCoefficients p).re *
      archivedGaussianVaughanConvolvedKernel (p * (m / X)) * W (p / V))
  have hTerm (m : ℕ) (hm : m ∈ ms) (p : ℕ) (hp : p ∈ ps) :
      |f m p| ≤ 16 * C * X ^ (2 : ℕ) / X ^ (5 : ℕ) := by
    by_cases hPrime : p.Prime
    · have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
      have hm₀ := zero_lt_one.trans_le hm₁
      have hmL : (m : ℝ) ≤ L :=
        (Nat.cast_le.mpr (mem_Icc.mp hm).2).trans (Nat.floor_le hL₀)
      have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr hPrime.pos
      have hpQ : (p : ℝ) ≤ q := (mem_filter.mp hp).2
      have hv : 0 < (p : ℝ) * (m / X) := mul_pos hp₀ (div_pos hm₀ hX₀)
      have hvUpper : (p : ℝ) * (m / X) ≤ ℓ ^ (-(7 / 3 : ℝ)) := by
        calc
          _ ≤ q * (L / X) := mul_le_mul hpQ
            (div_le_div_of_nonneg_right hmL hX₀.le) (div_nonneg hm₀.le hX₀.le)
            (hp₀.le.trans hpQ)
          _ = L / ℓ ^ (5 : ℕ) := by
            dsimp only [q]
            field_simp
          _ = _ := by
            dsimp only [L]
            rw [← Real.rpow_natCast ℓ 5, ← Real.rpow_sub hℓ]
            norm_num [ℓ]
      have hK := hKernel _ hv hvUpper
      have hA : |(archivedGaussianMoebiusCoefficients m).re| ≤ 8 * X := by
        refine (Complex.abs_re_le_norm _).trans
          ((archivedGaussianMoebius_three_eighths_bound (Nat.ne_of_gt (mem_Icc.mp hm).1)).trans ?_)
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        refine le_trans ?_ (hmL.trans hL)
        have hPow : (m : ℝ) ^ (3 / 8 : ℝ) ≤ (m : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hm₁ (by norm_num)
        simpa only [Real.rpow_one] using hPow
      have hP : |(archivedGaussianVaughanPrimeCoefficients p).re| ≤ 2 * X := by
        simp only [archivedGaussianVaughanPrimeCoefficients, ArithmeticFunction.coe_mk, if_pos hPrime]
        refine (Complex.abs_re_le_norm _).trans ((archivedGaussianMangoldt_norm_le p).trans ?_)
        rw [vonMangoldt_apply_prime hPrime]
        have hLogP : Real.log (p : ℝ) ≤ p := by linarith [Real.log_le_sub_one_of_pos hp₀]
        exact mul_le_mul_of_nonneg_left (hLogP.trans (hpBound p hp)) (by norm_num)
      have hWt := hW (p / V) (div_nonneg hp₀.le hV.le)
      dsimp only [f]
      simp only [abs_mul]
      calc
        _ ≤ (8 * X) * ((2 * X) * (C / X ^ (5 : ℕ)) * 1) := by gcongr
        _ = _ := by ring
    · simp only [f, archivedGaussianVaughanPrimeCoefficients, ArithmeticFunction.coe_mk,
        if_neg hPrime, Complex.zero_re, zero_mul, mul_zero, abs_zero]
      positivity
  have hSum :
      archivedGaussianVaughanBelowWindowSum W X = ∑ m ∈ ms, ∑ p ∈ ps, f m p := by
    change (∑ m ∈ ms, (archivedGaussianMoebiusCoefficients m).re *
      ∑ p ∈ ps, (archivedGaussianVaughanPrimeCoefficients p).re *
        archivedGaussianVaughanConvolvedKernel (p * (m / X)) * W (p / V)) = _
    simp only [mul_sum, f]
  let E := 16 * C * X ^ (2 : ℕ) / X ^ (5 : ℕ)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  rw [hSum]
  calc
    _ ≤ ∑ m ∈ ms, |∑ p ∈ ps, f m p| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ ms, ∑ p ∈ ps, |f m p| :=
      sum_le_sum fun m _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ ms, ∑ _p ∈ ps, E := sum_le_sum fun m hm => sum_le_sum fun p hp => hTerm m hm p hp
    _ = (ms.card : ℝ) * ((ps.card : ℝ) * E) := by simp [sum_const, nsmul_eq_mul]
    _ ≤ X * (2 * X * E) := by gcongr
    _ = _ := by dsimp [E]; field_simp; ring

/-- The upper approximation is the remaining input to the three-part
complementary error estimate. -/
theorem quartic_rh_of_archived_vaughan_windows_upper_error
    (hDir : DirichletLZerosOnLine)
    (hFree : ∀ w : ℂ, archivedGaussianKnownBoundary < w.re → archivedGaussianFactor w ≠ 0)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (W : ℝ → ℝ) (hW : ∀ u ≥ 0, |W u| ≤ 1) (hSupport : ∀ u ≥ 2, W u = 0)
    {A : ℝ} (hA : 0 ≤ A)
    (hUpper : ∀ᶠ X : ℝ in atTop, |archivedGaussianVaughanSum X -
      archivedGaussianVaughanUpperPrimeSum W X| ≤
        A * (X ^ (3 / 8 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ)))
    (hcut : GaussianCutoffWindowBound (archivedGaussianVaughanLowerSum W)) :
    DedekindZetaRH QuarticModel.K := by
  obtain ⟨B, hB, hPrime⟩ := archivedGaussianVaughan_complement_error_with_prime_bound hDir
  obtain ⟨C, hC, hBelow⟩ := archivedGaussianVaughanBelowWindowSum_inv_bound W hW
  apply quartic_rh_of_archived_vaughan_prime_windows hDir hFree hpos W
    (C := A + B + C) (by positivity) _ hcut
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  filter_upwards [eventually_gt_atTop (1 : ℝ), hLog, hUpper, hBelow]
    with X hX hLog hUpper hBelow
  let E := X ^ (3 / 8 : ℝ) * (Real.log X) ^ (8 / 3 : ℝ)
  have hE : 1 ≤ E := by
    have h₁ := Real.one_le_rpow hX.le (by norm_num : (0 : ℝ) ≤ 3 / 8)
    have h₂ := Real.one_le_rpow hLog (by norm_num : (0 : ℝ) ≤ 8 / 3)
    exact (le_mul_of_one_le_left (by positivity) h₁).trans' h₂
  have hc : |archivedGaussianVaughanBelowWindowSum W X| ≤ C * E :=
    hBelow.trans ((div_le_self hC.le hX.le).trans (le_mul_of_one_le_right hC.le hE))
  calc
    _ ≤ |archivedGaussianVaughanSum X - archivedGaussianVaughanUpperPrimeSum W X| +
        B * E + |archivedGaussianVaughanBelowWindowSum W X| := hPrime W hSupport X hX
    _ ≤ A * E + B * E + C * E := add_le_add (add_le_add_left hUpper _) hc
    _ = _ := by dsimp [E]; ring

#check archivedGaussianVaughanBelowWindowSum_inv_bound
#check quartic_rh_of_archived_vaughan_windows_upper_error
#print axioms archivedGaussianVaughanBelowWindowSum_inv_bound
#print axioms quartic_rh_of_archived_vaughan_windows_upper_error

end
end AlpogeSuperZeta
