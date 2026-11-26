import GaussianDyadicPairMoment
import Mathlib.Data.Nat.Sqrt

/-! Two parts of the prime-pair expansion are uniformly bounded. They are
the diagonal and the outer band where the two log intervals barely overlap. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

noncomputable section

private def pairTerm (θ U V : ℝ) (p q : ℕ) : ℝ :=
  (archivedGaussianSignedPrimeWeight p * archivedGaussianSignedPrimeWeight q) *
    dyadicPrimePairKernel θ U V p q

private theorem pairTerm_comm (θ U V : ℝ) (p q : ℕ) :
    pairTerm θ U V p q = pairTerm θ U V q p := by
  rw [pairTerm, pairTerm, mul_comm (archivedGaussianSignedPrimeWeight p),
    dyadicPrimePairKernel_comm θ U V p q]

private theorem signedPrimeWeight_abs_le_log (p : ℕ) :
    |archivedGaussianSignedPrimeWeight p| ≤ 2 * Real.log (p : ℝ) := by
  by_cases hp : p.Prime
  · exact archivedGaussianSignedPrimeWeight_abs_le hp
  · simpa [archivedGaussianSignedPrimeWeight, hp] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.log_natCast_nonneg p)

private def logSquaredPower (θ : ℝ) (p : ℕ) : ℝ :=
  (Real.log (p : ℝ)) ^ 2 * (p : ℝ) ^ (-2 * θ)

private theorem logSquaredPower_nonneg (θ : ℝ) (p : ℕ) : 0 ≤ logSquaredPower θ p := by
  unfold logSquaredPower
  positivity

private theorem logSquaredPower_summable {θ : ℝ} (hθ : 1 / 2 < θ) :
    Summable (logSquaredPower θ) := by
  let ε := (θ - 1 / 2) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hExponent : -2 * θ + 2 * ε < -1 := by dsimp [ε]; linarith
  have hMajor := (Real.summable_nat_rpow.mpr hExponent).mul_left ((ε⁻¹) ^ 2)
  refine hMajor.of_nonneg_of_le (logSquaredPower_nonneg θ) fun p => ?_
  by_cases hp : p = 0
  · subst p
    simpa [logSquaredPower] using mul_nonneg (sq_nonneg (ε⁻¹))
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 0) (-2 * θ + 2 * ε))
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
  calc
    logSquaredPower θ p ≤ ((p : ℝ) ^ ε / ε) ^ 2 * (p : ℝ) ^ (-2 * θ) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Real.log_natCast_nonneg p) (Real.log_natCast_le_rpow_div p hε) 2)
        (Real.rpow_nonneg hp₀.le _)
    _ = (ε⁻¹) ^ 2 * ((((p : ℝ) ^ ε) * ((p : ℝ) ^ ε)) * ((p : ℝ) ^ (-2 * θ))) := by
      rw [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [← Real.rpow_add hp₀, ← Real.rpow_add hp₀]
      congr 2
      ring

private theorem pairDiagonal_le {θ : ℝ} (hθ : 0 ≤ θ) (U V : ℝ) (p : ℕ) :
    pairTerm θ U V p p ≤ (4 * Real.log 2) * logSquaredPower θ p := by
  by_cases hp : p = 0
  · subst p
    simp [pairTerm, archivedGaussianSignedPrimeWeight, logSquaredPower]
  have hSq : (archivedGaussianSignedPrimeWeight p) ^ 2 ≤ 4 * (Real.log (p : ℝ)) ^ 2 := by
    calc
      _ = |archivedGaussianSignedPrimeWeight p| ^ 2 := (sq_abs _).symm
      _ ≤ (2 * Real.log (p : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (signedPrimeWeight_abs_le_log p) 2
      _ = _ := by ring
  calc
    _ = (archivedGaussianSignedPrimeWeight p) ^ 2 * dyadicPrimePairKernel θ U V p p := by
      rw [pairTerm, pow_two]
    _ ≤ (4 * (Real.log (p : ℝ)) ^ 2) * (Real.log 2 * (p : ℝ) ^ (-2 * θ)) :=
      mul_le_mul hSq (dyadicPrimePairKernel_le_log_two hθ (Nat.pos_of_ne_zero hp))
        (dyadicPrimePairKernel_nonneg θ U V p p) (by positivity)
    _ = _ := by unfold logSquaredPower; ring

private def outerPartners (p N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun q => p < q ∧ 2 * p - p.sqrt ≤ q ∧ q < 2 * p)

private theorem outerPartners_card_le (p N : ℕ) : (outerPartners p N).card ≤ p.sqrt := by
  have hSub : outerPartners p N ⊆ Finset.Ico (2 * p - p.sqrt) (2 * p) := by
    intro q hq
    have h := (Finset.mem_filter.mp hq).2
    exact Finset.mem_Ico.mpr ⟨h.2.1, h.2.2⟩
  have hCard := Finset.card_le_card hSub
  rw [Nat.card_Ico] at hCard
  have hs := Nat.sqrt_le_self p
  omega

private theorem outerPair_abs_le {θ U V : ℝ} {p q : ℕ} (hθ : 0 ≤ θ)
    (hp : p.Prime) (hpq : p < q) (hL : 2 * p - p.sqrt ≤ q) (hR : q < 2 * p) :
    |pairTerm θ U V p q| ≤
      (8 * (Real.log (p : ℝ)) ^ 2) * (((p.sqrt : ℝ) / (p : ℝ)) * (p : ℝ) ^ (-2 * θ)) := by
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpq' : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq.le
  have hq₀ : 0 < (q : ℝ) := hp₀.trans_le hpq'
  have hq₂' : (q : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hR.le
  have hgap : 2 * (p : ℝ) - (q : ℝ) ≤ (p.sqrt : ℝ) := by
    have hAdd : 2 * p ≤ q + p.sqrt := by omega
    have hAdd' : 2 * (p : ℝ) ≤ (q : ℝ) + (p.sqrt : ℝ) := by exact_mod_cast hAdd
    linarith
  have hRatio : (2 * (p : ℝ) - (q : ℝ)) / (q : ℝ) ≤ (p.sqrt : ℝ) / (p : ℝ) :=
    (div_le_div_of_nonneg_right hgap hq₀.le).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hp₀ hpq')
  have hLog : Real.log (q : ℝ) ≤ 2 * Real.log (p : ℝ) := by
    have h := Real.log_le_log hq₀ hq₂'
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hp₀.ne'] at h
    have hp₂ : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith only [h, Real.log_le_log (by norm_num : (0 : ℝ) < 2) hp₂]
  have hK : dyadicPrimePairKernel θ U V p q ≤ ((p.sqrt : ℝ) / (p : ℝ)) * (p : ℝ) ^ (-2 * θ) :=
    (dyadicPrimePairKernel_le_outer_gap hθ (hp.pos.trans hpq) hR.le).trans
      (mul_le_mul hRatio (Real.rpow_le_rpow_of_nonpos hp₀ hpq' (by linarith))
        (Real.rpow_nonneg hq₀.le _) (by positivity))
  rw [pairTerm, abs_mul, abs_mul, abs_of_nonneg (dyadicPrimePairKernel_nonneg θ U V p q)]
  apply mul_le_mul _ hK (dyadicPrimePairKernel_nonneg θ U V p q) (by positivity)
  calc
    _ ≤ (2 * Real.log (p : ℝ)) * (2 * Real.log (q : ℝ)) :=
      mul_le_mul (signedPrimeWeight_abs_le_log p) (signedPrimeWeight_abs_le_log q)
        (abs_nonneg _) (by positivity)
    _ ≤ (2 * Real.log (p : ℝ)) * (2 * (2 * Real.log (p : ℝ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLog (by norm_num))
        (by positivity)
    _ = _ := by ring

private theorem pairOuterRow_le {θ : ℝ} (hθ : 0 ≤ θ) (U V : ℝ) (p N : ℕ) :
    ∑ q ∈ outerPartners p N, pairTerm θ U V p q ≤ 8 * logSquaredPower θ p := by
  by_cases hp : p.Prime
  · have hp₀ : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    let B := (8 * (Real.log (p : ℝ)) ^ 2) * (((p.sqrt : ℝ) / (p : ℝ)) * (p : ℝ) ^ (-2 * θ))
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hFrac : (p.sqrt : ℝ) * ((p.sqrt : ℝ) / (p : ℝ)) ≤ 1 := by
      rw [← mul_div_assoc, div_le_iff₀ hp₀, one_mul]
      exact_mod_cast Nat.sqrt_le p
    calc
      _ ≤ ∑ _q ∈ outerPartners p N, B := by
        apply Finset.sum_le_sum
        intro q hq
        obtain ⟨hpq, hL, hR⟩ := (Finset.mem_filter.mp hq).2
        exact (le_abs_self _).trans (outerPair_abs_le hθ hp hpq hL hR)
      _ = ((outerPartners p N).card : ℝ) * B := by simp
      _ ≤ (p.sqrt : ℝ) * B :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast outerPartners_card_le p N) hB
      _ = (8 * logSquaredPower θ p) * ((p.sqrt : ℝ) * ((p.sqrt : ℝ) / (p : ℝ))) := by
        unfold logSquaredPower
        dsimp [B]
        ring
      _ ≤ _ := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hFrac (mul_nonneg (by norm_num) (logSquaredPower_nonneg θ p))
  · have h : archivedGaussianSignedPrimeWeight p = 0 := by simp [archivedGaussianSignedPrimeWeight, hp]
    simpa [pairTerm, h] using (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) (logSquaredPower_nonneg θ p))

/-- The signed pairs strictly above the diagonal and below the outer
band. The omitted terms have a uniform upper bound for θ > 1/2. -/
def archivedGaussianDyadicInteriorMoment (θ U V : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (⌊Real.exp V⌋₊ + 1),
    ∑ q ∈ (Finset.range (⌊Real.exp V⌋₊ + 1)).filter (fun q => p < q ∧ q < 2 * p - p.sqrt),
      pairTerm θ U V p q

private theorem pairSum_eq_diagonal_add_twice (θ U V : ℝ) (S : Finset ℕ) :
    (∑ p ∈ S, ∑ q ∈ S, pairTerm θ U V p q) =
      (∑ p ∈ S, pairTerm θ U V p p) +
        2 * (∑ p ∈ S, ∑ q ∈ S, if p < q then pairTerm θ U V p q else 0) := by
  have hPart (p q : ℕ) : pairTerm θ U V p q =
      (if q = p then pairTerm θ U V p q else 0) +
        (if p < q then pairTerm θ U V p q else 0) +
        (if q < p then pairTerm θ U V p q else 0) := by
    rcases lt_trichotomy p q with h | rfl | h
    · simp [h, h.ne.symm, not_lt_of_ge h.le]
    · simp
    · simp [h, h.ne, not_lt_of_ge h.le]
  have hDiag : (∑ p ∈ S, ∑ q ∈ S, if q = p then pairTerm θ U V p q else 0) =
      ∑ p ∈ S, pairTerm θ U V p p := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [hp]
  have hSwap :
      (∑ p ∈ S, ∑ q ∈ S, if q < p then pairTerm θ U V p q else 0) =
      ∑ p ∈ S, ∑ q ∈ S, if p < q then pairTerm θ U V p q else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [pairTerm_comm θ U V q p]
  calc
    _ = ∑ p ∈ S, ∑ q ∈ S,
        ((if q = p then pairTerm θ U V p q else 0) +
          (if p < q then pairTerm θ U V p q else 0) +
          (if q < p then pairTerm θ U V p q else 0)) :=
      Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hPart p q))
    _ = _ := by simp only [Finset.sum_add_distrib, hDiag, hSwap]; ring

private theorem pairTriangle_row_split (θ U V : ℝ) (p N : ℕ) :
    (∑ q ∈ Finset.range N, if p < q then pairTerm θ U V p q else 0) =
      (∑ q ∈ (Finset.range N).filter (fun q => p < q ∧ q < 2 * p - p.sqrt), pairTerm θ U V p q) +
      (∑ q ∈ outerPartners p N, pairTerm θ U V p q) := by
  rw [outerPartners, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hpq : p < q
  · by_cases hCore : q < 2 * p - p.sqrt
    · simp [hpq, hCore, not_le_of_gt hCore]
    · by_cases hNear : q < 2 * p
      · simp [hpq, hCore, hNear, le_of_not_gt hCore]
      · have hz : pairTerm θ U V p q = 0 := by
          by_cases hp : 0 < p
          · rw [pairTerm, dyadicPrimePairKernel_eq_zero_of_twice_le hp (le_of_not_gt hNear), mul_zero]
          · have hp₀ : p = 0 := by omega
            simp [pairTerm, hp₀, archivedGaussianSignedPrimeWeight]
        simp [hpq, hCore, hNear, hz]
  · simp [hpq]

theorem archivedGaussianDyadicSecondMoment_le_interior_add {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ C ≥ (0 : ℝ), ∀ U V : ℝ, archivedGaussianDyadicSecondMoment θ U V ≤
      2 * archivedGaussianDyadicInteriorMoment θ U V + C := by
  let total := ∑' p : ℕ, logSquaredPower θ p
  have hTotal : 0 ≤ total := tsum_nonneg (logSquaredPower_nonneg θ)
  have hSeries := logSquaredPower_summable hθ
  have hθ₀ : 0 ≤ θ := by linarith
  refine ⟨(4 * Real.log 2 + 16) * total, by positivity, fun U V => ?_⟩
  let N := ⌊Real.exp V⌋₊ + 1
  let S := Finset.range N
  have hSum : (∑ p ∈ S, logSquaredPower θ p) ≤ total :=
    hSeries.sum_le_tsum S (fun p _ => logSquaredPower_nonneg θ p)
  have hD : (∑ p ∈ S, pairTerm θ U V p p) ≤ (4 * Real.log 2) * total := by
    calc
      _ ≤ ∑ p ∈ S, (4 * Real.log 2) * logSquaredPower θ p :=
        Finset.sum_le_sum (fun p _ => pairDiagonal_le hθ₀ U V p)
      _ = (4 * Real.log 2) * (∑ p ∈ S, logSquaredPower θ p) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hSum (by positivity)
  have hO : (∑ p ∈ S, ∑ q ∈ outerPartners p N, pairTerm θ U V p q) ≤ 8 * total := by
    calc
      _ ≤ ∑ p ∈ S, 8 * logSquaredPower θ p :=
        Finset.sum_le_sum (fun p _ => pairOuterRow_le hθ₀ U V p N)
      _ = 8 * (∑ p ∈ S, logSquaredPower θ p) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hSum (by norm_num)
  rw [archivedGaussianDyadicSecondMoment_eq_pairs]
  change (∑ p ∈ S, ∑ q ∈ S, pairTerm θ U V p q) ≤ _
  rw [pairSum_eq_diagonal_add_twice]
  have hT : (∑ p ∈ S, ∑ q ∈ S, if p < q then pairTerm θ U V p q else 0) =
      archivedGaussianDyadicInteriorMoment θ U V +
        (∑ p ∈ S, ∑ q ∈ outerPartners p N, pairTerm θ U V p q) := by
    unfold archivedGaussianDyadicInteriorMoment
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => pairTriangle_row_split θ U V p N)
  rw [hT]
  linarith only [hD, hO]

#print axioms logSquaredPower_summable
#print axioms pairDiagonal_le
#print axioms pairOuterRow_le
#print axioms archivedGaussianDyadicSecondMoment_le_interior_add

end
end GaussianQuarticClosure
end AlpogeSuperZeta
