import GaussianVaughanUpperShortPrime

/-! For cofactors beyond the stated logarithmic limit, every nonzero
upper-prime term sees a large argument of the convolved kernel. -/

namespace AlpogeSuperZeta

open Complex Filter QuarticModel
open scoped Classical

noncomputable section

private theorem gaussian_term_norm_at_two (a : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖LSeries.term a (2 : ℂ) n‖ = ‖a n‖ / (n : ℝ) ^ (2 : ℕ) := by
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  rw [LSeries.term_of_ne_zero hn, norm_div, ← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos hn₀]
  norm_num [Real.rpow_two]

set_option maxHeartbeats 700000 in
theorem archivedGaussianVaughanUpperCofactorTail_inv_bound (W : ℝ → ℝ)
    (hW : ∀ u ≥ 0, |W u| ≤ 1) (hUnit : ∀ u : ℝ, 0 ≤ u → u ≤ 1 → W u = 1) :
    ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop, ‖archivedGaussianVaughanUpperCofactorTail W X‖ ≤ C / X := by
  obtain ⟨D, hD, c, hc, T, hT, hLarge⟩ := archivedGaussianVaughanConvolvedKernel_large_exp
  let A := archivedGaussianMoebiusCoefficients
  let P := archivedGaussianVaughanPrimeCoefficients
  let a (m : ℕ) := ‖LSeries.term A (2 : ℂ) m‖
  let b (p : ℕ) := ‖LSeries.term P (2 : ℂ) p‖
  have ha : Summable a := archivedGaussianMoebius_summable_at_two.norm
  have hb : Summable b := (archivedGaussianVaughanPrime_summable (z := (2 : ℂ)) (by norm_num)).norm
  let B := ∑' p, b p
  have hB : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  have hA : 0 ≤ ∑' m, a m := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨(2 * D * B) * ∑' m, a m, by positivity, ?_⟩
  have hLog := Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))
  have hLogL := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
    Real.tendsto_log_atTop).eventually (eventually_ge_atTop T)
  have hLogE := gaussian_exp_log_power_eventually_inverse (a := c) (b := 7 / 6) hc (by norm_num) 3
  filter_upwards [eventually_ge_atTop (1 : ℝ), hLog, hLogL, hLogE]
    with X hX hLog hLogL hLogE
  have hx := zero_lt_one.trans_le hX
  let ℓ := Real.log X
  have hℓ : 0 < ℓ := zero_lt_one.trans_le hLog
  let L := ℓ ^ (8 / 3 : ℝ)
  have hL : 0 ≤ L := Real.rpow_nonneg hℓ.le _
  let V := X / ℓ ^ (5 / 2 : ℝ)
  have hBase : 0 < ℓ ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hℓ _
  have hV : 0 < V := div_pos hx hBase
  let W' (u : ℝ) := 1 - W u
  have hW' (u : ℝ) (hu : 0 ≤ u) : |W' u| ≤ 2 :=
    (abs_sub _ _).trans (by rw [abs_one]; linarith [hW u hu])
  let Q := archivedGaussianVaughanWeightedPrimes W' V
  have hProduct : V * (L / X) = ℓ ^ (1 / 6 : ℝ) := by
    calc
      _ = L / ℓ ^ (5 / 2 : ℝ) := by
        dsimp only [V]
        field_simp [hBase.ne', hx.ne']
      _ = _ := by
        dsimp only [L]
        rw [← Real.rpow_sub hℓ, show (8 / 3 : ℝ) - 5 / 2 = 1 / 6 by norm_num]
  have hBoundInner (m : ℕ) (hm : Nat.floor L < m) :
      ‖archivedGaussianVaughanWeightedPrimeReading W' V (m / X)‖ ≤
        (2 * D * B) / (X * (m : ℝ) ^ (2 : ℕ)) := by
    have hm₀ : 0 < (m : ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt hm)
    have hmL : L ≤ (m : ℝ) := le_of_lt (lt_of_not_ge (fun h =>
      (not_le_of_gt hm) ((Nat.le_floor_iff hL).mpr h)))
    let F (p : ℕ) : ℂ := Q p * (archivedGaussianVaughanConvolvedKernel (p * (m / X)) : ℂ)
    let M := 2 * D / (X * (m : ℝ) ^ (2 : ℕ))
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hTerm (p : ℕ) : ‖F p‖ ≤ M * b p := by
      by_cases hp : (p : ℝ) ≤ V
      · have hW1 := hUnit (p / V) (by positivity) ((div_le_iff₀ hV).mpr (by simpa using hp))
        have hQ : Q p = 0 := by simp [Q, archivedGaussianVaughanWeightedPrimes, W', hW1]
        simp only [F, hQ, zero_mul, norm_zero]
        positivity
      have hpV := lt_of_not_ge hp
      have hp₀ := hV.trans hpV
      have hpN : p ≠ 0 := by exact_mod_cast hp₀.ne'
      let u := (p : ℝ) * (m / X)
      have hu₀ : 0 < u := mul_pos hp₀ (div_pos hm₀ hx)
      have hLow : ℓ ^ (1 / 6 : ℝ) ≤ u := by
        rw [← hProduct]
        exact mul_le_mul hpV.le (div_le_div_of_nonneg_right hmL hx.le) (by positivity) hp₀.le
      have hu : T ≤ u := hLogL.trans hLow
      have hPowEq : (ℓ ^ (1 / 6 : ℝ)) ^ (7 : ℕ) = ℓ ^ (7 / 6 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hℓ.le]
        norm_num
      have hPow : ℓ ^ (7 / 6 : ℝ) ≤ u ^ (7 : ℕ) := by
        rw [← hPowEq]
        exact pow_le_pow_left₀ (by positivity) hLow _
      have hExp : Real.exp (-(c * u ^ (7 : ℕ))) ≤ (X ^ (3 : ℕ))⁻¹ :=
        (Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hPow hc.le))).trans hLogE
      have hK : |archivedGaussianVaughanConvolvedKernel u| ≤ D * (X ^ (3 : ℕ))⁻¹ / u ^ (2 : ℕ) :=
        (hLarge u hu).trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hExp hD)
          (by positivity))
      have hQ : ‖Q p‖ / (p : ℝ) ^ (2 : ℕ) ≤ 2 * b p := by
        rw [← gaussian_term_norm_at_two Q hpN]
        exact archivedGaussianVaughanWeightedPrimes_term_norm hV hW' p
      change ‖Q p * (archivedGaussianVaughanConvolvedKernel u : ℂ)‖ ≤ _
      rw [norm_mul, norm_real, Real.norm_eq_abs]
      calc
        _ ≤ ‖Q p‖ * (D * (X ^ (3 : ℕ))⁻¹ / u ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hK (norm_nonneg _)
        _ = (D / (X * (m : ℝ) ^ (2 : ℕ))) * (‖Q p‖ / (p : ℝ) ^ (2 : ℕ)) := by
          dsimp only [u]
          field_simp [hp₀.ne', hm₀.ne', hx.ne']
        _ ≤ (D / (X * (m : ℝ) ^ (2 : ℕ))) * (2 * b p) :=
          mul_le_mul_of_nonneg_left hQ (by positivity)
        _ = _ := by dsimp [M]; ring
    have hSum : Summable (fun p => ‖F p‖) :=
      (hb.mul_left M).of_nonneg_of_le (fun _ => norm_nonneg _) hTerm
    change ‖∑' p, F p‖ ≤ _
    calc
      _ ≤ ∑' p, ‖F p‖ := norm_tsum_le_tsum_norm hSum
      _ ≤ ∑' p, M * b p := hSum.tsum_le_tsum hTerm (hb.mul_left M)
      _ = _ := by rw [tsum_mul_left]; dsimp only [M, B]; ring
  let f (m : ℕ) : ℂ := if Nat.floor L < m then
    A m * archivedGaussianVaughanWeightedPrimeReading W' V (m / X) else 0
  let C := (2 * D * B) / X
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hTerm (m : ℕ) : ‖f m‖ ≤ C * a m := by
    by_cases hm : Nat.floor L < m
    · have hm₀ : 0 < (m : ℝ) := Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt hm)
      have hmN : m ≠ 0 := by exact_mod_cast hm₀.ne'
      rw [show f m = A m * archivedGaussianVaughanWeightedPrimeReading W' V (m / X) from if_pos hm,
        norm_mul]
      calc
        _ ≤ ‖A m‖ * ((2 * D * B) / (X * (m : ℝ) ^ (2 : ℕ))) :=
          mul_le_mul_of_nonneg_left (hBoundInner m hm) (norm_nonneg _)
        _ = _ := by
          rw [show a m = _ from gaussian_term_norm_at_two A hmN]
          dsimp [C]
          ring
    · simp only [f, if_neg hm, norm_zero]
      exact mul_nonneg hC (norm_nonneg _)
  have hf : Summable (fun m => ‖f m‖) :=
    (ha.mul_left C).of_nonneg_of_le (fun _ => norm_nonneg _) hTerm
  change ‖∑' m, f m‖ ≤ _
  calc
    _ ≤ ∑' m, ‖f m‖ := norm_tsum_le_tsum_norm hf
    _ ≤ ∑' m, C * a m := hf.tsum_le_tsum hTerm (ha.mul_left C)
    _ = _ := by rw [tsum_mul_left]; dsimp [C]; ring

#print axioms archivedGaussianVaughanUpperCofactorTail_inv_bound

end
end AlpogeSuperZeta
