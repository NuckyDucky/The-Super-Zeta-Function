import ArchivedGaussianTriangleWindow
import Mathlib.Analysis.SumIntegralComparisons

/-! An exact linear correction for the primes below the row-divisibility threshold. -/

namespace AlpogeSuperZeta

open ArtinPrimitiveRootsConjecture FieldTarget Finset Set
open scoped Classical

noncomputable section

/-- For one prime, the centered squared ramp has a rounding error between zero and one. -/
theorem squaredRampMultiples_rounding {x : ℝ} (hx : 0 < x) {p : ℕ} (hp : 0 < p) :
    let S := ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * p)
    0 ≤ x / (3 * (p : ℝ)) - S ∧ x / (3 * (p : ℝ)) - S ≤ 1 := by
  let N : ℕ := ⌈x⌉₊
  let q : ℝ := x / (p : ℝ)
  let f (t : ℝ) := (max (1 - t / q) 0) ^ 2
  have hp' : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hp₁ : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hq : 0 < q := div_pos hx hp'
  have hqN : q ≤ (N : ℝ) := (div_le_self hx.le hp₁).trans (Nat.le_ceil x)
  have hAnti : Antitone f := by
    intro a b hab
    exact pow_le_pow_left₀ (le_max_right _ _)
      (max_le_max (sub_le_sub_left (div_le_div_of_nonneg_right hab hq.le) _) le_rfl) _
  have hf : Continuous f := by
    unfold f
    fun_prop
  have hfZero (t : ℝ) (ht : q ≤ t) : f t = 0 := by
    have h := (le_div_iff₀ hq).mpr (by simpa using ht : (1 : ℝ) * q ≤ t)
    simp [f, max_eq_right (sub_nonpos.mpr h)]
  have hfOne (t : ℝ) (ht : t ≤ q) : f t = (1 - t / q) ^ 2 := by
    simp [f, max_eq_left (sub_nonneg.mpr ((div_le_one hq).mpr ht))]
  have hEnd : f (N : ℝ) = 0 := hfZero _ hqN
  have hStart : f 0 = 1 := by simp [f]
  have hI₀ : (∫ t in (0 : ℝ)..q, f t) = q / 3 := by
    calc
      _ = ∫ t in (0 : ℝ)..q, (1 - t / q) ^ 2 := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hq.le]
        exact fun t ht => hfOne t ht.2
      _ = q * ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 := by
        rw [intervalIntegral.integral_comp_div (fun t : ℝ => (1 - t) ^ 2) hq.ne']
        simp [hq.ne']
      _ = _ := by
        rw [intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ 2) (1 : ℝ)]
        norm_num [integral_pow]
        ring
  have hI₁ : (∫ t in q..(N : ℝ), f t) = 0 := by
    calc
      _ = ∫ _ in q..(N : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le hqN]
        exact fun t ht => hfZero t ht.1
      _ = 0 := intervalIntegral.integral_zero
  have hI : (∫ t in (0 : ℝ)..(N : ℝ), f t) = x / (3 * (p : ℝ)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 q) (hf.intervalIntegrable q N), hI₀, hI₁, add_zero]
    dsimp [q]
    ring
  have hWeight (m : ℕ) : f ((m + 1 : ℕ) : ℝ) = squaredRampWeight x ((m + 1) * p) := by
    have he : ((m + 1 : ℕ) : ℝ) / q = (((m + 1) * p : ℕ) : ℝ) / x := by
      dsimp [q]
      push_cast
      field_simp
    have hqEq : ∀ t : ℝ, t ≤ q ↔ t * (p : ℝ) ≤ x :=
      fun t => le_div_iff₀ hp'
    by_cases hm : (((m + 1) * p : ℕ) : ℝ) < x
    · rw [squaredRampWeight, if_pos hm, hfOne _ ((hqEq _).mpr (by exact_mod_cast hm.le)), he]
    · rw [squaredRampWeight, if_neg hm, hfZero _ ((div_le_iff₀ hp').mpr (by exact_mod_cast le_of_not_gt hm))]
  have hSumShift : (∑ m ∈ range N, f (m : ℝ)) =
      (∑ m ∈ range N, f ((m + 1 : ℕ) : ℝ)) + 1 := by
    have h₁ : (∑ m ∈ range (N + 1), f (m : ℝ)) = ∑ m ∈ range N, f (m : ℝ) := by
      rw [sum_range_succ, hEnd, add_zero]
    have h₂ : (∑ m ∈ range (N + 1), f (m : ℝ)) =
        (∑ m ∈ range N, f ((m + 1 : ℕ) : ℝ)) + 1 := by
      rw [sum_range_succ', Nat.cast_zero, hStart]
    exact h₁.symm.trans h₂
  have hLower : (∑ m ∈ range N, f ((m + 1 : ℕ) : ℝ)) ≤ x / (3 * (p : ℝ)) := by
    rw [← hI]
    simpa only [zero_add] using (hAnti.antitoneOn (s := Icc (0 : ℝ) (0 + N))).sum_le_integral
  have hUpper : x / (3 * (p : ℝ)) ≤ (∑ m ∈ range N, f ((m + 1 : ℕ) : ℝ)) + 1 := by
    rw [← hSumShift, ← hI]
    simpa only [zero_add] using (hAnti.antitoneOn (s := Icc (0 : ℝ) (0 + N))).integral_le_sum
  simp_rw [hWeight] at hLower hUpper
  exact ⟨sub_nonneg.mpr hLower, sub_le_iff_le_add.mpr (by simpa only [add_comm] using hUpper)⟩

def archivedGaussianLogCutTriangleWindow (x : ℝ) : ℝ :=
  (∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => Real.log x ≤ (p : ℝ)),
    archivedGaussianSignedPrimeWeight p *
      ((2 * Real.log x / x ^ 2) * (frobeniusTriangleDivisibility x (Real.log x) p : ℝ))) -
    x / 3 * (archivedGaussianPrimeCenter -
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p : ℝ) < Real.log x),
        archivedGaussianSignedPrimeWeight p / (p : ℝ))

theorem archivedGaussianLogCutTriangleWindow_sub_eq_sum (x : ℝ) :
    archivedGaussianLogCutTriangleWindow x - archivedGaussianTriangleWindow x =
      ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p : ℝ) < Real.log x),
        archivedGaussianSignedPrimeWeight p * (x / (3 * (p : ℝ)) -
          (2 * Real.log x / x ^ 2) * (frobeniusTriangleDivisibility x (Real.log x) p : ℝ)) := by
  let V (p : ℕ) := (2 * Real.log x / x ^ 2) * (frobeniusTriangleDivisibility x (Real.log x) p : ℝ)
  let w := archivedGaussianSignedPrimeWeight
  let P := range (⌊x⌋₊ + 1)
  let L := P.filter (fun p : ℕ => (p : ℝ) < Real.log x)
  let H := P.filter (fun p : ℕ => Real.log x ≤ (p : ℝ))
  have hPartition : (∑ p ∈ L, w p * V p) + (∑ p ∈ H, w p * V p) = ∑ p ∈ P, w p * V p := by
    simpa only [L, H, not_lt] using
      (sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) < Real.log x) (fun p => w p * V p))
  have hCenter : x / 3 * (∑ p ∈ L, w p / (p : ℝ)) = ∑ p ∈ L, w p * (x / (3 * (p : ℝ))) := by
    rw [mul_sum]
    exact sum_congr rfl fun p _ => by ring
  change ((∑ p ∈ H, w p * V p) -
      x / 3 * (archivedGaussianPrimeCenter - ∑ p ∈ L, w p / (p : ℝ))) -
        ((∑ p ∈ P, w p * V p) - x / 3 * archivedGaussianPrimeCenter) =
      ∑ p ∈ L, w p * (x / (3 * (p : ℝ)) - V p)
  rw [← hPartition, mul_sub, hCenter]
  simp_rw [mul_sub, sum_sub_distrib]
  ring

private theorem logCutTriangleTerm_bound {x : ℝ} (hx : 2 ≤ x) {p : ℕ} (hp : 0 < p)
    (hpCut : (p : ℝ) < Real.log x) :
    |x / (3 * (p : ℝ)) -
      (2 * Real.log x / x ^ 2) * (frobeniusTriangleDivisibility x (Real.log x) p : ℝ)| ≤
      (2 * Real.log x + 2 + 2 * Real.log x / x) / (p : ℝ) := by
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := one_pos.trans_le hx₁
  have hp₀ : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  let k := Real.log x
  have hk : 0 < k := Real.log_pos (by linarith)
  let V := (2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k p : ℝ)
  let S := ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * p)
  let B := (2 * k / x ^ 2) * (x + x / k + 1)
  let A := 2 * k + 2 + 2 * k / x
  have hA : B * x = A := by dsimp [B, A]; field_simp
  have hN : 1 ≤ ⌈x / (p : ℝ)⌉₊ :=
    Nat.lt_ceil.mpr (by simpa using div_pos hx₀ hp₀)
  have hCount : ((⌈x / (p : ℝ)⌉₊ - 1 : ℕ) : ℝ) ≤ x / (p : ℝ) := by
    rw [Nat.cast_sub hN, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one (div_pos hx₀ hp₀).le]
  have hRound := squaredRampMultiples_rounding hx₀ hp
  change 0 ≤ x / (3 * (p : ℝ)) - S ∧ x / (3 * (p : ℝ)) - S ≤ 1 at hRound
  have hTriangle := frobeniusTriangleDivisibility_error hx₁ hk hp
  change 0 ≤ V - S ∧ V - S ≤ B * ((⌈x / (p : ℝ)⌉₊ - 1 : ℕ) : ℝ) at hTriangle
  have hTriangleBound : V - S ≤ A / (p : ℝ) := by
    calc
      _ ≤ B * ((⌈x / (p : ℝ)⌉₊ - 1 : ℕ) : ℝ) := hTriangle.2
      _ ≤ B * (x / (p : ℝ)) := mul_le_mul_of_nonneg_left hCount (by dsimp [B]; positivity)
      _ = _ := by rw [← mul_div_assoc, hA]
  have hBody : 1 ≤ A / (p : ℝ) := by
    apply (le_div_iff₀ hp₀).mpr
    have hAux : 0 ≤ 2 * k / x := by positivity
    dsimp [A]
    change (p : ℝ) < k at hpCut
    linarith
  change |x / (3 * (p : ℝ)) - V| ≤ A / (p : ℝ)
  rw [abs_le]
  constructor <;> linarith [hRound.1, hRound.2, hTriangle.1]

theorem archivedGaussianLogCutTriangleWindow_error {x : ℝ} (hx : 2 ≤ x) :
    |archivedGaussianLogCutTriangleWindow x - archivedGaussianTriangleWindow x| ≤
      ((2 * Real.log x + 2 + 2 * Real.log x / x) * Real.log x ^ (1 / 4 : ℝ)) *
        (∑' p : ℕ, |archivedGaussianSignedPrimeWeight p| / ((max 1 p : ℕ) : ℝ) ^ (5 / 4 : ℝ)) := by
  let k := Real.log x
  have hk : 0 < k := Real.log_pos (by linarith)
  have hx₀ : 0 < x := by linarith
  let A := 2 * k + 2 + 2 * k / x
  let W (p : ℕ) := |archivedGaussianSignedPrimeWeight p| / ((max 1 p : ℕ) : ℝ) ^ (5 / 4 : ℝ)
  have hW : Summable W := archivedGaussianSignedPrimeWeight_summable (by norm_num)
  have hW₀ (p : ℕ) : 0 ≤ W p := by dsimp [W]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let L := (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p : ℝ) < k)
  let D (p : ℕ) := x / (3 * (p : ℝ)) - (2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k p : ℝ)
  rw [archivedGaussianLogCutTriangleWindow_sub_eq_sum]
  change |∑ p ∈ L, archivedGaussianSignedPrimeWeight p * D p| ≤
    (A * k ^ (1 / 4 : ℝ)) * ∑' p, W p
  calc
    _ ≤ ∑ p ∈ L, |archivedGaussianSignedPrimeWeight p * D p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ L, (A * k ^ (1 / 4 : ℝ)) * W p := by
      apply sum_le_sum
      intro p hp
      by_cases h : p.Prime
      · have hp₀ : (0 : ℝ) < p := Nat.cast_pos.mpr h.pos
        have hpk : (p : ℝ) < k := (mem_filter.mp hp).2
        have hPower : (p : ℝ) ^ (5 / 4 : ℝ) = (p : ℝ) ^ (1 / 4 : ℝ) * (p : ℝ) := by
          rw [show (5 / 4 : ℝ) = (1 / 4 : ℝ) + 1 by norm_num, Real.rpow_add hp₀, Real.rpow_one]
        have hFactor : |archivedGaussianSignedPrimeWeight p| / (p : ℝ) =
            (p : ℝ) ^ (1 / 4 : ℝ) * W p := by
          dsimp [W]
          rw [max_eq_right h.one_lt.le, hPower]
          field_simp
        rw [abs_mul]
        calc
          _ ≤ |archivedGaussianSignedPrimeWeight p| * (A / (p : ℝ)) :=
            mul_le_mul_of_nonneg_left (logCutTriangleTerm_bound hx h.pos hpk) (abs_nonneg _)
          _ = A * (|archivedGaussianSignedPrimeWeight p| / (p : ℝ)) := by ring
          _ ≤ _ := by
            rw [hFactor, mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp₀.le hpk.le (by norm_num)) (hW₀ p)) hA
      · have hz : archivedGaussianSignedPrimeWeight p = 0 := by simp [archivedGaussianSignedPrimeWeight, h]
        simpa only [hz, zero_mul, abs_zero] using
          mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hk.le _)) (hW₀ p)
    _ = (A * k ^ (1 / 4 : ℝ)) * ∑ p ∈ L, W p := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hW.sum_le_tsum _ fun p _ => hW₀ p) (by positivity)

theorem archivedGaussianLogCutTriangleWindow_error_sqrt {x : ℝ} (hx : 2 ≤ x) :
    |archivedGaussianLogCutTriangleWindow x - archivedGaussianTriangleWindow x| ≤
      (18 * (∑' p : ℕ, |archivedGaussianSignedPrimeWeight p| / ((max 1 p : ℕ) : ℝ) ^ (5 / 4 : ℝ))) *
        x ^ (1 / 2 : ℝ) := by
  let k := Real.log x
  let M := ∑' p : ℕ, |archivedGaussianSignedPrimeWeight p| / ((max 1 p : ℕ) : ℝ) ^ (5 / 4 : ℝ)
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := one_pos.trans_le hx₁
  have hk : 0 ≤ k := Real.log_nonneg hx₁
  have hM : 0 ≤ M := tsum_nonneg (fun _ => by positivity)
  have hlog : k ≤ 4 * x ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div (ε := (1 / 4 : ℝ)) hx₀.le (by norm_num)
    dsimp [k]
    linarith
  have hDiv : 2 * k / x ≤ 2 * k := div_le_self (by positivity) hx₁
  have hPow : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow hx₁ (by norm_num)
  have hFirst : 2 * k + 2 + 2 * k / x ≤ 18 * x ^ (1 / 4 : ℝ) := by linarith
  have hSecond : k ^ (1 / 4 : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow hk (Real.log_le_self hx₀.le) (by norm_num)
  calc
    _ ≤ ((2 * k + 2 + 2 * k / x) * k ^ (1 / 4 : ℝ)) * M :=
      archivedGaussianLogCutTriangleWindow_error hx
    _ ≤ ((18 * x ^ (1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ)) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul hFirst hSecond (by positivity) (by positivity)) hM
    _ = 18 * (x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ)) * M := by ring
    _ = _ := by
      rw [← Real.rpow_add hx₀ (1 / 4 : ℝ) (1 / 4 : ℝ),
        show (1 / 4 : ℝ) + 1 / 4 = 1 / 2 by norm_num]
      change 18 * x ^ (1 / 2 : ℝ) * M = (18 * M) * x ^ (1 / 2 : ℝ)
      ring

theorem archivedGaussianLogCutTriangleWindowBound_iff :
    GaussianCutoffWindowBound archivedGaussianLogCutTriangleWindow ↔
      GaussianCutoffWindowBound archivedGaussianTriangleWindow := by
  apply gaussianCutoffWindowBound_iff_of_error (X₀ := 2)
  intro θ hθ _
  let M := ∑' p : ℕ, |archivedGaussianSignedPrimeWeight p| / ((max 1 p : ℕ) : ℝ) ^ (5 / 4 : ℝ)
  have hM : 0 ≤ 18 * M := mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity)
  refine ⟨18 * M, hM, fun x hx => (archivedGaussianLogCutTriangleWindow_error_sqrt hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by linarith) hθ.le) hM

theorem quartic_rh_of_archived_gaussian_log_cut_triangle_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianLogCutTriangleWindow) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_triangle_windows hD hpos
    (archivedGaussianLogCutTriangleWindowBound_iff.mp hcut)

#print axioms squaredRampMultiples_rounding
#print axioms archivedGaussianLogCutTriangleWindow_sub_eq_sum
#print axioms archivedGaussianLogCutTriangleWindow_error
#print axioms archivedGaussianLogCutTriangleWindow_error_sqrt
#print axioms archivedGaussianLogCutTriangleWindowBound_iff
#check quartic_rh_of_archived_gaussian_log_cut_triangle_windows
#print axioms quartic_rh_of_archived_gaussian_log_cut_triangle_windows

end
end AlpogeSuperZeta
