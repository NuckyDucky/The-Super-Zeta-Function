import ArchivedGaussianNormPowerBound
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The ordered prime-prefix sum for the centered squared cutoff. -/

namespace AlpogeSuperZeta

open Filter Finset Topology

noncomputable section

/-- The drop in the squared residual weight from one integer address to the next. -/
def squaredRoundingWeightStep (x : ℝ) (n : ℕ) : ℝ :=
  squaredRoundingWeight x n - squaredRoundingWeight x (n + 1)

theorem squaredRoundingWeightStep_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ squaredRoundingWeightStep x n :=
  sub_nonneg.mpr (squaredRoundingWeight_antitone hx (Nat.le_succ n))

theorem squaredRoundingWeightStep_sum_le_half {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    (∑ n ∈ range N, squaredRoundingWeightStep x n) ≤ 1 / 2 := by
  have h (n : ℕ) : squaredRoundingWeightStep x n =
      -(squaredRoundingWeight x (n + 1) - squaredRoundingWeight x n) := by
    rw [squaredRoundingWeightStep, neg_sub]
  simp_rw [h, sum_neg_distrib, sum_range_sub (squaredRoundingWeight x), neg_sub]
  rw [show squaredRoundingWeight x 0 = 1 / 2 by simp [squaredRoundingWeight]]
  exact sub_le_self _ (squaredRoundingWeight_nonneg hx N)

theorem squaredRoundingWeightStep_le {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    squaredRoundingWeightStep x n ≤ 1 / (3 * x) := by
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn₁ : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have horder := div_le_div_of_nonneg_left hx.le hn₀ (Nat.cast_le.mpr (Nat.le_succ n))
  unfold squaredRoundingWeightStep
  rw [squaredRoundingWeight, if_neg hn.ne', squaredRoundingWeight, if_neg (Nat.succ_ne_zero n)]
  calc
    _ ≤ ((x / ((n + 1 : ℕ) : ℝ))⁻¹ - (x / (n : ℝ))⁻¹) / 3 :=
      squaredRoundingResidual_sub_le_reciprocal (div_pos hx hn₁) horder
    _ = _ := by push_cast; field_simp; ring

private theorem squaredRoundingWeight_eq_reciprocal {x : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (hn : 0 < n) (hxn : x ≤ (n : ℝ)) :
    squaredRoundingWeight x n = x / (3 * (n : ℝ)) := by
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [squaredRoundingWeight, if_neg hn.ne',
    squaredRoundingResidual_eq_div_three (div_nonneg hx hn₀.le) ((div_le_one hn₀).mpr hxn)]
  ring

theorem squaredRoundingWeightStep_eq_reciprocal {x : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (hn : 0 < n) (hxn : x ≤ (n : ℝ)) :
    squaredRoundingWeightStep x n = x / (3 * (n : ℝ) * ((n : ℝ) + 1)) := by
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn₁ : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold squaredRoundingWeightStep
  rw [squaredRoundingWeight_eq_reciprocal hx hn hxn,
    squaredRoundingWeight_eq_reciprocal hx (Nat.succ_pos n)
      (hxn.trans (Nat.cast_le.mpr (Nat.le_succ n)))]
  push_cast
  field_simp
  ring

theorem squaredRoundingWeightStep_mul_rpow_le {x θ : ℝ} (hx : 0 ≤ x) {n : ℕ}
    (hn : 0 < n) (hxn : x ≤ (n : ℝ)) (hθ₀ : 0 ≤ θ) (hθ₁ : θ < 1) :
    (n : ℝ) ^ θ * squaredRoundingWeightStep x n ≤ x / (3 * (1 - θ)) *
      ((n : ℝ) ^ (θ - 1) - ((n + 1 : ℕ) : ℝ) ^ (θ - 1)) := by
  let u : ℝ := n
  let v := u + 1
  have hu : 0 < u := Nat.cast_pos.mpr hn
  have hv : 0 < v := by dsimp [v]; positivity
  have hv₁ : 1 ≤ v := by dsimp [v]; linarith
  have hθ : 0 < 1 - θ := by linarith
  have hratio : 1 + -(1 / v) = u / v := by
    apply (eq_div_iff hv.ne').2
    rw [add_mul, neg_mul, div_mul_cancel₀ _ hv.ne', one_mul]
    dsimp [v]
    ring
  have hBernoulli := rpow_one_add_le_one_add_mul_self
    (show -1 ≤ -(1 / v) by linarith [(div_le_one hv).mpr hv₁])
    (show 0 ≤ 1 - θ by linarith) (show 1 - θ ≤ 1 by linarith)
  rw [hratio] at hBernoulli
  have hmul : u ^ (θ - 1) * (u / v) ^ (1 - θ) = v ^ (θ - 1) := by
    rw [Real.div_rpow hu.le hv.le, ← mul_div_assoc, ← Real.rpow_add hu,
      show θ - 1 + (1 - θ) = 0 by ring, Real.rpow_zero, one_div,
      ← Real.rpow_neg hv.le, neg_sub]
  have hd : (1 - θ) * (u ^ θ / (u * v)) ≤ u ^ (θ - 1) - v ^ (θ - 1) := by
    calc
      _ = u ^ (θ - 1) * ((1 - θ) / v) := by
        rw [Real.rpow_sub_one hu.ne']
        ring
      _ ≤ u ^ (θ - 1) * (1 - (u / v) ^ (1 - θ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.le _)
        have h := hBernoulli.trans_eq (show 1 + (1 - θ) * -(1 / v) = 1 - (1 - θ) / v by ring)
        linarith only [h]
      _ = _ := by rw [mul_sub, mul_one, hmul]
  rw [squaredRoundingWeightStep_eq_reciprocal hx hn hxn]
  push_cast
  change u ^ θ * (x / (3 * u * v)) ≤
    x / (3 * (1 - θ)) * (u ^ (θ - 1) - v ^ (θ - 1))
  calc
    _ = (x / (3 * (1 - θ))) * ((1 - θ) * (u ^ θ / (u * v))) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)

/-- Ordered convergence of the reciprocal prime sum at the archived center. -/
def ArchivedGaussianPrimeCenterLimit : Prop :=
  Tendsto (fun n : ℕ => ∑ p ∈ range (n + 1), archivedGaussianSignedPrimeWeight p / (p : ℝ))
    atTop (𝓝 archivedGaussianPrimeCenter)

/-- The exact centered squared cutoff is the ordered sum of signed prefixes with nonnegative
step weights. The reciprocal sum converges at the fixed center, and a sublinear envelope
on the prefixes makes the partial-summation endpoint tend to zero. -/
theorem archivedGaussianPrimeSquaredWindow_prefixLimit {x η B : ℝ} (hx : 1 ≤ x)
    (hη : η < 1) (hcenter : ArchivedGaussianPrimeCenterLimit)
    (hglobal : ∀ n : ℕ, |archivedGaussianSignedPrimePrefix n| ≤ B * (n : ℝ) ^ η) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N,
      archivedGaussianSignedPrimePrefix n * squaredRoundingWeightStep x n)
      atTop (𝓝 (archivedGaussianPrimeSquaredWindow x)) := by
  let b := archivedGaussianSignedPrimeWeight
  let w := squaredRoundingWeight x
  let P := archivedGaussianSignedPrimePrefix
  let c := archivedGaussianPrimeCenter
  let S (N : ℕ) := ∑ p ∈ range (N + 1), b p / (p : ℝ)
  let F (p : ℕ) := (-b p) * w p
  let M := ⌊x⌋₊
  let A := archivedGaussianPrimeSquaredWindow x
  have hx₀ : 0 < x := one_pos.trans_le hx
  have hstart := archivedGaussianPrimeSquaredWindow_eq_rounding hx
  change A = (∑ p ∈ range (M + 1), F p) + x / 3 * (S M - c) at hstart
  have htrunc (N : ℕ) (hN : M ≤ N) : (∑ p ∈ range (N + 1), F p) = A + x / 3 * (c - S N) := by
    have hMN : M + 1 ≤ N + 1 := Nat.succ_le_succ hN
    have htail : (∑ p ∈ range (N + 1), F p) - (∑ p ∈ range (M + 1), F p) =
        -(x / 3) * (S N - S M) := by
      dsimp [S]
      rw [sum_range_sub_sum_range hMN, sum_range_sub_sum_range hMN, mul_sum]
      apply sum_congr rfl
      intro p hp
      have hp₁ : M + 1 ≤ p := (mem_filter.mp hp).2
      have hp₀ : 0 < p := (Nat.succ_pos M).trans_le hp₁
      have hpX : x ≤ (p : ℝ) := (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast hp₁)
      dsimp only [F, w]
      rw [squaredRoundingWeight_eq_reciprocal hx₀.le hp₀ hpX]
      ring
    rw [hstart]
    linear_combination htail
  have hsum : Tendsto (fun N : ℕ => ∑ p ∈ range (N + 1), F p) atTop (𝓝 A) := by
    have hS : Tendsto S atTop (𝓝 c) := hcenter
    have hlim : Tendsto (fun N : ℕ => A + x / 3 * (c - S N)) atTop (𝓝 A) := by
      simpa only [sub_self, mul_zero, add_zero] using
        (tendsto_const_nhds (x := A)).add
          (((tendsto_const_nhds (x := c)).sub hS).const_mul (x / 3))
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop M] with N hN
    exact (htrunc N hN).symm
  have hend : Tendsto (fun n : ℕ => w n * P n) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (η - 1)) atTop (𝓝 0) := by
      rw [show η - 1 = -(1 - η) by ring]
      exact (tendsto_rpow_neg_atTop (sub_pos.mpr hη)).comp
        (show Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop from tendsto_natCast_atTop_atTop)
    have hscaled : Tendsto (fun n : ℕ => (x * B / 3) * (n : ℝ) ^ (η - 1)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hlim.const_mul (x * B / 3)
    apply squeeze_zero_norm' _ hscaled
    filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
    have hxn : x ≤ (n : ℝ) := (Nat.le_ceil x).trans (Nat.cast_le.mpr hn)
    have hn₀ : (0 : ℝ) < n := hx₀.trans_le hxn
    have hn' : 0 < n := Nat.cast_pos.mp hn₀
    have hw : 0 ≤ w n := squaredRoundingWeight_nonneg hx₀.le n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ w n * (B * (n : ℝ) ^ η) := mul_le_mul_of_nonneg_left (hglobal n) hw
      _ = _ := by
        dsimp only [w]
        rw [squaredRoundingWeight_eq_reciprocal hx₀.le hn' hxn, Real.rpow_sub_one hn₀.ne']
        ring
  have hparts (N : ℕ) :
      (∑ n ∈ range N, P n * squaredRoundingWeightStep x n) =
        (∑ p ∈ range (N + 1), F p) - w N * P N := by
    have h := sum_range_by_parts w (fun p : ℕ => -b p) (N + 1)
    change (∑ p ∈ range (N + 1), w p • -b p) =
      w (N + 1 - 1) • P N -
        ∑ i ∈ range (N + 1 - 1), (w (i + 1) - w i) • P i at h
    have hdiff : (∑ n ∈ range N, P n * squaredRoundingWeightStep x n) =
        -(∑ n ∈ range N, (w (n + 1) - w n) * P n) := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl fun n _ => by dsimp [squaredRoundingWeightStep, w]; ring
    simp only [Nat.add_sub_cancel, smul_eq_mul] at h
    have heq : (∑ p ∈ range (N + 1), w p * -b p) = ∑ p ∈ range (N + 1), F p :=
      sum_congr rfl fun p _ => mul_comm _ _
    rw [heq] at h
    rw [hdiff]
    linear_combination -h
  simpa only [sub_zero] using (hsum.sub hend).congr (fun N => (hparts N).symm)

#print axioms squaredRoundingResidual_sub_le_reciprocal
#print axioms squaredRoundingWeightStep_mul_rpow_le
#print axioms archivedGaussianPrimeSquaredWindow_prefixLimit

end

end AlpogeSuperZeta
