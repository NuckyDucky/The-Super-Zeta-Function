import GaussianLogCutTriangleWindow

/-! Recenter the omitted primes at a triangle width of order sqrt(x). -/

namespace AlpogeSuperZeta

open ArtinPrimitiveRootsConjecture FieldTarget Finset
open scoped Classical

noncomputable section

def archivedGaussianTriangleAtScale (x k : ℝ) : ℝ :=
  (∑ p ∈ range (⌊x⌋₊ + 1), archivedGaussianSignedPrimeWeight p *
    (if k ≤ (p : ℝ) then
      (2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k p : ℝ)
    else x / (3 * (p : ℝ)))) - x / 3 * archivedGaussianPrimeCenter

theorem archivedGaussianTriangleAtScale_eq_recentered (x k : ℝ) :
    archivedGaussianTriangleAtScale x k =
      (∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => k ≤ (p : ℝ)),
        archivedGaussianSignedPrimeWeight p *
          ((2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k p : ℝ))) -
      x / 3 * (archivedGaussianPrimeCenter -
        ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p : ℕ => (p : ℝ) < k),
          archivedGaussianSignedPrimeWeight p / (p : ℝ)) := by
  let b := archivedGaussianSignedPrimeWeight
  let P := range (⌊x⌋₊ + 1)
  let V (p : ℕ) := (2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k p : ℝ)
  have hCenter :
      (∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < k), b p * (x / (3 * (p : ℝ)))) =
        x / 3 * (∑ p ∈ P.filter (fun p : ℕ => (p : ℝ) < k), b p / (p : ℝ)) := by
    rw [mul_sum]
    exact sum_congr rfl fun p _ => by ring
  change ((∑ p ∈ P, b p * (if k ≤ (p : ℝ) then V p else x / (3 * (p : ℝ)))) -
      x / 3 * archivedGaussianPrimeCenter) = _
  simp_rw [mul_ite, sum_ite, not_le]
  rw [hCenter]
  ring

theorem frobeniusTriangleDivisibility_error_le_scale {x k : ℝ}
    (hx : 2 ≤ x) (hk : 1 ≤ k) {p : ℕ} (hp : 0 < p) :
    let V := (2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k p : ℝ)
    let S := ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * p)
    0 ≤ V - S ∧ V - S ≤ (5 * k) / (p : ℝ) := by
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := one_pos.trans_le hx₁
  have hk₀ := one_pos.trans_le hk
  have hp₀ : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  let B := (2 * k / x ^ 2) * (x + x / k + 1)
  have hB₀ : 0 ≤ B := by dsimp [B]; positivity
  have hB : B * x ≤ 5 * k := by
    have hEq : B * x = 2 * k + 2 + 2 * k / x := by dsimp [B]; field_simp
    have hDiv : 2 * k / x ≤ k := (div_le_iff₀ hx₀).mpr
      (by nlinarith [mul_nonneg hk₀.le (sub_nonneg.mpr hx)])
    linarith
  have hpDiv := div_pos hx₀ hp₀
  have hN : 1 ≤ ⌈x / (p : ℝ)⌉₊ := Nat.lt_ceil.mpr (by simpa using hpDiv)
  have hCount : ((⌈x / (p : ℝ)⌉₊ - 1 : ℕ) : ℝ) ≤ x / (p : ℝ) := by
    rw [Nat.cast_sub hN, Nat.cast_one]
    linarith [Nat.ceil_lt_add_one hpDiv.le]
  have hD := frobeniusTriangleDivisibility_error hx₁ hk₀ hp
  exact ⟨hD.1, hD.2.trans (calc
    _ ≤ B * (x / (p : ℝ)) := mul_le_mul_of_nonneg_left hCount hB₀
    _ = B * x / (p : ℝ) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hB hp₀.le)⟩

theorem archivedGaussianTriangleAtScale_error {x k θ : ℝ}
    (hx : 2 ≤ x) (hk : 1 ≤ k) (hkx : k ≤ 2 * x ^ (1 / 2 : ℝ)) (hθ : 1 / 2 < θ) :
    |archivedGaussianTriangleAtScale x k - archivedGaussianPrimeSquaredWindow x| ≤
      (10 * ∑' p : ℕ,
        |archivedGaussianSignedPrimeWeight p| / ((max 1 p : ℕ) : ℝ) ^ (1 + (θ - 1 / 2))) * x ^ θ := by
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ := one_pos.trans_le hx₁
  have hk₀ := one_pos.trans_le hk
  let ε := θ - 1 / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  let b := archivedGaussianSignedPrimeWeight
  let W (p : ℕ) := |b p| / ((max 1 p : ℕ) : ℝ) ^ (1 + ε)
  have hW : Summable W := archivedGaussianSignedPrimeWeight_summable (by linarith)
  have hW₀ (p : ℕ) : 0 ≤ W p := by dsimp [W]; positivity
  let P := range (⌊x⌋₊ + 1)
  let V (p : ℕ) := (2 * k / x ^ 2) * (frobeniusTriangleDivisibility x k p : ℝ)
  let S (p : ℕ) := ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * p)
  let T (p : ℕ) := if k ≤ (p : ℝ) then V p else x / (3 * (p : ℝ))
  have hScale : k * x ^ ε ≤ 2 * x ^ θ := by
    calc
      _ ≤ (2 * x ^ (1 / 2 : ℝ)) * x ^ ε := mul_le_mul_of_nonneg_right hkx (by positivity)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add hx₀]
        congr 2
        dsimp [ε]
        ring
  have hTerm (p : ℕ) (hpP : p ∈ P) : |b p * (T p - S p)| ≤ (10 * x ^ θ) * W p := by
    by_cases hp : p.Prime
    · have hp₀ : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
      have hpX : (p : ℝ) ≤ x := (Nat.le_floor_iff hx₀.le).mp
        (Nat.le_of_lt_succ (mem_range.mp hpP))
      have hFactor : |b p| / (p : ℝ) = (p : ℝ) ^ ε * W p := by
        dsimp [W]
        rw [max_eq_right hp.one_lt.le, Real.rpow_add hp₀, Real.rpow_one]
        field_simp
      have hWeight : |b p| / (p : ℝ) ≤ x ^ ε * W p := by
        rw [hFactor]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hp₀.le hpX hε.le) (hW₀ p)
      rw [abs_mul]
      by_cases hKeep : k ≤ (p : ℝ)
      · have hD := frobeniusTriangleDivisibility_error_le_scale hx hk hp.pos
        change 0 ≤ V p - S p ∧ V p - S p ≤ (5 * k) / (p : ℝ) at hD
        rw [show T p = V p by simp [T, hKeep], abs_of_nonneg hD.1]
        calc
          _ ≤ |b p| * ((5 * k) / (p : ℝ)) := mul_le_mul_of_nonneg_left hD.2 (abs_nonneg _)
          _ = (5 * k) * (|b p| / (p : ℝ)) := by ring
          _ ≤ (5 * k) * (x ^ ε * W p) := mul_le_mul_of_nonneg_left hWeight (by positivity)
          _ = 5 * (k * x ^ ε) * W p := by ring
          _ ≤ (10 * x ^ θ) * W p := by
            have hScaled := mul_le_mul_of_nonneg_right hScale (hW₀ p)
            linarith
      · have hR := squaredRampMultiples_rounding hx₀ hp.pos
        change 0 ≤ x / (3 * (p : ℝ)) - S p ∧ x / (3 * (p : ℝ)) - S p ≤ 1 at hR
        rw [show T p = x / (3 * (p : ℝ)) by simp [T, hKeep], abs_of_nonneg hR.1]
        calc
          _ ≤ |b p| := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hR.2 (abs_nonneg (b p))
          _ = (p : ℝ) * (|b p| / (p : ℝ)) := by field_simp
          _ ≤ k * (x ^ ε * W p) :=
            mul_le_mul (le_of_not_ge hKeep) hWeight (div_nonneg (abs_nonneg _) hp₀.le) hk₀.le
          _ = (k * x ^ ε) * W p := by ring
          _ ≤ (2 * x ^ θ) * W p := mul_le_mul_of_nonneg_right hScale (hW₀ p)
          _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [Real.rpow_nonneg hx₀.le θ]) (hW₀ p)
    · have hz : b p = 0 := by simp [b, archivedGaussianSignedPrimeWeight, hp]
      simpa only [hz, zero_mul, abs_zero] using mul_nonneg (by positivity : 0 ≤ 10 * x ^ θ) (hW₀ p)
  rw [archivedGaussianPrimeSquaredWindow_eq_sum hx₁, archivedGaussianTriangleAtScale]
  have he (a b c : ℝ) : (a - c) - (b - c) = a - b := by ring
  rw [he]
  change |(∑ p ∈ P, b p * T p) - (∑ p ∈ P, b p * S p)| ≤ (10 * ∑' p, W p) * x ^ θ
  rw [← sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ ∑ p ∈ P, |b p * (T p - S p)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ P, (10 * x ^ θ) * W p := sum_le_sum hTerm
    _ = (10 * x ^ θ) * ∑ p ∈ P, W p := (mul_sum _ _ _).symm
    _ ≤ (10 * x ^ θ) * ∑' p, W p :=
      mul_le_mul_of_nonneg_left (hW.sum_le_tsum _ (fun p _ => hW₀ p)) (by positivity)
    _ = _ := by ring

def gaussianSqrtTriangleScale (x : ℝ) : ℝ := 2 * x ^ (1 / 2 : ℝ)

def archivedGaussianSqrtTriangleWindow (x : ℝ) : ℝ :=
  archivedGaussianTriangleAtScale x (gaussianSqrtTriangleScale x)

theorem archivedGaussianSqrtTriangleWindowBound_iff :
    GaussianCutoffWindowBound archivedGaussianSqrtTriangleWindow ↔
      GaussianCutoffWindowBound archivedGaussianPrimeSquaredWindow := by
  apply gaussianCutoffWindowBound_iff_of_error (X₀ := 2)
  intro θ hθ _
  let W (p : ℕ) := |archivedGaussianSignedPrimeWeight p| /
    ((max 1 p : ℕ) : ℝ) ^ (1 + (θ - 1 / 2))
  refine ⟨10 * ∑' p, W p, mul_nonneg (by norm_num) (tsum_nonneg (by intro p; dsimp [W]; positivity)),
    fun x hx => ?_⟩
  have hx₁ : 1 ≤ x := by linarith
  have hPow := Real.one_le_rpow hx₁ (by norm_num : 0 ≤ (1 / 2 : ℝ))
  have hk : 1 ≤ gaussianSqrtTriangleScale x := by dsimp [gaussianSqrtTriangleScale]; linarith
  exact archivedGaussianTriangleAtScale_error hx hk le_rfl hθ

theorem quartic_rh_of_archived_gaussian_sqrt_triangle_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianSqrtTriangleWindow) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_prime_squared_windows hD hpos
    (archivedGaussianSqrtTriangleWindowBound_iff.mp hcut)

#print axioms archivedGaussianTriangleAtScale_eq_recentered
#print axioms frobeniusTriangleDivisibility_error_le_scale
#print axioms archivedGaussianTriangleAtScale_error
#print axioms archivedGaussianSqrtTriangleWindowBound_iff
#check quartic_rh_of_archived_gaussian_sqrt_triangle_windows
#print axioms quartic_rh_of_archived_gaussian_sqrt_triangle_windows

end
end AlpogeSuperZeta
