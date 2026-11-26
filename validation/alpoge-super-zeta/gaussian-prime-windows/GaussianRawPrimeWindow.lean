import GaussianCenteredHalfWindowShift
import GaussianRawWindowCriterion

/-! The original determinant window can be evaluated using the finite
degree-one prime readings at their unshifted addresses, with an explicit
linear term and an error of order `x ^ θ` for each `θ > 1/2`. -/

namespace AlpogeSuperZeta

open ArithmeticFunction ArtinPrimitiveRootsConjecture Finset QuarticModel
open scoped Classical

noncomputable section

private def primeHalfShiftSlope : ℝ :=
  ∑' n : ℕ, archivedInertIndexWeight n 1 / (n : ℝ) / ((n : ℝ) + 1)

private def primeHalfTailSlope (f k : ℕ) : ℝ :=
  ∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val f / (archivedInertTailIndex f k pk : ℝ)

private theorem primeHalfRamp_one :
    archivedGaussianPrimitiveIndexRamp 1 =
      -((logDeriv archivedGaussianFactor 1).re + gaussianHigherPrimeLinearCoefficient) +
        2 * (primeHalfShiftSlope - primeHalfTailSlope 1 1 - primeHalfTailSlope 2 0) := by
  have hz (n : ℕ) : indexRampWeight 1 n = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num [indexRampWeight]
    · exact IndexedCutoff.ramp.weight_zero_of_le hn (by exact_mod_cast hn)
  unfold archivedGaussianPrimitiveIndexRamp
  change 2 * ((∑ n ∈ range (⌊(1 : ℝ)⌋₊ + 1),
    archivedInertIndexWeight n 1 * indexRampWeight 1 (n + 1)) +
    (∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 1 *
      indexRampWeight 1 (archivedInertTailIndex 1 1 pk)) +
    (∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 2 *
      indexRampWeight 1 (archivedInertTailIndex 2 0 pk))) -
    (∑ n ∈ range (⌊(1 : ℝ)⌋₊ + 1), archivedIndexBaseWeight n * indexRampWeight 1 n) -
    _ * 1 + 2 * 1 * ((∑' n : ℕ, archivedInertIndexWeight n 1 / (n : ℝ) / ((n + 1 : ℕ) : ℝ)) -
      primeHalfTailSlope 1 1 - primeHalfTailSlope 2 0) = _
  simp only [hz, mul_zero, sum_const_zero, tsum_zero, Nat.cast_succ, primeHalfShiftSlope]
  ring

private theorem divisorWindowFinite_hasSum (b : ℕ → ℝ) (N : ℕ → ℕ) (hN : ∀ n, n ≤ N n)
    {x : ℝ} (hx : 1 ≤ x) :
    HasSum (fun n => b n * divisorWindowMultiplicity x (N n))
      (∑ n ∈ range (⌊x⌋₊ + 1), b n * divisorWindowMultiplicity x (N n)) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have hx₀ : 0 ≤ x := zero_le_one.trans hx
  have hlt : x < (n : ℝ) := lt_of_not_ge fun h =>
    hn (mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff hx₀).mpr h)))
  have hN' : x ≤ (N n : ℝ) := hlt.le.trans (by exact_mod_cast hN n)
  have hp : 0 < N n := Nat.cast_pos.mp (zero_lt_one.trans_le (hx.trans hN'))
  rw [divisorWindowMultiplicity_zero_of_le hx₀ hp hN', mul_zero]

private theorem archivedRawHalfWindow_parts {x : ℝ} (hx : 1 ≤ x)
    (ht : ∀ f k : ℕ, f + k = 2 → Summable (fun pk : Nat.Primes × ℕ =>
      archivedInertIndexWeight pk.1.val f * divisorWindowMultiplicity x (archivedInertTailIndex f k pk))) :
    archivedGaussianRawWindow x =
      archivedGaussianPrimitiveIndexRamp 1 * divisorWindowMultiplicity x 1 +
      2 * (∑ n ∈ range (⌊x⌋₊ + 1), archivedInertIndexWeight n 1 *
        divisorWindowMultiplicity x (n + 1)) +
      2 * (∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 1 *
        divisorWindowMultiplicity x (archivedInertTailIndex 1 1 pk)) +
      2 * (∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 2 *
        divisorWindowMultiplicity x (archivedInertTailIndex 2 0 pk)) -
      (∑ n ∈ range (⌊x⌋₊ + 1), archivedIndexBaseWeight n * divisorWindowMultiplicity x n) := by
  let F (i : GaussianIndexFamily) := gaussianIndexCoefficient i * divisorWindowMultiplicity x (gaussianIndexAddress i)
  have h0 : HasSum (F ∘ Sum.inl) (archivedGaussianPrimitiveIndexRamp 1 * divisorWindowMultiplicity x 1) := by
    change HasSum (fun _ : Unit => archivedGaussianPrimitiveIndexRamp 1 * divisorWindowMultiplicity x 1) _
    simp
  have h1 : HasSum (fun n => F (.inr (.inl n)))
      (2 * ∑ n ∈ range (⌊x⌋₊ + 1), archivedInertIndexWeight n 1 *
        divisorWindowMultiplicity x (n + 1)) := by
    simpa only [F, gaussianIndexCoefficient, gaussianIndexAddress, mul_assoc] using
      (divisorWindowFinite_hasSum (fun n => archivedInertIndexWeight n 1) (· + 1) Nat.le_succ hx).mul_left (2 : ℝ)
  have h2 : HasSum (fun pk => F (.inr (.inr (.inl pk))))
      (2 * ∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 1 *
        divisorWindowMultiplicity x (archivedInertTailIndex 1 1 pk)) := by
    simpa only [F, gaussianIndexCoefficient, gaussianIndexAddress, mul_assoc] using (ht 1 1 rfl).hasSum.mul_left (2 : ℝ)
  have h3 : HasSum (fun pk => F (.inr (.inr (.inr (.inl pk)))))
      (2 * ∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val 2 *
        divisorWindowMultiplicity x (archivedInertTailIndex 2 0 pk)) := by
    simpa only [F, gaussianIndexCoefficient, gaussianIndexAddress, mul_assoc] using (ht 2 0 rfl).hasSum.mul_left (2 : ℝ)
  have hb (n : ℕ) : F (.inr (.inr (.inr (.inr n)))) =
      -(archivedIndexBaseWeight n * divisorWindowMultiplicity x n) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num [F, gaussianIndexCoefficient, archivedIndexBaseWeight]
    · simp [F, gaussianIndexCoefficient, gaussianIndexAddress, max_eq_right (show 1 ≤ n from hn)]
  have h4 : HasSum (fun n => F (.inr (.inr (.inr (.inr n)))))
      (-(∑ n ∈ range (⌊x⌋₊ + 1), archivedIndexBaseWeight n * divisorWindowMultiplicity x n)) := by
    simpa only [hb, id_eq] using (divisorWindowFinite_hasSum archivedIndexBaseWeight id (fun _ => le_rfl) hx).neg
  have h34 := HasSum.sum (f := fun i => F (.inr (.inr (.inr i)))) h3 h4
  have h234 := HasSum.sum (f := fun i => F (.inr (.inr i))) h2 h34
  have h1234 := HasSum.sum (f := fun i => F (.inr i)) h1 h234
  rw [archivedGaussianRawWindow_by_multiplicity hx]
  change (∑' i, F i) = _
  rw [(HasSum.sum (f := F) h0 h1234).tsum_eq]
  ring

/-- The finite prime half-window, with all counts at the addresses `p`. -/
def archivedGaussianPrimeHalfWindow (x : ℝ) : ℝ :=
  -(∑ n ∈ range (⌊x⌋₊ + 1), (vonMangoldt n * (if n.Prime then archivedGaussianPrimeWeight n else 0)) *
    divisorWindowMultiplicity x n) -
  (x / 2) * ((logDeriv archivedGaussianFactor 1).re + gaussianHigherPrimeLinearCoefficient)

set_option maxHeartbeats 700000 in
theorem archivedGaussianPrimeHalfWindow_error {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) :
    ∃ D ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ),
      |archivedGaussianRawWindow x - archivedGaussianPrimeHalfWindow x| ≤ D * x ^ θ := by
  let b (n : ℕ) := archivedInertIndexWeight n 1
  have hb₀ : b 0 = 0 := archivedInertIndexWeight_eq_zero_of_not_prime _ Nat.not_prime_zero
  have hb (n : ℕ) : 0 ≤ b n := archivedInertIndexWeight_nonneg _ _
  have hlog (n : ℕ) : b n ≤ 2 * Real.log n := by
    by_cases hp : n.Prime
    · simpa only [b, Nat.cast_one, one_mul] using archivedInertIndexWeight_le ⟨n, hp⟩ 1
    · rw [show b n = 0 from archivedInertIndexWeight_eq_zero_of_not_prime _ hp]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast hn))
  have hs : Summable (fun n => b n / (n : ℝ) ^ (2 * θ)) := by
    have h := archivedInertIndexWeight_one_summable (θ := 2 * θ - 1) (by linarith)
    rwa [show 1 + (2 * θ - 1) = 2 * θ by ring] at h
  obtain ⟨_, D, hD, hShift⟩ :=
    divisorWindow_shift_centered_error hθ hθ₁ b hb₀ hb (by norm_num : (0 : ℝ) ≤ 2) hlog hs
  let B (f k : ℕ) := ∑' pk : Nat.Primes × ℕ,
    archivedInertIndexWeight pk.1.val f / (archivedInertTailIndex f k pk : ℝ) ^ θ
  have hB (f k : ℕ) : 0 ≤ B f k := tsum_nonneg fun _ =>
    div_nonneg (archivedInertIndexWeight_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hB₁ := hB 1 1
  have hB₂ := hB 2 0
  let L := archivedGaussianPrimitiveIndexRamp 1
  refine ⟨|L| + 2 * D + 2 * B 1 1 + 2 * B 2 0, by positivity, fun x hx => ?_⟩
  have hx₀ := zero_le_one.trans hx
  have hθ₀ : 0 ≤ θ := by linarith
  let M := divisorWindowMultiplicity x
  let R := range (⌊x⌋₊ + 1)
  let T (f k : ℕ) :=
    ∑' pk : Nat.Primes × ℕ, archivedInertIndexWeight pk.1.val f * M (archivedInertTailIndex f k pk)
  have hTail (f k : ℕ) (hfk : f + k = 2) :
      Summable (fun pk : Nat.Primes × ℕ => archivedInertIndexWeight pk.1.val f * M (archivedInertTailIndex f k pk)) ∧
      |T f k - (x / 2) * primeHalfTailSlope f k| ≤ x ^ θ * B f k := by
    have h := divisorWindow_sparse_approximation (fun pk : Nat.Primes × ℕ => archivedInertIndexWeight pk.1.val f)
      (archivedInertTailIndex f k) (archivedInertTailIndex_pos f k) hθ₀ hθ₁.le (θ := θ) (by
        simpa only [abs_of_nonneg (archivedInertIndexWeight_nonneg _ _)] using
          archivedInertTail_summable f k hfk hθ) (zero_lt_one.trans_le hx)
    exact ⟨h.2.1, by simpa only [T, M, primeHalfTailSlope, B, abs_of_nonneg (archivedInertIndexWeight_nonneg _ _)] using h.2.2⟩
  let S := (∑ n ∈ R, b n * (M n - M (n + 1))) - (x / 2) * primeHalfShiftSlope
  have hS : |S| ≤ D * x ^ θ := hShift x hx
  have hL : |L * (M 1 - x / 2)| ≤ |L| * x ^ θ := by
    have hr := divisorWindowMultiplicity_rounding (d := 1) (by decide) hx₀
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      ((by simpa only [Nat.cast_one, mul_one, M] using hr.le : |M 1 - x / 2| ≤ 1).trans
        (Real.one_le_rpow hx hθ₀)) (abs_nonneg _)
  have hBalance :
      -(∑ n ∈ R, (vonMangoldt n * (if n.Prime then archivedGaussianPrimeWeight n else 0)) * M n) =
      2 * (∑ n ∈ R, b n * M n) - (∑ n ∈ R, archivedIndexBaseWeight n * M n) := by
    calc
      _ = ∑ n ∈ R, (2 * b n - archivedIndexBaseWeight n) * M n := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun n _ => by simp only [b, archivedIndexWeight_balance, neg_mul]
      _ = _ := by simp only [sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum]
  have hE : archivedGaussianRawWindow x - archivedGaussianPrimeHalfWindow x =
      L * (M 1 - x / 2) - 2 * S +
        2 * (T 1 1 - (x / 2) * primeHalfTailSlope 1 1) +
        2 * (T 2 0 - (x / 2) * primeHalfTailSlope 2 0) := by
    rw [archivedRawHalfWindow_parts hx (fun f k h => (hTail f k h).1), archivedGaussianPrimeHalfWindow]
    change L * M 1 + 2 * (∑ n ∈ R, b n * M (n + 1)) + 2 * T 1 1 + 2 * T 2 0 -
      (∑ n ∈ R, archivedIndexBaseWeight n * M n) -
      (-(∑ n ∈ R, (vonMangoldt n * (if n.Prime then archivedGaussianPrimeWeight n else 0)) * M n) -
        (x / 2) * ((logDeriv archivedGaussianFactor 1).re + gaussianHigherPrimeLinearCoefficient)) = _
    rw [hBalance]
    simp only [S, mul_sub, sum_sub_distrib]
    rw [show L = _ from primeHalfRamp_one]
    ring
  have hT₁ := (hTail 1 1 rfl).2
  have hT₂ := (hTail 2 0 rfl).2
  rw [hE, abs_le]
  constructor <;> linarith only [(abs_le.mp hL).1, (abs_le.mp hL).2,
    (abs_le.mp hS).1, (abs_le.mp hS).2, (abs_le.mp hT₁).1, (abs_le.mp hT₁).2,
    (abs_le.mp hT₂).1, (abs_le.mp hT₂).2]

def ArchivedGaussianPrimeHalfWindowBound : Prop :=
  ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ Y₀ : ℝ, ∃ Y ≥ Y₀,
      ∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), archivedGaussianPrimeHalfWindow y ≤ C * y ^ θ

theorem archivedGaussianRawWindowBound_iff_prime_half_window :
    ArchivedGaussianRawWindowBound ↔ ArchivedGaussianPrimeHalfWindowBound := by
  constructor <;> intro h θ hθ hθ₁
  all_goals
    obtain ⟨D, hD, hE⟩ := archivedGaussianPrimeHalfWindow_error hθ hθ₁
    obtain ⟨δ, hδ, C, hC, hW⟩ := h θ hθ hθ₁
    refine ⟨δ, hδ, C + D, add_nonneg hC hD, fun Y₀ => ?_⟩
    obtain ⟨Y, hY, hb⟩ := hW (max Y₀ 1)
    refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
    have h₁ : 1 ≤ y := (le_max_right Y₀ 1).trans (hY.trans hy.1)
    have hL := abs_le.mp (hE y h₁)
  · linarith only [hb y hy, hL.1]
  · linarith only [hb y hy, hL.2]

theorem quartic_rh_of_archived_gaussian_prime_half_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : ArchivedGaussianPrimeHalfWindowBound) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_raw_windows hD hpos (archivedGaussianRawWindowBound_iff_prime_half_window.mpr hcut)

#print axioms archivedGaussianPrimeHalfWindow_error
#print axioms archivedGaussianRawWindowBound_iff_prime_half_window
#print ArchivedGaussianPrimeHalfWindowBound
#check quartic_rh_of_archived_gaussian_prime_half_windows
#print axioms quartic_rh_of_archived_gaussian_prime_half_windows

end
end AlpogeSuperZeta
