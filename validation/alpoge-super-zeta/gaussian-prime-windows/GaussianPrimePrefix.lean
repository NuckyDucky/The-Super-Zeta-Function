import GaussianRawPrimeWindow

/-! Recover the full signed prime prefix and its error from the
checked half-window comparison. The cutoff is strict at integer addresses. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Finset QuarticModel
open scoped Classical

noncomputable section

/-- Number of positive multiples of d strictly below x, for positive d. -/
def divisorPrefixMultiplicity (x : ℝ) (d : ℕ) : ℝ :=
  ↑(⌈x / (d : ℝ)⌉₊ - 1 : ℕ)

theorem divisorPrefixMultiplicity_eq_zero {x : ℝ} {d : ℕ} (hx : x ≤ d) :
    divisorPrefixMultiplicity x d = 0 := by
  have h : ⌈x / (d : ℝ)⌉₊ ≤ 1 := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_one]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · exact (div_le_one (Nat.cast_pos.mpr hd)).mpr hx
  rw [divisorPrefixMultiplicity, Nat.sub_eq_zero_of_le h, Nat.cast_zero]

theorem divisorPrefixMultiplicity_sub_half {x : ℝ} (hx : 0 < x) (d : ℕ) :
    divisorPrefixMultiplicity x d - divisorPrefixMultiplicity (x / 2) d =
      divisorWindowMultiplicity x d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [divisorPrefixMultiplicity, divisorWindowMultiplicity]
  have hp : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h₁ : 1 ≤ ⌈x / (d : ℝ)⌉₊ := Nat.lt_ceil.mpr (by simpa using div_pos hx hp)
  have h₂ : 1 ≤ ⌈(x / 2) / (d : ℝ)⌉₊ :=
    Nat.lt_ceil.mpr (by simpa using div_pos (half_pos hx) hp)
  rw [divisorPrefixMultiplicity, divisorPrefixMultiplicity, Nat.cast_sub h₁, Nat.cast_sub h₂,
    Nat.cast_one, divisorWindowMultiplicity]
  rw [show (x / 2) / (d : ℝ) = x / (2 * (d : ℝ)) by ring]
  ring

theorem indexedPrefix_summable_at {ι : Type*} (b : ι → ℝ) (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) {a : ℝ} (ha : 0 ≤ a)
    (hb : Summable fun i => |b i| / (N i : ℝ) ^ a) (x : ℝ) :
    Summable (fun i => b i * IndexedCutoff.prefix.weight x (N i)) := by
  by_cases hx : 1 ≤ x
  · exact indexedCutoffSum_summable_at .prefix b N hN ha hx hb
  · have hz (i : ι) : b i * IndexedCutoff.prefix.weight x (N i) = 0 := by
      have hn : (1 : ℝ) ≤ N i := by exact_mod_cast hN i
      rw [IndexedCutoff.prefix.weight_zero_of_le (hN i) ((le_of_not_ge hx).trans hn), mul_zero]
    simpa only [hz] using (summable_zero : Summable fun _ : ι => (0 : ℝ))

theorem archivedGaussianRawWindow_eq_prefix_sub (x : ℝ) :
    archivedGaussianRawWindow x = archivedGaussianRawPrefix x - archivedGaussianRawPrefix (x / 2) := by
  let b (p : GaussianIndexFamily × ℕ) := gaussianIndexCoefficient p.1
  let N := divisorWindowIndex gaussianIndexAddress
  have hb := divisorWindow_summable gaussianIndexCoefficient gaussianIndexAddress
    (a := 2) (by norm_num) (gaussianIndexFamily_summable (by norm_num))
  have hsum t := indexedPrefix_summable_at b N (divisorWindowIndex_pos gaussianIndexAddress_pos)
    (by norm_num : 0 ≤ (2 : ℝ)) hb t
  change (∑' p, b p * IndexedCutoff.window.weight x (N p)) =
    (∑' p, b p * IndexedCutoff.prefix.weight x (N p)) -
      (∑' p, b p * IndexedCutoff.prefix.weight (x / 2) (N p))
  rw [← (hsum x).tsum_sub (hsum (x / 2))]
  apply tsum_congr
  intro p
  rw [indexedWindow_weight, mul_sub]
  have he : (↑(2 * N p) : ℝ) < x ↔ ((N p : ℕ) : ℝ) < x / 2 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, lt_div_iff₀ (by norm_num : (0 : ℝ) < 2), mul_comm (2 : ℝ)]
  simp only [IndexedCutoff.weight, he]

def archivedGaussianSignedPrimeWeight (n : ℕ) : ℝ :=
  -(vonMangoldt n * (if n.Prime then archivedGaussianPrimeWeight n else 0))

def archivedGaussianPrimeCenter : ℝ :=
  (logDeriv archivedGaussianFactor 1).re + gaussianHigherPrimeLinearCoefficient

def archivedGaussianPrimePrefix (x : ℝ) : ℝ :=
  (∑ n ∈ range (⌊x⌋₊ + 1), archivedGaussianSignedPrimeWeight n * divisorPrefixMultiplicity x n) -
    x * archivedGaussianPrimeCenter

theorem archivedGaussianPrimeHalfWindow_eq_prefix_sub {x : ℝ} (hx : 0 < x) :
    archivedGaussianPrimeHalfWindow x =
      archivedGaussianPrimePrefix x - archivedGaussianPrimePrefix (x / 2) := by
  have hhalf : 0 ≤ x / 2 := (half_pos hx).le
  have hsub : range (⌊x / 2⌋₊ + 1) ⊆ range (⌊x⌋₊ + 1) :=
    range_mono (Nat.succ_le_succ (Nat.floor_le_floor (by linarith)))
  have hsum : (∑ n ∈ range (⌊x / 2⌋₊ + 1),
      archivedGaussianSignedPrimeWeight n * divisorPrefixMultiplicity (x / 2) n) =
      ∑ n ∈ range (⌊x⌋₊ + 1),
        archivedGaussianSignedPrimeWeight n * divisorPrefixMultiplicity (x / 2) n := by
    apply sum_subset hsub
    intro n _ hn
    have hn' : ⌊x / 2⌋₊ < n :=
      lt_of_not_ge fun h => hn (mem_range.mpr (Nat.lt_succ_of_le h))
    rw [divisorPrefixMultiplicity_eq_zero ((Nat.floor_lt hhalf).mp hn').le, mul_zero]
  unfold archivedGaussianPrimePrefix
  rw [hsum]
  have hrw : ∀ a b c : ℝ, (a - x * c) - (b - x / 2 * c) =
      (a - b) - (x / 2) * c := fun a b c => by ring
  rw [hrw, ← sum_sub_distrib]
  simp_rw [← mul_sub, divisorPrefixMultiplicity_sub_half hx]
  simp only [archivedGaussianPrimeHalfWindow, archivedGaussianPrimeCenter,
    archivedGaussianSignedPrimeWeight, neg_mul, sum_neg_distrib]

private theorem archivedGaussianRawPrefix_eq_zero {x : ℝ} (hx : x ≤ 1) :
    archivedGaussianRawPrefix x = 0 := by
  unfold archivedGaussianRawPrefix indexedCutoffSum
  have hz (p : GaussianIndexFamily × ℕ) : gaussianIndexCoefficient p.1 *
      IndexedCutoff.prefix.weight x (divisorWindowIndex gaussianIndexAddress p) = 0 := by
    have hp := divisorWindowIndex_pos gaussianIndexAddress_pos p
    have hp' : (1 : ℝ) ≤ divisorWindowIndex gaussianIndexAddress p := by exact_mod_cast hp
    rw [IndexedCutoff.prefix.weight_zero_of_le hp (hx.trans hp'), mul_zero]
  simp only [hz, tsum_zero]

private theorem archivedGaussianPrimePrefix_eq_linear {x : ℝ} (hx : x ≤ 1) :
    archivedGaussianPrimePrefix x = -(x * archivedGaussianPrimeCenter) := by
  unfold archivedGaussianPrimePrefix
  have hz (n : ℕ) : archivedGaussianSignedPrimeWeight n * divisorPrefixMultiplicity x n = 0 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [archivedGaussianSignedPrimeWeight]
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [divisorPrefixMultiplicity_eq_zero (hx.trans hn'), mul_zero]
  simp [hz]

private theorem dyadic_error_bound (F : ℝ → ℝ) {θ B D : ℝ} (hθ : 0 < θ)
    (hB : 0 ≤ B)
    (hbase : ∀ x, 0 < x → x ≤ 1 → |F x| ≤ B * x ^ θ)
    (hstep : ∀ x, 1 ≤ x → |F x - F (x / 2)| ≤ D * x ^ θ) :
    ∃ C ≥ (0 : ℝ), ∀ x, 0 < x → |F x| ≤ C * x ^ θ := by
  let r : ℝ := (2 : ℝ) ^ (-θ)
  have hr : r < 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ) < 2) (neg_lt_zero.mpr hθ)
  let C := max B (D / (1 - r))
  have hBC : B ≤ C := le_max_left _ _
  have hC : 0 ≤ C := hB.trans hBC
  have hD : D + C * r ≤ C := by
    have h := (div_le_iff₀ (sub_pos.mpr hr)).mp (le_max_right B (D / (1 - r)))
    change D ≤ C * (1 - r) at h
    linarith
  have hpow {x : ℝ} (hx : 0 < x) : (x / 2) ^ θ = x ^ θ * r := by
    dsimp [r]
    rw [Real.div_rpow hx.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hforall (n : ℕ) : ∀ x, 0 < x → x ≤ (2 : ℝ) ^ n → |F x| ≤ C * x ^ θ := by
    induction n with
    | zero =>
      intro x hp hx
      exact (hbase x hp (by simpa only [pow_zero] using hx)).trans
        (mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg hp.le _))
    | succ n ih =>
      intro x hp hx
      by_cases hsmall : x ≤ 1
      · exact (hbase x hp hsmall).trans (mul_le_mul_of_nonneg_right hBC (Real.rpow_nonneg hp.le _))
      have hhalf : x / 2 ≤ (2 : ℝ) ^ n := by rw [pow_succ] at hx; linarith
      calc
        _ = |(F x - F (x / 2)) + F (x / 2)| := by rw [sub_add_cancel]
        _ ≤ |F x - F (x / 2)| + |F (x / 2)| := abs_add_le _ _
        _ ≤ D * x ^ θ + C * (x / 2) ^ θ :=
          add_le_add (hstep x (le_of_not_ge hsmall)) (ih _ (half_pos hp) hhalf)
        _ = (D + C * r) * x ^ θ := by rw [hpow hp]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hD (Real.rpow_nonneg hp.le _)
  refine ⟨C, hC, fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt x (by norm_num : (1 : ℝ) < 2)
  exact hforall n x hx hn.le

theorem archivedGaussianPrimePrefix_error {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) :
    ∃ D ≥ (0 : ℝ), ∀ x, 0 < x →
      |archivedGaussianRawPrefix x - archivedGaussianPrimePrefix x| ≤ D * x ^ θ := by
  obtain ⟨D, _, hD⟩ := archivedGaussianPrimeHalfWindow_error hθ hθ₁
  let F (x : ℝ) := archivedGaussianRawPrefix x - archivedGaussianPrimePrefix x
  refine dyadic_error_bound F (by linarith) (abs_nonneg archivedGaussianPrimeCenter)
    (D := D) ?_ ?_
  · intro x hp hx
    dsimp [F]
    rw [archivedGaussianRawPrefix_eq_zero hx, archivedGaussianPrimePrefix_eq_linear hx,
      zero_sub, neg_neg, abs_mul, abs_of_pos hp, mul_comm x]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hp hx hθ₁.le
  · intro x hx
    have hp : 0 < x := one_pos.trans_le hx
    have he : F x - F (x / 2) =
        archivedGaussianRawWindow x - archivedGaussianPrimeHalfWindow x := by
      rw [archivedGaussianRawWindow_eq_prefix_sub, archivedGaussianPrimeHalfWindow_eq_prefix_sub hp]
      dsimp [F]
      ring
    rw [he]
    exact hD x hx

#print axioms divisorPrefixMultiplicity_sub_half
#print axioms archivedGaussianRawWindow_eq_prefix_sub
#print axioms archivedGaussianPrimeHalfWindow_eq_prefix_sub
#print axioms archivedGaussianPrimePrefix_error

end
end AlpogeSuperZeta
