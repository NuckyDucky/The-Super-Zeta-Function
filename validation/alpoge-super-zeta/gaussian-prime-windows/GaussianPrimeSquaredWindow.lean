import GaussianDivisorSquaredWindow
import GaussianPrimePrefix
import GaussianSquaredSmoothing

/-! The centered signed prime sum with the squared cutoff has the same
power-scale error as the original half-window, with its own exact centering. -/

namespace AlpogeSuperZeta

open ArithmeticFunction ArtinPrimitiveRootsConjecture FieldTarget Finset MeasureTheory QuarticModel Set
open scoped Classical

noncomputable section

theorem archivedGaussianSignedPrimeWeight_abs_le {p : ℕ} (hp : p.Prime) :
    |archivedGaussianSignedPrimeWeight p| ≤ 2 * Real.log p := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  rw [archivedGaussianSignedPrimeWeight, if_pos hp, vonMangoldt_apply_prime hp,
    abs_neg, abs_mul, abs_of_nonneg hlog, mul_comm (2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (archivedGaussianPrimeWeight_abs_le_two p) hlog

theorem archivedGaussianSignedPrimeWeight_summable {a : ℝ} (ha : 1 < a) :
    Summable (fun p : ℕ => |archivedGaussianSignedPrimeWeight p| / ((max 1 p : ℕ) : ℝ) ^ a) := by
  have h := ((LSeriesSummable_vonMangoldt (s := (a : ℂ))
    (by simpa using ha)).norm).mul_left (2 : ℝ)
  refine h.of_nonneg_of_le (fun _ => div_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun p => ?_)
  by_cases hp : p.Prime
  · have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    rw [max_eq_right hp.one_lt.le, LSeries.norm_term_eq, if_neg hp.ne_zero,
      vonMangoldt_apply_prime hp, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (archivedGaussianSignedPrimeWeight_abs_le hp)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · simp only [archivedGaussianSignedPrimeWeight, if_neg hp, mul_zero, neg_zero, abs_zero, zero_div]
    positivity

private theorem primeAddress_pos (p : ℕ) : 0 < max 1 p :=
  (Nat.zero_lt_succ 0).trans_le (le_max_left _ _)

private theorem weightedPrefixMultiplicity_sum {x : ℝ} (hx : 0 ≤ x) (b : ℝ) {d : ℕ} (hd : 0 < d) :
    (∑ m ∈ range ⌈x⌉₊, b * IndexedCutoff.prefix.weight x (d * (m + 1))) =
      b * divisorPrefixMultiplicity x d := by
  let Q : ℕ := ⌈x / (d : ℝ)⌉₊ - 1
  have hmem (m : ℕ) : (↑(d * (m + 1) : ℕ) : ℝ) < x ↔ m < Q := by
    rw [Nat.cast_mul, mul_comm (d : ℝ), ← lt_div_iff₀ (Nat.cast_pos.mpr hd), ← Nat.lt_ceil]
    dsimp [Q]
    omega
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdiv : x / (d : ℝ) ≤ x :=
    (div_le_iff₀ (Nat.cast_pos.mpr hd)).mpr (by nlinarith [mul_nonneg hx (sub_nonneg.mpr hd₁)])
  have hQ : Q ≤ ⌈x⌉₊ := (Nat.sub_le _ _).trans (Nat.ceil_le_ceil hdiv)
  have hF : (range ⌈x⌉₊).filter (fun m => m < Q) = range Q := by
    ext m
    simp only [mem_filter, Finset.mem_range]
    exact ⟨And.right, fun hm => ⟨hm.trans_le hQ, hm⟩⟩
  calc
    _ = ∑ m ∈ range ⌈x⌉₊, (if m < Q then b else 0) :=
      sum_congr rfl fun m _ => by simp only [IndexedCutoff.weight, hmem, mul_ite, mul_one, mul_zero]
    _ = _ := by rw [← sum_filter, hF, sum_const, card_range, nsmul_eq_mul, mul_comm]; rfl

private def primeDivisorWeight (q : ℕ × ℕ) : ℝ := archivedGaussianSignedPrimeWeight q.1

private def primeDivisorAddress : ℕ × ℕ → ℕ := divisorWindowIndex (max 1 ·)

private theorem primeDivisorAddress_pos : ∀ q, 0 < primeDivisorAddress q :=
  divisorWindowIndex_pos primeAddress_pos

private theorem primeDivisorWeight_summable {a : ℝ} (ha : 1 < a) :
    Summable (fun q => |primeDivisorWeight q| / (primeDivisorAddress q : ℝ) ^ a) :=
  divisorWindow_summable archivedGaussianSignedPrimeWeight (max 1 ·) ha
    (archivedGaussianSignedPrimeWeight_summable ha)

private def primeDivisorIndices (x : ℝ) : Finset (ℕ × ℕ) :=
  (range (⌊x⌋₊ + 1)).product (range ⌈x⌉₊)

private theorem primeDivisorAddress_support {x : ℝ} (hx : 0 ≤ x) {q : ℕ × ℕ}
    (h : (primeDivisorAddress q : ℝ) < x) : q ∈ primeDivisorIndices x := by
  have h₁ : q.1 ≤ primeDivisorAddress q := (le_max_right _ _).trans (by
    simpa only [primeDivisorAddress, divisorWindowIndex, mul_one] using
      Nat.mul_le_mul_left (max 1 q.1) (show 1 ≤ q.2 + 1 by omega))
  have h₂ : q.2 + 1 ≤ primeDivisorAddress q := by
    simpa only [primeDivisorAddress, divisorWindowIndex, one_mul] using
      Nat.mul_le_mul_right (q.2 + 1) (le_max_left 1 q.1)
  have hf := (Nat.le_floor_iff hx).mpr ((Nat.cast_le.mpr h₁).trans h.le)
  have hm := Nat.lt_ceil.mpr ((Nat.cast_le.mpr h₂).trans_lt h)
  exact mem_product.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hf),
    mem_range.mpr ((Nat.lt_succ_self _).trans hm)⟩

private theorem archivedGaussianPrimePrefix_eq_indexed {x : ℝ} (hx : 0 ≤ x) :
    archivedGaussianPrimePrefix x =
      indexedCutoffSum .prefix primeDivisorWeight primeDivisorAddress x -
        x * archivedGaussianPrimeCenter := by
  have hs : HasSum (fun q => primeDivisorWeight q * IndexedCutoff.prefix.weight x (primeDivisorAddress q))
      (∑ q ∈ primeDivisorIndices x, primeDivisorWeight q * IndexedCutoff.prefix.weight x (primeDivisorAddress q)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro q hq
    simp only [IndexedCutoff.weight, if_neg (fun h => hq (primeDivisorAddress_support hx h)), mul_zero]
  unfold archivedGaussianPrimePrefix indexedCutoffSum
  rw [hs.tsum_eq]
  congr 1
  have hp : (∑ q ∈ primeDivisorIndices x,
      primeDivisorWeight q * IndexedCutoff.prefix.weight x (primeDivisorAddress q)) =
      ∑ p ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range ⌈x⌉₊,
        primeDivisorWeight (p, m) * IndexedCutoff.prefix.weight x (primeDivisorAddress (p, m)) :=
    sum_product ..
  rw [hp]
  apply sum_congr rfl
  intro p _
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [primeDivisorWeight, archivedGaussianSignedPrimeWeight]
  · simpa only [primeDivisorWeight, primeDivisorAddress, divisorWindowIndex,
      max_eq_right (show 1 ≤ p from hp)] using
      (weightedPrefixMultiplicity_sum hx (archivedGaussianSignedPrimeWeight p) hp).symm

/-- The squared prime-only window. Its explicit linear subtraction is
one third of the full-prefix subtraction. -/
def archivedGaussianPrimeSquaredWindow (x : ℝ) : ℝ :=
  indexedSquaredRamp primeDivisorWeight primeDivisorAddress x - x / 3 * archivedGaussianPrimeCenter

theorem archivedGaussianPrimeSquaredWindow_eq_sum {x : ℝ} (hx : 1 ≤ x) :
    archivedGaussianPrimeSquaredWindow x =
      (∑ p ∈ range (⌊x⌋₊ + 1), archivedGaussianSignedPrimeWeight p *
        ∑ m ∈ range ⌈x⌉₊, squaredRampWeight x ((m + 1) * p)) -
      x / 3 * archivedGaussianPrimeCenter := by
  have hs : HasSum (fun q => primeDivisorWeight q * squaredRampWeight x (primeDivisorAddress q))
      (∑ q ∈ primeDivisorIndices x, primeDivisorWeight q * squaredRampWeight x (primeDivisorAddress q)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro q hq
    simp only [squaredRampWeight,
      if_neg (fun h => hq (primeDivisorAddress_support (zero_le_one.trans hx) h)), mul_zero]
  unfold archivedGaussianPrimeSquaredWindow
  rw [indexedSquaredRamp_eq_sum _ _ primeDivisorAddress_pos (a := 2) (by norm_num) hx
    (primeDivisorWeight_summable (by norm_num)), hs.tsum_eq]
  congr 1
  have hprod : (∑ q ∈ primeDivisorIndices x, primeDivisorWeight q * squaredRampWeight x (primeDivisorAddress q)) =
      ∑ p ∈ range (⌊x⌋₊ + 1), ∑ m ∈ range ⌈x⌉₊,
        primeDivisorWeight (p, m) * squaredRampWeight x (primeDivisorAddress (p, m)) :=
    sum_product ..
  rw [hprod]
  apply sum_congr rfl
  intro p _
  rw [mul_sum]
  apply sum_congr rfl
  intro m _
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [primeDivisorWeight, archivedGaussianSignedPrimeWeight]
  · simp only [primeDivisorAddress, divisorWindowIndex, max_eq_right (show 1 ≤ p from hp),
      primeDivisorWeight, Nat.mul_comm p]

theorem archivedGaussianPrimeSquaredWindow_error {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) :
    ∃ D ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ),
      |archivedGaussianSquaredWindow x - archivedGaussianPrimeSquaredWindow x| ≤ D * x ^ θ := by
  obtain ⟨D, hD, hPrefix⟩ := archivedGaussianPrimePrefix_error hθ hθ₁
  refine ⟨D, hD, fun x hx => ?_⟩
  have hx₀ : 0 < x := one_pos.trans_le hx
  have hRaw := indexedSquaredRamp_eq_integral
    (fun q : GaussianIndexFamily × ℕ => gaussianIndexCoefficient q.1)
    (divisorWindowIndex gaussianIndexAddress) (divisorWindowIndex_pos gaussianIndexAddress_pos)
    (a := 2) hx (by norm_num) (divisorWindow_summable gaussianIndexCoefficient gaussianIndexAddress
      (by norm_num) (gaussianIndexFamily_summable (by norm_num)))
  let P := indexedCutoffSum .prefix primeDivisorWeight primeDivisorAddress
  have hPrime := indexedSquaredRamp_eq_integral primeDivisorWeight primeDivisorAddress primeDivisorAddress_pos
    (a := 2) hx (by norm_num) (primeDivisorWeight_summable (by norm_num))
  have hL : IntegrableOn (fun t => (x - t) * (t * archivedGaussianPrimeCenter)) (Ioc 0 x) :=
    ((continuous_const.sub continuous_id).mul (continuous_id.mul continuous_const)).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hEq (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) x) :
      (x - t) * (P t - t * archivedGaussianPrimeCenter) = (x - t) * archivedGaussianPrimePrefix t := by
    rw [archivedGaussianPrimePrefix_eq_indexed ht.1.le]
  have hI : IntegrableOn (fun t => (x - t) * archivedGaussianPrimePrefix t) (Ioc 0 x) :=
    (hPrime.1.sub hL).congr_fun (fun t ht => (mul_sub _ _ _).symm.trans (hEq t ht)) measurableSet_Ioc
  have hS : archivedGaussianPrimeSquaredWindow x = squaredCutoffIntegral archivedGaussianPrimePrefix x := by
    rw [archivedGaussianPrimeSquaredWindow, hPrime.2, ← squaredCutoffIntegral_linear hx₀,
      squaredCutoffIntegral_sub hPrime.1 hL, squaredCutoffIntegral, squaredCutoffIntegral]
    congr 1
    exact setIntegral_congr_fun measurableSet_Ioc hEq
  have hR : archivedGaussianSquaredWindow x = squaredCutoffIntegral archivedGaussianRawPrefix x :=
    hRaw.2
  rw [hR, hS]
  exact squaredCutoffIntegral_error hx₀ (by linarith) hD hRaw.1 hI (fun t ht => hPrefix t ht.1)

theorem gaussianCutoffWindowBound_iff_of_error {A B : ℝ → ℝ} {X₀ : ℝ}
    (hError : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ D ≥ (0 : ℝ), ∀ x ≥ X₀, |A x - B x| ≤ D * x ^ θ) :
    GaussianCutoffWindowBound A ↔ GaussianCutoffWindowBound B := by
  constructor <;> intro h θ hθ hθ₁
  all_goals
    obtain ⟨D, hD, hE⟩ := hError θ hθ hθ₁
    obtain ⟨δ, hδ, C, hC, hW⟩ := h θ hθ hθ₁
    refine ⟨δ, hδ, C + D, add_nonneg hC hD, fun Y₀ => ?_⟩
    obtain ⟨Y, hY, hb⟩ := hW (max Y₀ X₀)
    refine ⟨Y, (le_max_left _ _).trans hY, fun y hy => ?_⟩
    have hy₀ : X₀ ≤ y := (le_max_right Y₀ X₀).trans (hY.trans hy.1)
    have hL := abs_le.mp (hE y hy₀)
  · linarith only [hb y hy, hL.1]
  · linarith only [hb y hy, hL.2]

theorem archivedGaussianSquaredWindowBound_iff_prime_squared :
    GaussianCutoffWindowBound archivedGaussianSquaredWindow ↔ GaussianCutoffWindowBound archivedGaussianPrimeSquaredWindow :=
  gaussianCutoffWindowBound_iff_of_error (X₀ := 1) (fun _ => archivedGaussianPrimeSquaredWindow_error)

theorem quartic_rh_of_archived_gaussian_prime_squared_windows (hD : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianPrimeSquaredWindow) : DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_gaussian_squared_windows hD hpos
    (archivedGaussianSquaredWindowBound_iff_prime_squared.mpr hcut)

#print axioms archivedGaussianSignedPrimeWeight_summable
#print axioms archivedGaussianPrimeSquaredWindow_eq_sum
#print axioms archivedGaussianPrimeSquaredWindow_error
#print axioms archivedGaussianSquaredWindowBound_iff_prime_squared
#check quartic_rh_of_archived_gaussian_prime_squared_windows
#print axioms quartic_rh_of_archived_gaussian_prime_squared_windows

end
end AlpogeSuperZeta
