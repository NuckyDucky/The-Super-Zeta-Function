import GaussianIndexedCutoff

/-! The squared full-prefix weight, using three shifts of the same
termwise Mellin theorem. -/

namespace AlpogeSuperZeta

open Complex MeasureTheory Set

noncomputable section

private def prefixMoment {ι : Type*} (b : ι → ℝ) (N : ι → ℕ) (k : ℕ) : ℝ → ℝ :=
  indexedCutoffSum .prefix (fun i => b i * (N i : ℝ) ^ k) N

def indexedSquaredRamp {ι : Type*} (b : ι → ℝ) (N : ι → ℕ) (x : ℝ) : ℝ :=
  prefixMoment b N 0 x - (2 / x) * prefixMoment b N 1 x + prefixMoment b N 2 x / x ^ 2

theorem indexedSquaredRamp_measurable {ι : Type*} [Countable ι] (b : ι → ℝ) (N : ι → ℕ) :
    Measurable (indexedSquaredRamp b N) := by
  have h k : Measurable (prefixMoment b N k) := indexedCutoffSum_measurable _ _ _
  exact ((h 0).sub ((measurable_const.div measurable_id).mul (h 1))).add
    ((h 2).div (measurable_id.pow_const _))

private theorem prefixMoment_summable {ι : Type*} (b : ι → ℝ) (N : ι → ℕ) (hN : ∀ i, 0 < N i)
    (k : ℕ) {a : ℝ} (h : Summable fun i => |b i| / (N i : ℝ) ^ a) :
    Summable (fun i => |b i * (N i : ℝ) ^ k| / (N i : ℝ) ^ (a + k)) := by
  apply h.congr
  intro i
  have hp : (0 : ℝ) < N i := Nat.cast_pos.mpr (hN i)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hp.le _), Real.rpow_add hp, Real.rpow_natCast]
  field_simp

def squaredRampWeight (x : ℝ) (n : ℕ) : ℝ :=
  if (n : ℝ) < x then (1 - (n : ℝ) / x) ^ 2 else 0

theorem indexedSquaredRamp_eq_sum {ι : Type*} (b : ι → ℝ) (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) {a x : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x)
    (hb : Summable fun i => |b i| / (N i : ℝ) ^ a) :
    indexedSquaredRamp b N x = ∑' i, b i * squaredRampWeight x (N i) := by
  let F (k : ℕ) (i : ι) := (b i * (N i : ℝ) ^ k) * IndexedCutoff.prefix.weight x (N i)
  have h k : Summable (F k) :=
    indexedCutoffSum_summable_at .prefix _ N hN (by positivity : 0 ≤ a + (k : ℝ)) hx
      (prefixMoment_summable b N hN k hb)
  change (∑' i, F 0 i) - (2 / x) * (∑' i, F 1 i) + (∑' i, F 2 i) / x ^ 2 = _
  rw [← tsum_mul_left, ← tsum_div_const,
    ← (h 0).tsum_sub ((h 1).mul_left (2 / x)),
    ← ((h 0).sub ((h 1).mul_left (2 / x))).tsum_add ((h 2).div_const (x ^ 2))]
  apply tsum_congr
  intro i
  by_cases hnx : (N i : ℝ) < x
  · simp only [F, IndexedCutoff.weight, squaredRampWeight, if_pos hnx, mul_one, pow_zero, pow_one]
    have hx0 : x ≠ 0 := (zero_lt_one.trans_le hx).ne'
    field_simp
    ring
  · simp [F, IndexedCutoff.weight, squaredRampWeight, hnx]

theorem indexedSquaredRamp_abs_le {ι : Type*} (b : ι → ℝ) (N : ι → ℕ)
    (hN : ∀ i, 0 < N i) {a x : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x)
    (hb : Summable fun i => |b i| / (N i : ℝ) ^ a) :
    |indexedSquaredRamp b N x| ≤ x ^ a * ∑' i, |b i| / (N i : ℝ) ^ a := by
  have hAbs : Summable (fun i => abs (abs (b i)) / (N i : ℝ) ^ a) := by
    simpa only [abs_abs] using hb
  have hPrefix := indexedCutoffSum_summable_at .prefix (fun i => |b i|) N hN ha hx hAbs
  have hle (i : ι) : |b i * squaredRampWeight x (N i)| ≤
      |b i| * IndexedCutoff.prefix.weight x (N i) := by
    by_cases h : (N i : ℝ) < x
    · have hn : 0 ≤ (N i : ℝ) / x := div_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hx)
      have hn' : (N i : ℝ) / x ≤ 1 := (div_le_one (one_pos.trans_le hx)).mpr h.le
      have hs : (1 - (N i : ℝ) / x) ^ 2 ≤ 1 := by
        have h₀ : 0 ≤ 1 - (N i : ℝ) / x := sub_nonneg.mpr hn'
        have h₁ : 1 - (N i : ℝ) / x ≤ 1 := sub_le_self _ hn
        simpa only [one_pow] using pow_le_pow_left₀ h₀ h₁ 2
      simpa only [squaredRampWeight, IndexedCutoff.weight, if_pos h, abs_mul,
        abs_of_nonneg (sq_nonneg (1 - (N i : ℝ) / x)), mul_one] using
        mul_le_of_le_one_right (abs_nonneg (b i)) hs
    · simp [squaredRampWeight, IndexedCutoff.weight, h]
  have hs := hPrefix.of_nonneg_of_le (fun i => abs_nonneg (b i * squaredRampWeight x (N i))) hle
  rw [indexedSquaredRamp_eq_sum b N hN ha hx hb]
  calc
    _ ≤ ∑' i, |b i * squaredRampWeight x (N i)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
        (f := fun i => b i * squaredRampWeight x (N i)) (by simpa only [Real.norm_eq_abs] using hs)
    _ ≤ indexedCutoffSum .prefix (fun i => |b i|) N x := hs.tsum_le_tsum hle hPrefix
    _ ≤ _ := by
      have h := indexedCutoffSum_abs_le .prefix (fun i => |b i|) N hN ha hx hAbs
      exact (le_abs_self _).trans (by simpa only [IndexedCutoff.maxWeight, one_mul, abs_abs] using h)

private theorem cpow_shift_by_nat (x w : ℂ) (hx : x ≠ 0) (k : ℕ) :
    x ^ (-(w + k) - 1) = x ^ (-w - 1) / x ^ k := by
  rw [show -(w + (k : ℂ)) - 1 = (-w - 1) + (-(k : ℂ)) by ring,
    cpow_add _ _ hx, cpow_neg, cpow_natCast, div_eq_mul_inv]

private theorem prefixMoment_mellin {ι : Type*} [Countable ι] (b : ι → ℝ)
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) (k : ℕ) {w : ℂ} (hw : 1 < w.re)
    (hb : Summable fun i => |b i| / (N i : ℝ) ^ w.re) :
    IntegrableOn (fun x : ℝ => (prefixMoment b N k x : ℂ) * (x : ℂ) ^ (-(w + k) - 1)) (Ioi 1) ∧
      ∫ x in Ioi (1 : ℝ), (prefixMoment b N k x : ℂ) * (x : ℂ) ^ (-(w + k) - 1) =
        indexedDirichletSum b N w / (w + k) := by
  have hk : 1 < (w + k).re := by
    simp only [add_re, natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have h := indexedCutoffSum_mellin .prefix (fun i => b i * (N i : ℝ) ^ k) N hN hk
    (by simpa only [add_re, natCast_re] using prefixMoment_summable b N hN k hb)
  refine ⟨h.1, ?_⟩
  rw [prefixMoment, h.2, IndexedCutoff.mellinNumerator, mul_one, IndexedCutoff.mellinDenominator]
  congr 1
  apply tsum_congr
  intro i
  have hn : (N i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hN i).ne'
  rw [ofReal_mul, ofReal_pow, ofReal_natCast, neg_add, cpow_add _ _ hn,
    cpow_neg (N i : ℂ) (k : ℂ), cpow_natCast]
  field_simp

theorem indexedSquaredRamp_mellin {ι : Type*} [Countable ι] (b : ι → ℝ)
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) {w : ℂ} (hw : 1 < w.re)
    (hb : Summable fun i => |b i| / (N i : ℝ) ^ w.re) :
    IntegrableOn (fun x : ℝ => (indexedSquaredRamp b N x : ℂ) * (x : ℂ) ^ (-w - 1)) (Ioi 1) ∧
      ∫ x in Ioi (1 : ℝ), (indexedSquaredRamp b N x : ℂ) * (x : ℂ) ^ (-w - 1) =
        indexedDirichletSum b N w * 2 / (w * (w + 1) * (w + 2)) := by
  let F (k : ℕ) (x : ℝ) := (prefixMoment b N k x : ℂ) * (x : ℂ) ^ (-(w + k) - 1)
  have h k : IntegrableOn (F k) (Ioi 1) ∧ ∫ x in Ioi (1 : ℝ), F k x =
      indexedDirichletSum b N w / (w + k) := prefixMoment_mellin b N hN k hw hb
  have hF (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (indexedSquaredRamp b N x : ℂ) * (x : ℂ) ^ (-w - 1) = F 0 x - 2 * F 1 x + F 2 x := by
    have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (one_pos.trans (mem_Ioi.mp hx)).ne'
    simp only [indexedSquaredRamp, F, cpow_shift_by_nat _ _ hx0, ofReal_add, ofReal_sub,
      ofReal_div, ofReal_mul, ofReal_pow, ofReal_ofNat, pow_zero, pow_one, div_one]
    ring
  have hi := ((h 0).1.sub ((h 1).1.const_mul (2 : ℂ))).add (h 2).1
  refine ⟨hi.congr_fun (fun x hx => (hF x hx).symm) measurableSet_Ioi, ?_⟩
  have hadd : (∫ x in Ioi (1 : ℝ), F 0 x - 2 * F 1 x + F 2 x) =
      (∫ x in Ioi (1 : ℝ), F 0 x - 2 * F 1 x) + ∫ x in Ioi (1 : ℝ), F 2 x :=
    integral_add ((h 0).1.sub ((h 1).1.const_mul (2 : ℂ))) (h 2).1
  have hsub : (∫ x in Ioi (1 : ℝ), F 0 x - 2 * F 1 x) =
      (∫ x in Ioi (1 : ℝ), F 0 x) - ∫ x in Ioi (1 : ℝ), 2 * F 1 x :=
    integral_sub (h 0).1 ((h 1).1.const_mul (2 : ℂ))
  rw [setIntegral_congr_fun measurableSet_Ioi hF, hadd, hsub,
    integral_const_mul, (h 0).2, (h 1).2, (h 2).2]
  simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero]
  have h0 : w ≠ 0 := by
    intro he
    rw [he, zero_re] at hw
    linarith
  have h1 : w + 1 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp only [add_re, one_re, zero_re] at hr
    linarith
  have h2 : w + 2 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    change w.re + (2 : ℝ) = 0 at hr
    linarith
  field_simp
  ring

#print axioms indexedSquaredRamp_mellin
#print axioms indexedSquaredRamp_eq_sum
#print axioms indexedSquaredRamp_abs_le

end
end AlpogeSuperZeta
