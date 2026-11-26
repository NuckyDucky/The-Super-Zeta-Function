import GaussianSharpRationalMainTerm

/-! A half-unit transition beyond the last included integer gives the
exact strict prefix. Removing the higher powers preserves the exponent. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Finset Set ArtinPrimitiveRootsConjecture
open scoped Classical

noncomputable section

def rationalStrictPrefix (a : ArithmeticFunction ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ range ⌈x⌉₊, a n

theorem perron_eq_rationalStrictPrefix (a : ArithmeticFunction ℂ) {x : ℝ}
    (hx : 2 ≤ x) :
    let y : ℝ := (⌈x⌉₊ : ℝ) - 1
    dirichletKernelSum a (shortPerronKernel (1 / (2 * y))) y⁻¹ = rationalStrictPrefix a x := by
  let y : ℝ := (⌈x⌉₊ : ℝ) - 1
  let d : ℝ := 1 / (2 * y)
  have hy : 0 < y := by dsimp [y]; linarith [Nat.le_ceil x]
  have hd : 0 < d := by dsimp [d]; positivity
  have hd' : (1 + d) * y = y + 1 / 2 := by
    have h : d * y = 1 / 2 := by dsimp [d]; field_simp
    linarith
  change (∑' n : ℕ, a n * shortPerronKernel d (n * y⁻¹)) = _
  rw [rationalStrictPrefix, tsum_eq_sum (s := range ⌈x⌉₊)]
  · apply sum_congr rfl
    intro n hn
    have h : (n : ℝ) + 1 ≤ (⌈x⌉₊ : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (mem_range.mp hn)
    have h₁ : (n : ℝ) * y⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hy]
      dsimp [y]
      linarith
    rw [shortPerronKernel_eq_one hd h₁, mul_one]
  · intro n hn
    have h : (⌈x⌉₊ : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast Nat.le_of_not_gt (fun h => hn (mem_range.mpr h))
    have h₀ : 1 + d ≤ (n : ℝ) * y⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hy, hd']
      dsimp [y]
      linarith
    rw [shortPerronKernel_eq_zero hd h₀, mul_zero]

theorem archivedGaussianSplitMangoldt_prefix_main_term (hDir : DirichletLZerosOnLine)
    {t : ℝ} (ht : 1 / 2 < t) (ht₁ : t < 1) :
    ∃ C ≥ 0, ∀ x ≥ (2 : ℝ),
      ‖rationalStrictPrefix archivedGaussianSplitMangoldt x - (x : ℂ)‖ ≤ C * x ^ t := by
  let r := (1 / 2 + t) / 2
  let e := t - r
  have hr : 1 / 2 < r := by dsimp [r]; linarith
  have hr₁ : r < 1 := by dsimp [r]; linarith
  have he : 0 < e := by dsimp [r, e]; linarith
  have he₁ : e ≤ 1 := by dsimp [r, e]; linarith
  obtain ⟨C, hC, hB⟩ := archivedGaussianSharpPerron_scaled hDir hr hr₁ he he₁
  refine ⟨C + 1, by positivity, fun x hx => ?_⟩
  let y : ℝ := (⌈x⌉₊ : ℝ) - 1
  have hy : 1 ≤ y := by dsimp [y]; linarith [Nat.le_ceil x]
  have hL : x - 1 ≤ y := by dsimp [y]; linarith [Nat.le_ceil x]
  have hR : y ≤ x := by dsimp [y]; linarith [Nat.ceil_lt_add_one (show 0 ≤ x by linarith)]
  have hE := hB y hy
  rw [show r + e = t by dsimp [e]; ring] at hE
  change ‖dirichletKernelSum archivedGaussianSplitMangoldt (shortPerronKernel (1 / (2 * y))) y⁻¹ -
    (y : ℂ)‖ ≤ C * y ^ t at hE
  rw [perron_eq_rationalStrictPrefix archivedGaussianSplitMangoldt hx] at hE
  have hClose : ‖(y : ℂ) - (x : ℂ)‖ ≤ 1 := by
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  calc
    _ ≤ ‖rationalStrictPrefix archivedGaussianSplitMangoldt x - (y : ℂ)‖ +
        ‖(y : ℂ) - (x : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ C * y ^ t + 1 := add_le_add hE hClose
    _ ≤ C * x ^ t + x ^ t := add_le_add (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) hR (by linarith)) hC)
      (Real.one_le_rpow (by linarith) (by linarith))
    _ = _ := by ring

private theorem rationalStrictPrefix_norm_le {a : ArithmeticFunction ℂ} {t x : ℝ}
    (ht : 0 ≤ t) (hx : 0 < x) (hA : LSeriesSummable a (t : ℂ)) :
    ‖rationalStrictPrefix a x‖ ≤ x ^ t * ∑' n : ℕ, ‖LSeries.term a (t : ℂ) n‖ := by
  have hTerm (n : ℕ) (hn : n ∈ range ⌈x⌉₊) :
      ‖a n‖ ≤ x ^ t * ‖LSeries.term a (t : ℂ) n‖ := by
    by_cases hn₀ : n = 0
    · subst n
      simp [LSeries.term]
    have hnR := Nat.lt_ceil.mp (mem_range.mp hn)
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn₀)
    rw [LSeries.term_of_ne_zero hn₀, norm_div, ← ofReal_natCast,
      norm_cpow_eq_rpow_re_of_pos hnpos, ofReal_re, ← mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hnpos _)).mpr
    rw [mul_comm ‖a n‖]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hnpos.le hnR.le ht) (norm_nonneg _)
  calc
    _ ≤ ∑ n ∈ range ⌈x⌉₊, ‖a n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ range ⌈x⌉₊, x ^ t * ‖LSeries.term a (t : ℂ) n‖ := sum_le_sum hTerm
    _ ≤ _ := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left
        (hA.norm.sum_le_tsum _ (fun n _ => norm_nonneg (LSeries.term a (t : ℂ) n)))
        (Real.rpow_nonneg hx.le _)

theorem archivedGaussianSplitPrime_prefix_main_term (hDir : DirichletLZerosOnLine)
    {t : ℝ} (ht : 1 / 2 < t) (ht₁ : t < 1) :
    ∃ C ≥ 0, ∀ x ≥ (2 : ℝ),
      ‖rationalStrictPrefix (primePart archivedGaussianSplitMangoldt) x - (x : ℂ)‖ ≤ C * x ^ t := by
  obtain ⟨A, hA, hP⟩ := archivedGaussianSplitMangoldt_prefix_main_term hDir ht ht₁
  let a := archivedGaussianSplitMangoldt
  let b := primePowerTail 2 a
  have hs : LSeriesSummable b (t : ℂ) := by
    apply primePowerTail_summable 2 _ (by norm_num : (0 : ℝ) ≤ 4) archivedGaussianSplitMangoldt_norm_le
    · change 0 < t
      linarith
    · change 1 < (2 : ℝ) * t
      linarith
  let B := ∑' n : ℕ, ‖LSeries.term b (t : ℂ) n‖
  have hB : 0 ≤ B := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨A + B, by positivity, fun x hx => ?_⟩
  have he : primePart a + b = a := by
    apply primePart_add_tail_two
    intro n hn
    simp [a, archivedGaussianSplitMangoldt, vonMangoldt_eq_zero_iff.mpr hn]
  have hsum : rationalStrictPrefix (primePart a) x =
      rationalStrictPrefix a x - rationalStrictPrefix b x := by
    have h : rationalStrictPrefix (primePart a + b) x =
        rationalStrictPrefix (primePart a) x + rationalStrictPrefix b x := by
      simp only [rationalStrictPrefix, ArithmeticFunction.add_apply, sum_add_distrib]
    rw [he] at h
    exact eq_sub_of_add_eq h.symm
  rw [hsum]
  calc
    _ = ‖(rationalStrictPrefix a x - (x : ℂ)) - rationalStrictPrefix b x‖ := by congr 1; ring
    _ ≤ ‖rationalStrictPrefix a x - (x : ℂ)‖ + ‖rationalStrictPrefix b x‖ := norm_sub_le _ _
    _ ≤ A * x ^ t + x ^ t * B := add_le_add (hP x hx)
      (rationalStrictPrefix_norm_le (by linarith) (by linarith) hs)
    _ = _ := by ring

#print axioms perron_eq_rationalStrictPrefix
#print axioms archivedGaussianSplitMangoldt_prefix_main_term
#print axioms archivedGaussianSplitPrime_prefix_main_term

end
end AlpogeSuperZeta
