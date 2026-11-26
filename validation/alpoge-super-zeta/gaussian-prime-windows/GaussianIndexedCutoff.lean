import GaussianIndexRamp
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.mellinGchiOfNeOne

/-! Termwise Mellin transforms for indexed ramps and prefix counts. -/

namespace AlpogeSuperZeta

open Complex Filter MeasureTheory Set
open scoped Classical

noncomputable section

inductive IndexedCutoff
  | ramp
  | prefix
  | window

def IndexedCutoff.weight : IndexedCutoff → ℝ → ℕ → ℝ
  | .ramp, x, n => indexRampWeight x n
  | .prefix, x, n => if (n : ℝ) < x then 1 else 0
  | .window, x, n => if (n : ℝ) < x ∧ x ≤ 2 * n then 1 else 0

def IndexedCutoff.maxWeight : IndexedCutoff → ℝ → ℝ
  | .ramp, x => x
  | .prefix, _ => 1
  | .window, _ => 1

def IndexedCutoff.mellinDenominator : IndexedCutoff → ℂ → ℂ
  | .ramp, w => w * (w - 1)
  | .prefix, w => w
  | .window, w => w

def IndexedCutoff.mellinNumerator : IndexedCutoff → ℂ → ℂ
  | .ramp, _ => 1
  | .prefix, _ => 1
  | .window, w => 1 - (2 : ℂ) ^ (-w)

def indexedCutoffSum {ι : Type*} (kind : IndexedCutoff)
    (b : ι → ℝ) (N : ι → ℕ) (x : ℝ) : ℝ :=
  ∑' i, b i * kind.weight x (N i)

def indexedDirichletSum {ι : Type*} (b : ι → ℝ) (N : ι → ℕ) (w : ℂ) : ℂ :=
  ∑' i, (b i : ℂ) * (N i : ℂ) ^ (-w)

theorem IndexedCutoff.weight_nonneg (kind : IndexedCutoff) (x : ℝ) (n : ℕ) :
    0 ≤ kind.weight x n := by
  cases kind
  · exact le_max_right _ _
  all_goals simp [IndexedCutoff.weight, apply_ite]

theorem IndexedCutoff.weight_zero_of_le (kind : IndexedCutoff) {x : ℝ} {n : ℕ}
    (hn : 0 < n) (hx : x ≤ n) : kind.weight x n = 0 := by
  cases kind
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    exact max_eq_right (sub_nonpos.mpr ((div_le_iff₀ hn').mpr (by simpa using hx)))
  all_goals simp [IndexedCutoff.weight, not_lt_of_ge hx]

private theorem IndexedCutoff.weight_le (kind : IndexedCutoff) {x : ℝ} (hx : 1 ≤ x)
    {n : ℕ} (hn : 0 < n) : kind.weight x n ≤ kind.maxWeight x := by
  cases kind
  · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv : x / n ≤ x := by
      apply (div_le_iff₀ (zero_lt_one.trans_le hn')).mpr
      nlinarith [(mul_nonneg (zero_le_one.trans hx) (sub_nonneg.mpr hn'))]
    exact max_le ((sub_le_self _ zero_le_one).trans hdiv) (zero_le_one.trans hx)
  all_goals
    simp only [IndexedCutoff.weight, IndexedCutoff.maxWeight]
    split_ifs <;> norm_num

private theorem IndexedCutoff.maxWeight_nonneg (kind : IndexedCutoff) {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ kind.maxWeight x := by
  cases kind <;> simp [IndexedCutoff.maxWeight, zero_le_one.trans hx]

theorem IndexedCutoff.weight_measurable (kind : IndexedCutoff) (n : ℕ) :
    Measurable (fun x => kind.weight x n) := by
  cases kind
  · unfold IndexedCutoff.weight indexRampWeight
    fun_prop
  · exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
  · exact Measurable.ite (measurableSet_Ioi.inter measurableSet_Iic)
      measurable_const measurable_const

theorem indexedCutoffSum_measurable {ι : Type*} [Countable ι] (kind : IndexedCutoff)
    (b : ι → ℝ) (N : ι → ℕ) : Measurable (indexedCutoffSum kind b N) :=
  Measurable.tsum fun i => measurable_const.mul (kind.weight_measurable (N i))

private theorem indexedCutoff_majorant (kind : IndexedCutoff) (b : ℝ) {n : ℕ}
    (hn : 0 < n) {a x : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x) :
    |b * kind.weight x n| ≤ (kind.maxWeight x * x ^ a) * (|b| / (n : ℝ) ^ a) := by
  by_cases hNi : (n : ℝ) < x
  · have hp : 0 < (n : ℝ) ^ a := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
    rw [abs_mul, abs_of_nonneg (kind.weight_nonneg x n)]
    calc
      _ ≤ |b| * kind.maxWeight x := mul_le_mul_of_nonneg_left (kind.weight_le hx hn) (abs_nonneg _)
      _ ≤ (kind.maxWeight x * x ^ a) * (|b| / (n : ℝ) ^ a) := by
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hp).mpr
        have ht := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hNi.le ha)
          (mul_nonneg (abs_nonneg b) (kind.maxWeight_nonneg hx))
        convert ht using 1
        ring
  · rw [kind.weight_zero_of_le hn (le_of_not_gt hNi), mul_zero, abs_zero]
    have := kind.maxWeight_nonneg hx
    positivity

theorem indexedCutoffSum_summable_at {ι : Type*} (kind : IndexedCutoff) (b : ι → ℝ)
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) {a x : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x)
    (h : Summable (fun i => |b i| / (N i : ℝ) ^ a)) :
    Summable (fun i => b i * kind.weight x (N i)) :=
  Summable.of_abs <| (h.mul_left (kind.maxWeight x * x ^ a)).of_nonneg_of_le
    (fun _ => abs_nonneg _) (fun i => indexedCutoff_majorant kind (b i) (hN i) ha hx)

theorem indexedCutoffSum_abs_le {ι : Type*} (kind : IndexedCutoff) (b : ι → ℝ)
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) {a x : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x)
    (h : Summable (fun i => |b i| / (N i : ℝ) ^ a)) :
    |indexedCutoffSum kind b N x| ≤
      (kind.maxWeight x * x ^ a) * (∑' i, |b i| / (N i : ℝ) ^ a) := by
  have hs := (indexedCutoffSum_summable_at kind b N hN ha hx h).abs
  calc
    _ ≤ ∑' i, |b i * kind.weight x (N i)| := by
      simpa only [indexedCutoffSum, Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => b i * kind.weight x (N i))
          (by simpa only [Real.norm_eq_abs] using hs))
    _ ≤ ∑' i, (kind.maxWeight x * x ^ a) * (|b i| / (N i : ℝ) ^ a) :=
      hs.tsum_le_tsum (fun i => indexedCutoff_majorant kind (b i) (hN i) ha hx)
        (h.mul_left (kind.maxWeight x * x ^ a))
    _ = _ := h.tsum_mul_left _

private theorem indexedPrefix_integral (n : ℕ) (hn : 0 < n) (w : ℂ) (hw : 1 < w.re) :
    ∫ x in Ioi (1 : ℝ), ((IndexedCutoff.prefix.weight x n : ℝ) : ℂ) * (x : ℂ) ^ (-w - 1) =
      (n : ℂ) ^ (-w) / w := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcon (x : ℝ) :
      ((IndexedCutoff.prefix.weight x n : ℝ) : ℂ) * (x : ℂ) ^ (-w - 1) =
        (Ioi (n : ℝ)).indicator (fun y : ℝ => (y : ℂ) ^ (-w - 1)) x := by
    by_cases h : (n : ℝ) < x
    · simp [IndexedCutoff.weight, h]
    · simp [IndexedCutoff.weight, h]
  simp_rw [hcon]
  rw [setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Ioi_subset_Ioi hn1)]
  rw [integral_Ioi_cpow_of_lt (by simp only [sub_re, neg_re, one_re]; linarith) hn0,
    sub_add_cancel, div_neg, neg_div, neg_neg, ofReal_natCast]

private theorem indexedPrefix_integrable (n : ℕ) (hn : 0 < n) {w : ℂ} (hw : 1 < w.re) :
    IntegrableOn (fun x : ℝ => (IndexedCutoff.prefix.weight x n : ℂ) * (x : ℂ) ^ (-w - 1))
      (Ioi 1) := by
  apply Integrable.of_integral_ne_zero
  rw [indexedPrefix_integral n hn w hw]
  exact div_ne_zero (cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr hn.ne')))
    (Deduction.mellin_Gchi_of_ne_one_ne hw).1

theorem indexedWindow_weight (x : ℝ) (n : ℕ) :
    IndexedCutoff.window.weight x n =
      IndexedCutoff.prefix.weight x n - IndexedCutoff.prefix.weight x (2 * n) := by
  have hn : (n : ℝ) ≤ 2 * n := by linarith [Nat.cast_nonneg (α := ℝ) n]
  by_cases h₁ : (n : ℝ) < x
  · by_cases h₂ : x ≤ 2 * (n : ℝ)
    · simp [IndexedCutoff.weight, h₁, h₂, not_lt_of_ge h₂, Nat.cast_mul]
    · simp [IndexedCutoff.weight, h₁, h₂, lt_of_not_ge h₂, Nat.cast_mul]
  · have h₂ : ¬2 * (n : ℝ) < x := fun h => h₁ (hn.trans_lt h)
    simp [IndexedCutoff.weight, h₁, h₂, Nat.cast_mul]

private theorem indexedCutoff_integral (kind : IndexedCutoff) (n : ℕ) (hn : 0 < n)
    (w : ℂ) (hw : 1 < w.re) :
    ∫ x in Ioi (1 : ℝ), ((kind.weight x n : ℝ) : ℂ) * (x : ℂ) ^ (-w - 1) =
      (n : ℂ) ^ (-w) * kind.mellinNumerator w / kind.mellinDenominator w := by
  cases kind
  · simpa only [IndexedCutoff.weight, indexRampWeight, IndexedCutoff.mellinNumerator,
      IndexedCutoff.mellinDenominator, mul_one] using
      Deduction.mellin_ramp n hn w hw
  · simpa only [IndexedCutoff.mellinNumerator, IndexedCutoff.mellinDenominator, mul_one] using
      indexedPrefix_integral n hn w hw
  · have h2 : 0 < 2 * n := Nat.mul_pos (by decide) hn
    simp_rw [indexedWindow_weight, ofReal_sub, sub_mul]
    rw [integral_sub (indexedPrefix_integrable n hn hw) (indexedPrefix_integrable (2*n) h2 hw),
      indexedPrefix_integral n hn w hw, indexedPrefix_integral (2*n) h2 w hw, Nat.cast_mul,
      Nat.cast_ofNat]
    have hd : ((2 : ℂ) * (n : ℂ)) ^ (-w) = (2 : ℂ) ^ (-w) * (n : ℂ) ^ (-w) := by
      exact mul_cpow_ofReal_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (Nat.cast_nonneg n) _
    rw [hd, IndexedCutoff.mellinNumerator, IndexedCutoff.mellinDenominator]
    ring

private theorem IndexedCutoff.mellinDenominator_ne_zero (kind : IndexedCutoff)
    {w : ℂ} (hw : 1 < w.re) : kind.mellinDenominator w ≠ 0 := by
  obtain ⟨h0, h1⟩ := Deduction.mellin_Gchi_of_ne_one_ne hw
  cases kind
  · exact mul_ne_zero h0 h1
  all_goals exact h0

theorem norm_two_cpow_neg_lt_one {w : ℂ} (hw : 0 < w.re) :
    ‖(2 : ℂ) ^ (-w)‖ < 1 := by
  change ‖((2 : ℝ) : ℂ) ^ (-w)‖ < 1
  rw [norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), neg_re]
  simpa only [Real.rpow_zero] using
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) (neg_lt_zero.mpr hw)

private theorem IndexedCutoff.mellinNumerator_ne_zero (kind : IndexedCutoff)
    {w : ℂ} (hw : 1 < w.re) : kind.mellinNumerator w ≠ 0 := by
  cases kind
  · exact one_ne_zero
  · exact one_ne_zero
  · intro h
    have h' : (1 : ℂ) - (2 : ℂ) ^ (-w) = 0 := h
    have hb := norm_two_cpow_neg_lt_one (zero_lt_one.trans hw)
    rw [← sub_eq_zero.mp h', norm_one] at hb
    exact (lt_irrefl _ hb)

private theorem indexedCutoff_integral_norm (kind : IndexedCutoff) (n : ℕ) (hn : 0 < n)
    (w : ℂ) (hw : 1 < w.re) :
    ∫ x in Ioi (1 : ℝ), ‖((kind.weight x n : ℝ) : ℂ) * (x : ℂ) ^ (-w - 1)‖ =
      ((kind.mellinNumerator (w.re : ℂ)).re / (kind.mellinDenominator (w.re : ℂ)).re) *
        (1 / (n : ℝ) ^ w.re) := by
  have h := indexedCutoff_integral kind n hn (w.re : ℂ) (by simpa using hw)
  have hd : (((kind.mellinDenominator (w.re : ℂ)).re : ℝ) : ℂ) =
      kind.mellinDenominator (w.re : ℂ) := by
    cases kind <;> simp [IndexedCutoff.mellinDenominator, Complex.mul_re, Complex.ofReal_sub]
  have hnum : (((kind.mellinNumerator (w.re : ℂ)).re : ℝ) : ℂ) =
      kind.mellinNumerator (w.re : ℂ) := by
    cases kind
    · simp [IndexedCutoff.mellinNumerator]
    · simp [IndexedCutoff.mellinNumerator]
    · have hpow : (((2 : ℝ) ^ (-w.re) : ℝ) : ℂ) = (2 : ℂ) ^ (-(w.re : ℂ)) := by
        rw [ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2), ofReal_neg, ofReal_ofNat]
      rw [IndexedCutoff.mellinNumerator, ← hpow]
      simp only [sub_re, one_re, ofReal_re, ofReal_sub, ofReal_one]
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ofReal_mul, ofReal_div, hnum, hd, ofReal_div, ofReal_one,
    ofReal_cpow (Nat.cast_nonneg n), ofReal_natCast]
  calc
    _ = ∫ x in Ioi (1 : ℝ), (kind.weight x n : ℂ) * (x : ℂ) ^ (-(w.re : ℂ) - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx' : (0 : ℝ) < x := one_pos.trans (mem_Ioi.mp hx)
      change ((‖(kind.weight x n : ℂ) * (x : ℂ) ^ (-w - 1)‖ : ℝ) : ℂ) =
        (kind.weight x n : ℂ) * (x : ℂ) ^ (-(w.re : ℂ) - 1)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (kind.weight_nonneg x n),
        norm_cpow_eq_rpow_re_of_pos hx', ofReal_mul, ofReal_cpow hx'.le]
      simp only [sub_re, neg_re, one_re, ofReal_sub, ofReal_neg, ofReal_one]
    _ = _ := by rw [h, cpow_neg]; ring

/-- Absolute termwise integration preserves the index in both weights. -/
theorem indexedCutoffSum_mellin {ι : Type*} [Countable ι] (kind : IndexedCutoff)
    (b : ι → ℝ) (N : ι → ℕ) (hN : ∀ i, 0 < N i) {w : ℂ} (hw : 1 < w.re)
    (hb : Summable (fun i => |b i| / (N i : ℝ) ^ w.re)) :
    IntegrableOn (fun x : ℝ => (indexedCutoffSum kind b N x : ℂ) * (x : ℂ) ^ (-w - 1)) (Ioi 1) ∧
      ∫ x in Ioi (1 : ℝ), (indexedCutoffSum kind b N x : ℂ) * (x : ℂ) ^ (-w - 1) =
        indexedDirichletSum b N w * kind.mellinNumerator w / kind.mellinDenominator w := by
  let F (i : ι) (x : ℝ) := (b i : ℂ) * (((kind.weight x (N i) : ℝ) : ℂ) * (x : ℂ) ^ (-w - 1))
  have hF (i : ι) : IntegrableOn (F i) (Ioi 1) := by
    apply Integrable.const_mul
    apply Integrable.of_integral_ne_zero
    rw [indexedCutoff_integral kind (N i) (hN i) w hw]
    exact div_ne_zero (mul_ne_zero (cpow_ne_zero_iff.mpr
      (Or.inl (Nat.cast_ne_zero.mpr (hN i).ne'))) (kind.mellinNumerator_ne_zero hw))
      (kind.mellinDenominator_ne_zero hw)
  have hnorm : Summable (fun i => ∫ x in Ioi (1 : ℝ), ‖F i x‖) := by
    apply (hb.mul_left
      ((kind.mellinNumerator (w.re : ℂ)).re / (kind.mellinDenominator (w.re : ℂ)).re)).congr
    intro i
    simp only [F, norm_mul (b i : ℂ), Complex.norm_real, Real.norm_eq_abs]
    rw [integral_const_mul, indexedCutoff_integral_norm kind (N i) (hN i) w hw]
    ring
  have hterm (i : ι) : ∫ x in Ioi (1 : ℝ), F i x =
      (b i : ℂ) * (N i : ℂ) ^ (-w) * kind.mellinNumerator w / kind.mellinDenominator w := by
    rw [show F i = (fun x => (b i : ℂ) *
      (((kind.weight x (N i) : ℝ) : ℂ) * (x : ℂ) ^ (-w - 1))) by rfl, integral_const_mul,
      indexedCutoff_integral kind (N i) (hN i) w hw]
    ring
  have hpoint (x : ℝ) (hx : x ∈ Ioi (1 : ℝ)) :
      (indexedCutoffSum kind b N x : ℂ) * (x : ℂ) ^ (-w - 1) = ∑' i, F i x := by
    have hpt := indexedCutoffSum_summable_at kind b N hN
      (one_pos.trans hw).le (le_of_lt hx) hb
    have hh := (Complex.ofRealCLM.hasSum hpt.hasSum).mul_right ((x : ℂ) ^ (-w - 1))
    rw [show (fun i => Complex.ofRealCLM (b i * kind.weight x (N i)) *
      (x : ℂ) ^ (-w - 1)) = (fun i => F i x) from funext fun i => by
        simp [F, mul_assoc]] at hh
    exact hh.tsum_eq.symm
  refine ⟨?_, ?_⟩
  · have hs : IntegrableOn (fun x => ∑' i, F i x) (Ioi (1 : ℝ)) := by
      refine ⟨(AEMeasurable.tsum (fun i => (hF i).1.aemeasurable)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      apply lt_of_le_of_lt (lintegral_mono fun _ => enorm_tsum_le_tsum_enorm)
      rw [lintegral_tsum fun i => (hF i).1.aemeasurable.enorm]
      have he (i : ι) : ∫⁻ x in Ioi (1 : ℝ), ‖F i x‖ₑ =
          ‖∫ x in Ioi (1 : ℝ), ‖F i x‖‖ₑ := by
        dsimp [enorm]
        rw [lintegral_coe_eq_integral _ (hF i).norm, ENNReal.coe_nnreal_eq, coe_nnnorm,
          Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg (F i x)))]
        simp only [coe_nnnorm]
      rw [funext he]
      exact lt_top_iff_ne_top.mpr
        (ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hnorm.abs))
    exact hs.congr_fun (fun x hx => (hpoint x hx).symm) measurableSet_Ioi
  calc
    _ = ∫ x in Ioi (1 : ℝ), ∑' i, F i x := setIntegral_congr_fun measurableSet_Ioi hpoint
    _ = ∑' i, ∫ x in Ioi (1 : ℝ), F i x :=
      (integral_tsum_of_summable_integral_norm hF hnorm).symm
    _ = _ := by simp_rw [hterm, div_eq_mul_inv, tsum_mul_right, indexedDirichletSum]

#print axioms indexedCutoffSum_mellin

end
end AlpogeSuperZeta
