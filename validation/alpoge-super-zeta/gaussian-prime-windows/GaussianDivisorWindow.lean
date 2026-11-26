import GaussianIndexFamily
import GaussianPrimitiveIndexMellin
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! Repeating an index at each positive multiple introduces ordinary
zeta. The finite window uses the un-inverted determinant counts. -/

namespace AlpogeSuperZeta

open Complex Finset MeasureTheory Set
open scoped Classical

noncomputable section

private theorem zeta_positive_indices {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun m : ℕ => ((m + 1 : ℕ) : ℂ) ^ (-w)) (riemannZeta w) := by
  have h : HasSum (LSeries.term 1 w) (riemannZeta w) := LSeriesHasSum_one hw
  have hm := (hasSum_nat_add_iff' (f := LSeries.term 1 w) 1).mpr h
  have ht (m : ℕ) : LSeries.term 1 w (m + 1) = ((m + 1 : ℕ) : ℂ) ^ (-w) := by
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero m), cpow_neg]
    exact one_div _
  simpa only [Finset.sum_range_one, LSeries.term_zero, sub_zero, ht] using hm

private theorem zeta_index_abs (n : ℕ) (hn : 0 < n) (w : ℂ) :
    ‖(n : ℂ) ^ (-w)‖ = 1 / (n : ℝ) ^ w.re := by
  rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn),
    neg_re, Real.rpow_neg (Nat.cast_nonneg n), one_div]

def divisorWindowIndex {ι : Type*} (N : ι → ℕ) (p : ι × ℕ) : ℕ :=
  N p.1 * (p.2 + 1)

theorem divisorWindowIndex_pos {ι : Type*} {N : ι → ℕ} (hN : ∀ i, 0 < N i)
    (p : ι × ℕ) : 0 < divisorWindowIndex N p :=
  Nat.mul_pos (hN p.1) (Nat.succ_pos _)

theorem divisorWindow_summable {ι : Type*} (b : ι → ℝ) (N : ι → ℕ) {a : ℝ}
    (ha : 1 < a) (h : Summable (fun i => |b i| / (N i : ℝ) ^ a)) :
    Summable (fun p : ι × ℕ => |b p.1| / (divisorWindowIndex N p : ℝ) ^ a) := by
  have hs := (zeta_positive_indices (w := (a : ℂ)) (by simpa only [ofReal_re] using ha)).summable.norm
  simp_rw [zeta_index_abs _ (Nat.succ_pos _), ofReal_re] at hs
  apply (Summable.mul_of_nonneg h hs
    (fun _ => by positivity) (fun _ => by positivity)).congr
  intro p
  rw [divisorWindowIndex, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

theorem divisorWindow_dirichlet {ι : Type*} (b : ι → ℝ) (N : ι → ℕ) (hN : ∀ i, 0 < N i)
    {w : ℂ} (hw : 1 < w.re) (hb : Summable (fun i => |b i| / (N i : ℝ) ^ w.re)) :
    indexedDirichletSum (fun p : ι × ℕ => b p.1) (divisorWindowIndex N) w =
      indexedDirichletSum b N w * riemannZeta w := by
  have hg := zeta_positive_indices hw
  have hf : Summable (fun i => ‖(b i : ℂ) * (N i : ℂ) ^ (-w)‖) := by
    apply hb.congr
    intro i
    rw [norm_mul, norm_real, Real.norm_eq_abs, zeta_index_abs _ (hN i)]
    ring
  unfold indexedDirichletSum
  rw [← hg.tsum_eq, tsum_mul_tsum_of_summable_norm hf hg.summable.norm]
  apply tsum_congr
  intro p
  have hcast : (divisorWindowIndex N p : ℂ) =
      ((N p.1 : ℝ) : ℂ) * (((p.2 + 1 : ℕ) : ℝ) : ℂ) := by
    simp only [divisorWindowIndex, Nat.cast_mul, ofReal_natCast]
  rw [hcast, mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _) _,
    ofReal_natCast, ofReal_natCast, mul_assoc]

/-- Sum the centered determinant readings with integer indices in `[x/2,x)`. -/
def archivedGaussianRawWindow (x : ℝ) : ℝ :=
  indexedCutoffSum .window (fun p : GaussianIndexFamily × ℕ => gaussianIndexCoefficient p.1)
    (divisorWindowIndex gaussianIndexAddress) x

theorem archivedGaussianRawWindow_measurable : Measurable archivedGaussianRawWindow :=
  indexedCutoffSum_measurable _ _ _

theorem archivedGaussianRawWindow_growth :
    ∃ C ≥ (0 : ℝ), ∀ x ≥ (1 : ℝ), |archivedGaussianRawWindow x| ≤ C * x ^ (2 : ℝ) := by
  let T := ∑' p : GaussianIndexFamily × ℕ, |gaussianIndexCoefficient p.1| /
    (divisorWindowIndex gaussianIndexAddress p : ℝ) ^ (2 : ℝ)
  refine ⟨T, tsum_nonneg (fun _ => by positivity), fun x hx => ?_⟩
  have ht := indexedCutoffSum_abs_le .window
    (fun p : GaussianIndexFamily × ℕ => gaussianIndexCoefficient p.1)
    (divisorWindowIndex gaussianIndexAddress) (divisorWindowIndex_pos gaussianIndexAddress_pos)
    (a := 2) (by norm_num) hx
    (divisorWindow_summable gaussianIndexCoefficient gaussianIndexAddress (by norm_num)
      (gaussianIndexFamily_summable (by norm_num)))
  simpa only [archivedGaussianRawWindow, IndexedCutoff.maxWeight, one_mul, mul_comm, T] using ht

private theorem archivedIndexMellin_integral (w : ℂ) :
    archivedGaussianPrimitiveIndexMellin w =
      ∫ x in Ioi (1 : ℝ), (archivedGaussianPrimitiveIndexRamp x : ℂ) * (x : ℂ) ^ (-w - 1) := by
  change mellin
    (fun t : ℝ => (Ioi (1 : ℝ)).indicator
      (fun x => (archivedGaussianPrimitiveIndexRamp x : ℂ)) t⁻¹) w = _
  rw [mellin_comp_inv]
  simp only [mellin, smul_eq_mul]
  have h : (fun x : ℝ => (x : ℂ) ^ (-w - 1) *
      (Ioi (1 : ℝ)).indicator (fun y => (archivedGaussianPrimitiveIndexRamp y : ℂ)) x) =
        (Ioi (1 : ℝ)).indicator
          (fun x => (archivedGaussianPrimitiveIndexRamp x : ℂ) * (x : ℂ) ^ (-w - 1)) := by
    funext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [indicator_of_mem hx, mul_comm]
    · simp only [indicator_of_notMem hx, mul_zero]
  rw [h, setIntegral_indicator measurableSet_Ioi,
    inter_eq_right.mpr (Set.Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))]

private theorem gaussianIndexFamily_dirichlet {w : ℂ} (hw : 1 < w.re) :
    indexedDirichletSum gaussianIndexCoefficient gaussianIndexAddress w =
      w * (w - 1) * (archivedGaussianPrimitiveIndexMellin w -
        (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w) := by
  have hd := indexedCutoffSum_mellin .ramp gaussianIndexCoefficient gaussianIndexAddress
    gaussianIndexAddress_pos hw (gaussianIndexFamily_summable hw)
  have hpow : (-w - 1).re < -1 := by simp only [sub_re, neg_re, one_re]; linarith
  have h1 := (integrableOn_Ioi_cpow_of_lt hpow (by norm_num : (0 : ℝ) < 1)).const_mul
    (archivedGaussianPrimitiveIndexRamp 1 : ℂ)
  have hconst : ∫ x in Ioi (1 : ℝ),
      (archivedGaussianPrimitiveIndexRamp 1 : ℂ) * (x : ℂ) ^ (-w - 1) =
      (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w := by
    rw [integral_const_mul, integral_Ioi_cpow_of_lt hpow one_pos, ofReal_one, one_cpow,
      sub_add_cancel, div_neg, neg_div, neg_neg, mul_one_div]
  have heq : archivedGaussianPrimitiveIndexMellin w =
      indexedDirichletSum gaussianIndexCoefficient gaussianIndexAddress w / (w * (w - 1)) +
        (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w := by
    rw [archivedIndexMellin_integral]
    calc
      _ = ∫ x in Ioi (1 : ℝ),
          (indexedCutoffSum .ramp gaussianIndexCoefficient gaussianIndexAddress x : ℂ) *
            (x : ℂ) ^ (-w - 1) +
          (archivedGaussianPrimitiveIndexRamp 1 : ℂ) * (x : ℂ) ^ (-w - 1) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        change (archivedGaussianPrimitiveIndexRamp x : ℂ) * (x : ℂ) ^ (-w - 1) =
          (indexedCutoffSum .ramp gaussianIndexCoefficient gaussianIndexAddress x : ℂ) *
            (x : ℂ) ^ (-w - 1) +
          (archivedGaussianPrimitiveIndexRamp 1 : ℂ) * (x : ℂ) ^ (-w - 1)
        rw [gaussianIndexFamily_ramp (mem_Ioi.mp hx).le, ofReal_sub, sub_mul, sub_add_cancel]
      _ = _ := by
        rw [integral_add hd.1 h1, hd.2, hconst]
        simp only [IndexedCutoff.mellinNumerator, IndexedCutoff.mellinDenominator, mul_one]
  obtain ⟨h0,h'⟩ := Deduction.mellin_Gchi_of_ne_one_ne hw
  rw [heq, add_sub_cancel_right, mul_div_cancel₀]
  exact mul_ne_zero h0 h'

/-- The transform of the un-inverted window contains ordinary zeta
times the primitive transform. One factor of (w-1) cancels at one. -/
theorem archivedGaussianRawWindow_mellin {w : ℂ} (hw : 1 < w.re) :
    ∫ x in Ioi (1 : ℝ), (archivedGaussianRawWindow x : ℂ) * (x : ℂ) ^ (-w - 1) =
      (1 - (2 : ℂ) ^ (-w)) * ((w - 1) * riemannZeta w) *
        (archivedGaussianPrimitiveIndexMellin w - (archivedGaussianPrimitiveIndexRamp 1 : ℂ) / w) := by
  unfold archivedGaussianRawWindow
  rw [(indexedCutoffSum_mellin .window
    (fun p : GaussianIndexFamily × ℕ => gaussianIndexCoefficient p.1)
    (divisorWindowIndex gaussianIndexAddress) (divisorWindowIndex_pos gaussianIndexAddress_pos) hw
    (divisorWindow_summable gaussianIndexCoefficient gaussianIndexAddress hw
      (gaussianIndexFamily_summable hw))).2,
    divisorWindow_dirichlet _ _ gaussianIndexAddress_pos hw (gaussianIndexFamily_summable hw),
    gaussianIndexFamily_dirichlet hw, IndexedCutoff.mellinNumerator, IndexedCutoff.mellinDenominator]
  field_simp [(Deduction.mellin_Gchi_of_ne_one_ne hw).1]

#print axioms archivedGaussianRawWindow_growth
#print axioms archivedGaussianRawWindow_mellin

end
end AlpogeSuperZeta
