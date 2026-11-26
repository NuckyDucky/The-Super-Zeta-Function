import GaussianSquaredRamp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The squared cutoff is a positive integral average of the strict
prefix. In particular, a prefix error keeps its power bound under this average. -/

namespace AlpogeSuperZeta

open MeasureTheory Set

noncomputable section

def squaredCutoffIntegral (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (2 / x ^ 2) * ∫ t in Ioc (0 : ℝ) x, (x - t) * f t

private theorem descendingLine_integral {a x : ℝ} (h : a ≤ x) :
    ∫ t in Ioc a x, (x - t) = (x - a) ^ 2 / 2 := by
  have hi : IntervalIntegrable (fun t : ℝ => t) volume a x :=
    continuous_id.intervalIntegrable _ _
  rw [← intervalIntegral.integral_of_le h,
    intervalIntegral.integral_sub intervalIntegrable_const hi,
    intervalIntegral.integral_const, integral_id, smul_eq_mul]
  ring

private theorem weightedPrefixTerm_indicator (x : ℝ) (n : ℕ) :
    (fun t => (x - t) * IndexedCutoff.prefix.weight t n) =
      (Ioi (n : ℝ)).indicator (fun t => x - t) := by
  funext t
  by_cases h : (n : ℝ) < t
  · simp [IndexedCutoff.weight, h]
  · simp [IndexedCutoff.weight, h]

private theorem weightedPrefixTerm_integrable (x : ℝ) (n : ℕ) :
    IntegrableOn (fun t => (x - t) * IndexedCutoff.prefix.weight t n) (Ioc 0 x) := by
  rw [weightedPrefixTerm_indicator]
  have h : Integrable (fun t => x - t) (volume.restrict (Ioc 0 x)) :=
    (continuous_const.sub continuous_id).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  exact h.indicator measurableSet_Ioi

private theorem weightedPrefixTerm_integral (x : ℝ) (n : ℕ) :
    ∫ t in Ioc (0 : ℝ) x, (x - t) * IndexedCutoff.prefix.weight t n =
      if (n : ℝ) < x then (x - (n : ℝ)) ^ 2 / 2 else 0 := by
  rw [weightedPrefixTerm_indicator, setIntegral_indicator measurableSet_Ioi]
  have hSet : Ioc (0 : ℝ) x ∩ Ioi (n : ℝ) = Ioc (n : ℝ) x := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨(Nat.cast_nonneg n).trans_lt h.1, h.2⟩, h.1⟩⟩
  rw [hSet]
  by_cases hn : (n : ℝ) < x
  · rw [if_pos hn, descendingLine_integral hn.le]
  · rw [if_neg hn, Ioc_eq_empty hn, setIntegral_empty]

theorem squaredRampWeight_eq_integral {x : ℝ} (hx : 0 < x) (n : ℕ) :
    squaredRampWeight x n = squaredCutoffIntegral (fun t => IndexedCutoff.prefix.weight t n) x := by
  unfold squaredCutoffIntegral squaredRampWeight
  rw [weightedPrefixTerm_integral]
  by_cases hn : (n : ℝ) < x
  · rw [if_pos hn, if_pos hn]
    field_simp
  · simp [hn]

/-- Termwise averaging, with absolute summability on the integration interval. -/
theorem indexedSquaredRamp_eq_integral {ι : Type*} [Countable ι] (b : ι → ℝ)
    (N : ι → ℕ) (hN : ∀ i, 0 < N i) {x a : ℝ} (hx : 1 ≤ x) (ha : 0 ≤ a)
    (hb : Summable fun i => |b i| / (N i : ℝ) ^ a) :
    IntegrableOn (fun t => (x - t) * indexedCutoffSum .prefix b N t) (Ioc 0 x) ∧
      indexedSquaredRamp b N x = squaredCutoffIntegral (indexedCutoffSum .prefix b N) x := by
  have hx₀ : 0 < x := one_pos.trans_le hx
  let F (i : ι) (t : ℝ) := b i * ((x - t) * IndexedCutoff.prefix.weight t (N i))
  have hF (i : ι) : IntegrableOn (F i) (Ioc 0 x) :=
    (weightedPrefixTerm_integrable x (N i)).const_mul _
  have hAbs : Summable (fun i => abs (abs (b i)) / (N i : ℝ) ^ a) := by simpa only [abs_abs] using hb
  have hsum : Summable (fun i => |b i| * IndexedCutoff.prefix.weight x (N i)) :=
    indexedCutoffSum_summable_at .prefix _ N hN ha hx hAbs
  have hNorm : Summable (fun i => ∫ t in Ioc (0 : ℝ) x, ‖F i t‖) := by
    refine (hsum.mul_left (x ^ 2 / 2)).of_nonneg_of_le
      (fun i => integral_nonneg fun t => norm_nonneg (F i t)) (fun i => ?_)
    have hNormTerm : ∫ t in Ioc (0 : ℝ) x, ‖F i t‖ =
        |b i| * (∫ t in Ioc (0 : ℝ) x, (x - t) * IndexedCutoff.prefix.weight t (N i)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      change ‖b i * ((x - t) * IndexedCutoff.prefix.weight t (N i))‖ =
        |b i| * ((x - t) * IndexedCutoff.prefix.weight t (N i))
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg
        (mul_nonneg (sub_nonneg.mpr ht.2) (IndexedCutoff.prefix.weight_nonneg t (N i)))]
    rw [hNormTerm, weightedPrefixTerm_integral]
    by_cases hn : (N i : ℝ) < x
    · simp only [IndexedCutoff.weight, if_pos hn, mul_one]
      rw [mul_comm (x ^ 2 / 2)]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact div_le_div_of_nonneg_right
        (pow_le_pow_left₀ (sub_nonneg.mpr hn.le) (sub_le_self _ (Nat.cast_nonneg _)) _) (by norm_num)
    · simp [IndexedCutoff.weight, hn]
  have hPoint (t : ℝ) : (x - t) * indexedCutoffSum .prefix b N t = ∑' i, F i t := by
    rw [indexedCutoffSum, ← tsum_mul_left]
    apply tsum_congr
    intro i
    dsimp [F]
    ring
  refine ⟨?_, ?_⟩
  · have hI : IntegrableOn (fun t => ∑' i, F i t) (Ioc 0 x) := by
      refine ⟨(AEMeasurable.tsum (fun i => (hF i).1.aemeasurable)).aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      apply lt_of_le_of_lt (lintegral_mono fun _ => enorm_tsum_le_tsum_enorm)
      rw [lintegral_tsum fun i => (hF i).1.aemeasurable.enorm]
      have he (i : ι) : ∫⁻ t in Ioc (0 : ℝ) x, ‖F i t‖ₑ =
          ‖∫ t in Ioc (0 : ℝ) x, ‖F i t‖‖ₑ := by
        dsimp [enorm]
        rw [lintegral_coe_eq_integral _ (hF i).norm, ENNReal.coe_nnreal_eq]
        have hn : 0 ≤ ∫ t in Ioc (0 : ℝ) x, |F i t| :=
          integral_nonneg (fun t : ℝ => abs_nonneg (F i t))
        simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hn]
      rw [funext he]
      exact lt_top_iff_ne_top.mpr
        (ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hNorm.abs))
    exact hI.congr_fun (fun t _ => (hPoint t).symm) measurableSet_Ioc
  · rw [indexedSquaredRamp_eq_sum b N hN ha hx hb, squaredCutoffIntegral]
    simp_rw [hPoint]
    rw [← integral_tsum_of_summable_integral_norm hF hNorm, ← tsum_mul_left]
    apply tsum_congr
    intro i
    rw [squaredRampWeight_eq_integral hx₀, squaredCutoffIntegral]
    have hInt : ∫ t in Ioc (0 : ℝ) x, F i t =
        b i * (∫ t in Ioc (0 : ℝ) x, (x - t) * IndexedCutoff.prefix.weight t (N i)) :=
      integral_const_mul _ _
    rw [hInt]
    ring

theorem squaredCutoffIntegral_sub {x : ℝ} {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun t => (x - t) * f t) (Ioc 0 x))
    (hg : IntegrableOn (fun t => (x - t) * g t) (Ioc 0 x)) :
    squaredCutoffIntegral f x - squaredCutoffIntegral g x =
      squaredCutoffIntegral (fun t => f t - g t) x := by
  unfold squaredCutoffIntegral
  rw [← mul_sub, ← integral_sub hf hg]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t _
  ring

theorem squaredCutoffIntegral_linear {x : ℝ} (hx : 0 < x) (c : ℝ) :
    squaredCutoffIntegral (fun t => t * c) x = x / 3 * c := by
  have he : (fun t : ℝ => (x - t) * (t * c)) = fun t => c * (x * t - t ^ 2) := by
    funext t
    ring
  have h₁ : IntervalIntegrable (fun t : ℝ => x * t) volume 0 x :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  have h₂ : IntervalIntegrable (fun t : ℝ => t ^ 2) volume 0 x :=
    (continuous_pow 2).intervalIntegrable _ _
  rw [squaredCutoffIntegral, he, ← intervalIntegral.integral_of_le hx.le,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub h₁ h₂,
    intervalIntegral.integral_const_mul, integral_id, integral_pow]
  norm_num
  field_simp
  ring

theorem squaredCutoffIntegral_error {x θ D : ℝ} (hx : 0 < x) (hθ : 0 ≤ θ) (hD : 0 ≤ D)
    {f g : ℝ → ℝ}
    (hf : IntegrableOn (fun t => (x - t) * f t) (Ioc 0 x))
    (hg : IntegrableOn (fun t => (x - t) * g t) (Ioc 0 x))
    (hError : ∀ t ∈ Ioc (0 : ℝ) x, |f t - g t| ≤ D * t ^ θ) :
    |squaredCutoffIntegral f x - squaredCutoffIntegral g x| ≤ D * x ^ θ := by
  have hSub : IntegrableOn (fun t => (x - t) * (f t - g t)) (Ioc 0 x) := by
    exact (hf.sub hg).congr_fun (fun t _ => (mul_sub (x - t) (f t) (g t)).symm) measurableSet_Ioc
  have hMajor : IntegrableOn (fun t => (D * x ^ θ) * (x - t)) (Ioc 0 x) :=
    (continuous_const.mul (continuous_const.sub continuous_id)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hNorm : |∫ t in Ioc (0 : ℝ) x, (x - t) * (f t - g t)| ≤
      ∫ t in Ioc (0 : ℝ) x, |(x - t) * (f t - g t)| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
      (μ := volume.restrict (Ioc (0 : ℝ) x)) (fun t => (x - t) * (f t - g t))
  have hMajorant : ∫ t in Ioc (0 : ℝ) x, |(x - t) * (f t - g t)| ≤
      ∫ t in Ioc (0 : ℝ) x, (D * x ^ θ) * (x - t) := by
    have hAbs : IntegrableOn (fun t => |(x - t) * (f t - g t)|) (Ioc 0 x) := hSub.norm
    apply setIntegral_mono_on hAbs hMajor measurableSet_Ioc
    intro t ht
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2), mul_comm (D * x ^ θ)]
    exact mul_le_mul_of_nonneg_left ((hError t ht).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht.1.le ht.2 hθ) hD)) (sub_nonneg.mpr ht.2)
  rw [squaredCutoffIntegral_sub hf hg, squaredCutoffIntegral, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ 2 / x ^ 2)]
  calc
    _ ≤ (2 / x ^ 2) * ∫ t in Ioc (0 : ℝ) x, (D * x ^ θ) * (x - t) :=
      mul_le_mul_of_nonneg_left (hNorm.trans hMajorant) (by positivity)
    _ = _ := by
      rw [integral_const_mul, descendingLine_integral hx.le, sub_zero]
      field_simp

#print axioms indexedSquaredRamp_eq_integral
#print axioms squaredCutoffIntegral_linear
#print axioms squaredCutoffIntegral_error

end
end AlpogeSuperZeta
