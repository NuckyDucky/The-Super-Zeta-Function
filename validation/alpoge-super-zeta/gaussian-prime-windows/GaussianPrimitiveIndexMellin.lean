import GaussianPrimitiveIndexWindow
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.Floor

/-! The centered common-divisor ramp has the same Gaussian poles as
the original ramp throughout the open half-plane to the right of one half. -/

open scoped Topology

namespace AlpogeSuperZeta

open ArithmeticFunction ArtinPrimitiveRootsConjecture Asymptotics Complex Filter Finset
  MeasureTheory QuarticModel Set
open scoped Classical

noncomputable section

private theorem measurable_indexRampWeight (n : ℕ) :
    Measurable (fun x => indexRampWeight x n) := by
  unfold indexRampWeight
  fun_prop

private theorem measurable_indexFiniteRamp (b : ℕ → ℝ) (N : ℕ → ℕ) :
    Measurable (fun x => ∑ n ∈ range (⌊x⌋₊ + 1), b n * indexRampWeight x (N n)) := by
  let f (n : ℕ) (x : ℝ) :=
    if n ≤ ⌊x⌋₊ then b n * indexRampWeight x (N n) else 0
  have hm (n : ℕ) : Measurable (f n) :=
    Measurable.ite (measurableSet_le measurable_const Nat.measurable_floor)
      (measurable_const.mul (measurable_indexRampWeight _)) measurable_const
  have htsum : Measurable (fun x => ∑' n : ℕ, f n x) := Measurable.tsum hm
  convert htsum using 1
  ext x
  have hsum : HasSum (fun n : ℕ => f n x) (∑ n ∈ range (⌊x⌋₊ + 1), f n x) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    simp only [f, if_neg (fun h => hn (mem_range.mpr (Nat.lt_succ_of_le h)))]
  rw [hsum.tsum_eq]
  apply sum_congr rfl
  intro n hn
  simp only [f, if_pos (Nat.lt_succ_iff.mp (mem_range.mp hn))]

theorem archivedGaussianPrimitiveIndexRamp_measurable :
    Measurable archivedGaussianPrimitiveIndexRamp := by
  have hs := measurable_indexFiniteRamp (fun n => archivedInertIndexWeight n 1) (· + 1)
  have hb := measurable_indexFiniteRamp archivedIndexBaseWeight id
  have ht (f k : ℕ) : Measurable (fun x => ∑' pj : Nat.Primes × ℕ,
      archivedInertIndexWeight pj.1.val f * indexRampWeight x (archivedInertTailIndex f k pj)) :=
    Measurable.tsum fun pj => measurable_const.mul (measurable_indexRampWeight _)
  unfold archivedGaussianPrimitiveIndexRamp
  exact (((measurable_const.mul ((hs.add (ht 1 1)).add (ht 2 0))).sub hb).sub
    (measurable_const.mul measurable_id)).add
    ((measurable_const.mul measurable_id).mul measurable_const)

private theorem archivedFullPrimeRamp_measurable :
    Measurable (gaussianPrimeNormRamp archivedGaussianPrimeWeight) := by
  unfold gaussianPrimeNormRamp
  exact (Complex.continuous_re.measurable.comp (Deduction.measurable_Gchi_ramp _)).add
    (measurable_const.mul measurable_id)

/-- The error against the full ramp has the same growth bound as the
error against the prime-only ramp. -/
theorem archivedGaussianPrimitiveIndexRamp_full_error {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ ≤ 1) :
    ∃ D ≥ 0, ∀ x ≥ (1 : ℝ),
      |archivedGaussianPrimitiveIndexRamp x + gaussianPrimeNormRamp archivedGaussianPrimeWeight x| ≤
        D * x ^ θ := by
  obtain ⟨C, hC, hc⟩ := archivedGaussianPrimitiveIndexRamp_error hθ hθ₁
  obtain ⟨D, hD, hd⟩ := archivedGaussianPrimeOnlyRamp_error hθ hθ₁
  refine ⟨C + D, add_nonneg hC hD, fun x hx => ?_⟩
  calc
    _ = |(archivedGaussianPrimitiveIndexRamp x + archivedGaussianPrimeOnlyRamp x) +
        (gaussianPrimeNormRamp archivedGaussianPrimeWeight x - archivedGaussianPrimeOnlyRamp x)| := by
      congr 1
      ring
    _ ≤ _ := (abs_add_le _ _).trans (by rw [add_mul]; exact add_le_add (hc x hx) (hd x hx))

private def reflectedRamp (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  (Ioi (1 : ℝ)).indicator (fun x => (f x : ℂ)) t⁻¹

private theorem reflectedRamp_analysis {f : ℝ → ℝ} (hf : Measurable f)
    {b C : ℝ} (hC : 0 ≤ C) (hB : ∀ x ≥ (1 : ℝ), |f x| ≤ C * x ^ b) :
    LocallyIntegrableOn (reflectedRamp f) (Ioi 0) ∧
      (∀ a : ℝ, (reflectedRamp f) =O[atTop] (· ^ (-a))) ∧
      (reflectedRamp f) =O[𝓝[>] 0] (· ^ (-b)) := by
  have hm : Measurable (reflectedRamp f) :=
    ((Complex.continuous_ofReal.measurable.comp hf).indicator measurableSet_Ioi).comp measurable_inv
  have hb (t : ℝ) : ‖reflectedRamp f t‖ ≤ ‖C * t ^ (-b)‖ := by
    by_cases h : t⁻¹ ∈ Ioi (1 : ℝ)
    · have ht' : (1 : ℝ) < t⁻¹ := h
      have ht : 0 < t := inv_pos.mp (zero_lt_one.trans ht')
      rw [reflectedRamp, indicator_of_mem h, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hC (Real.rpow_nonneg ht.le _)), Real.rpow_neg ht.le,
        ← Real.inv_rpow ht.le]
      exact hB t⁻¹ ht'.le
    · rw [reflectedRamp, indicator_of_notMem h, norm_zero]
      exact norm_nonneg _
  have hcont : ContinuousOn (fun t : ℝ => C * t ^ (-b)) (Ioi 0) :=
    continuousOn_const.mul (continuousOn_id.rpow_const fun _ ht => Or.inl (mem_Ioi.mp ht).ne')
  refine ⟨(hcont.locallyIntegrableOn measurableSet_Ioi).mono hm.aestronglyMeasurable
    (Eventually.of_forall hb), fun a => ?_, isBigO_iff.mpr ⟨C, ?_⟩⟩
  · apply isBigO_iff.mpr
    refine ⟨0, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have h : t⁻¹ ∉ Ioi (1 : ℝ) := not_lt_of_ge (inv_le_one_of_one_le₀ ht)
    simp [reflectedRamp, indicator_of_notMem h]
  · filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
    simpa only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC] using hb t

private def primitiveIndexError (x : ℝ) : ℝ :=
  archivedGaussianPrimitiveIndexRamp x + gaussianPrimeNormRamp archivedGaussianPrimeWeight x

private theorem primitiveIndexError_analysis {b : ℝ} (hb : 1 / 2 < b) (hb₁ : b ≤ 1) :
    LocallyIntegrableOn (reflectedRamp primitiveIndexError) (Ioi 0) ∧
      (∀ a : ℝ, (reflectedRamp primitiveIndexError) =O[atTop] (· ^ (-a))) ∧
      (reflectedRamp primitiveIndexError) =O[𝓝[>] 0] (· ^ (-b)) := by
  obtain ⟨C, hC, hE⟩ := archivedGaussianPrimitiveIndexRamp_full_error hb hb₁
  exact reflectedRamp_analysis
    (archivedGaussianPrimitiveIndexRamp_measurable.add archivedFullPrimeRamp_measurable) hC hE

private theorem primitiveIndexError_mellin_analytic {w : ℂ} (hw : 1 / 2 < w.re) :
    AnalyticAt ℂ (mellin (reflectedRamp primitiveIndexError)) w := by
  refine ((show DifferentiableOn ℂ (mellin (reflectedRamp primitiveIndexError))
      {z : ℂ | 1 / 2 < z.re} from ?_).analyticOnNhd
        (isOpen_lt continuous_const Complex.continuous_re)) w hw
  intro z hz
  obtain ⟨b, hb, hb'⟩ := exists_between (lt_min (by norm_num : (1 : ℝ) / 2 < 1) hz)
  obtain ⟨hlocal, htop, hbottom⟩ := primitiveIndexError_analysis hb (hb'.le.trans (min_le_left _ _))
  exact (mellin_differentiableAt_of_isBigO_rpow (s := z) hlocal (htop (z.re + 1)) (by linarith)
    hbottom (hb'.trans_le (min_le_right _ _))).differentiableWithinAt

/-- The Mellin transform of the centered ramp on the common-divisor indices. -/
def archivedGaussianPrimitiveIndexMellin (w : ℂ) : ℂ :=
  mellin (reflectedRamp archivedGaussianPrimitiveIndexRamp) w

private theorem archivedFullPrimeRamp_reflected_convergent {w : ℂ} (hw : 2 < w.re) :
    MellinConvergent (reflectedRamp (gaussianPrimeNormRamp archivedGaussianPrimeWeight)) w := by
  obtain ⟨C, hc⟩ := gaussianLogCutoffRamp_growth archivedGaussianPrimeWeight
    archivedGaussianPrimeWeight_abs_le_two
  have hbound (x : ℝ) (hx : 1 ≤ x) :
      |gaussianPrimeNormRamp archivedGaussianPrimeWeight x| ≤ max C 0 * x ^ (2 : ℝ) := by
    have hx' := zero_lt_one.trans_le hx
    have hh := hc (Real.log x) (Real.log_nonneg hx)
    rw [gaussianLogCutoffRamp, Real.exp_log hx', mul_comm (2 : ℝ) (Real.log x),
      ← Real.rpow_def_of_pos hx'] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx'.le _))
  obtain ⟨hlocal, htop, hbottom⟩ :=
    reflectedRamp_analysis archivedFullPrimeRamp_measurable (le_max_right C 0) hbound
  exact mellinConvergent_of_isBigO_rpow (s := w) hlocal (htop (w.re + 1)) (by linarith) hbottom hw

private theorem archivedFullPrimeRamp_mellin {w : ℂ} (hw : 2 < w.re) :
    mellin (reflectedRamp (gaussianPrimeNormRamp archivedGaussianPrimeWeight)) w =
      gaussianPoleFormula w := by
  rw [gaussianLogCutoffRamp_laplace archivedGaussianPrimeWeight
    archivedGaussianPrimeWeight_abs_le_two hw
      (archivedGaussianMangoldt_eq_neg_logDeriv (by linarith))]
  change _ = ∫ u in Ioi (0 : ℝ),
    (gaussianPrimeNormRamp archivedGaussianPrimeWeight (Real.exp u) : ℂ) * exp (-w * u)
  rw [Deduction.poleData_change (fun x => (gaussianPrimeNormRamp archivedGaussianPrimeWeight x : ℂ))]
  unfold reflectedRamp
  rw [mellin_comp_inv]
  simp only [mellin, smul_eq_mul]
  have hi :
      (fun x : ℝ => (x : ℂ) ^ (-w - 1) *
        (Ioi (1 : ℝ)).indicator (fun y => (gaussianPrimeNormRamp archivedGaussianPrimeWeight y : ℂ)) x) =
      (Ioi (1 : ℝ)).indicator
        (fun x => (x : ℂ) ^ (-w - 1) * (gaussianPrimeNormRamp archivedGaussianPrimeWeight x : ℂ)) := by
    funext x
    by_cases hx : x ∈ Ioi (1 : ℝ)
    · simp only [indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  rw [hi]
  rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, sup_eq_right.mpr zero_le_one]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  exact mul_comm _ _

/-- On the half-plane of convergence, the regularized transform of
the original ramp and one absolutely convergent error give the new reading. -/
theorem archivedGaussianPrimitiveIndexMellin_eq {w : ℂ} (hw : 2 < w.re) :
    archivedGaussianPrimitiveIndexMellin w =
      -gaussianPoleFormula w + mellin (reflectedRamp primitiveIndexError) w := by
  obtain ⟨hlocal, htop, hbottom⟩ := primitiveIndexError_analysis (b := 1) (by norm_num) le_rfl
  have hconv := mellinConvergent_of_isBigO_rpow (s := w) hlocal (htop (w.re + 1)) (by linarith) hbottom
    (by linarith : 1 < w.re)
  have hsub := (hasMellin_sub hconv (archivedFullPrimeRamp_reflected_convergent hw)).2
  rw [show (fun t => reflectedRamp primitiveIndexError t -
      reflectedRamp (gaussianPrimeNormRamp archivedGaussianPrimeWeight) t) =
        reflectedRamp archivedGaussianPrimitiveIndexRamp from funext fun t => by
    by_cases h : t⁻¹ ∈ Ioi (1 : ℝ)
    · simp only [reflectedRamp, indicator_of_mem h, primitiveIndexError, ofReal_add]
      ring
    · simp [reflectedRamp, indicator_of_notMem h]] at hsub
  rw [archivedGaussianPrimitiveIndexMellin, hsub, archivedFullPrimeRamp_mellin hw]
  ring

/-- The primitive-index Mellin continuation has a pole at the exact
address of any Gaussian zero to the right of the critical line. -/
theorem archivedGaussianPrimitiveIndexMellin_same_pole :
    ∃ Ψ : ℂ → ℂ,
      (∀ w : ℂ, 2 < w.re → Ψ w = archivedGaussianPrimitiveIndexMellin w) ∧
      (∀ w : ℂ, 1 / 2 < w.re → archivedGaussianFactor w ≠ 0 → AnalyticAt ℂ Ψ w) ∧
      ∀ ρ ∈ gaussianPoles, 1 / 2 < ρ.re →
        ∃ c : ℂ, c ≠ 0 ∧ ∃ a : ℂ → ℂ, AnalyticAt ℂ a ρ ∧
          ∀ᶠ w in 𝓝[≠] ρ, Ψ w = c / (w - ρ) + a w := by
  obtain ⟨Φ, hΦ, hA, hpoles, _⟩ := gaussian_regularized_transform
  refine ⟨fun w => -Φ w + mellin (reflectedRamp primitiveIndexError) w, ?_, ?_, ?_⟩
  · intro w hw
    have hw₁ : w ≠ 1 := fun h => by rw [h, one_re] at hw; linarith
    change -Φ w + mellin (reflectedRamp primitiveIndexError) w = _
    rw [hΦ w hw₁, archivedGaussianPrimitiveIndexMellin_eq hw]
  · intro w hw hn
    have hw₀ : w ≠ 0 := fun h => by rw [h, zero_re] at hw; linarith
    exact (hA w hw₀ hn).neg.add (primitiveIndexError_mellin_analytic hw)
  · intro ρ hρ h
    have h₀ : ρ ≠ 0 := fun eq => by rw [eq, zero_re] at h; linarith
    have h₁ : ρ ≠ 1 := fun eq => quartic_gaussian_one_ne_zero (eq ▸ hρ.2)
    obtain ⟨m, hm, a, ha, he⟩ := hpoles ρ h₀
    have hm₀ : m ≠ 0 := fun hm₀ => (hm.mp hm₀) hρ.2
    refine ⟨(m : ℂ) / (ρ * (ρ - 1)), div_ne_zero (by exact_mod_cast hm₀)
      (mul_ne_zero h₀ (sub_ne_zero.mpr h₁)),
      fun w => -a w + mellin (reflectedRamp primitiveIndexError) w,
      ha.neg.add (primitiveIndexError_mellin_analytic h), ?_⟩
    filter_upwards [he] with w hw
    rw [hw]
    ring

/-- With the cutoff squared, the same pole has address ρ/2 and
the Mellin Jacobian preserves its residue. -/
theorem archivedGaussianPrimitiveIndexMellin_half_address :
    ∃ Ψ : ℂ → ℂ,
      (∀ s : ℂ, 1 < s.re → Ψ s = 2 * archivedGaussianPrimitiveIndexMellin (2 * s)) ∧
      ∀ ρ ∈ gaussianPoles, 1 / 2 < ρ.re →
        ∃ c : ℂ, c ≠ 0 ∧ ∃ a : ℂ → ℂ, AnalyticAt ℂ a (ρ / 2) ∧
          ∀ᶠ s in 𝓝[≠] (ρ / 2), Ψ s = c / (s - ρ / 2) + a s := by
  obtain ⟨Φ, hΦ, _, hpoles⟩ := archivedGaussianPrimitiveIndexMellin_same_pole
  refine ⟨fun s => 2 * Φ (2 * s), fun s hs => ?_, fun ρ hρ hre => ?_⟩
  · have h : 2 < ((2 : ℂ) * s).re := by
      norm_num [Complex.mul_re]
      linarith
    change 2 * Φ (2 * s) = _
    rw [hΦ (2 * s) h]
  · obtain ⟨c, hc, a, ha, he⟩ := hpoles ρ hρ hre
    have h₂ : (2 : ℂ) ≠ 0 := by norm_num
    have hAt : (2 : ℂ) * (ρ / 2) = ρ := by ring
    have hDouble : AnalyticAt ℂ (fun s : ℂ => 2 * s) (ρ / 2) :=
      analyticAt_const.mul analyticAt_id
    have ht : Tendsto (fun s : ℂ => 2 * s) (𝓝[≠] (ρ / 2)) (𝓝[≠] ρ) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, ?_⟩
      · simpa only [hAt] using hDouble.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        change s ≠ ρ / 2 at hs
        change 2 * s ≠ ρ
        intro h
        exact hs ((eq_div_iff h₂).2 (by simpa only [mul_comm s 2] using h))
    have ha' : AnalyticAt ℂ a ((2 : ℂ) * (ρ / 2)) := by simpa only [hAt] using ha
    refine ⟨c, hc, fun s => 2 * a (2 * s), analyticAt_const.mul (ha'.comp hDouble), ?_⟩
    filter_upwards [ht.eventually he] with s hs
    change Φ (2 * s) = _ at hs
    rw [hs, show (2 : ℂ) * s - ρ = 2 * (s - ρ / 2) by ring,
      mul_add, ← mul_div_assoc, mul_div_mul_left _ _ h₂]

#print axioms archivedGaussianPrimitiveIndexRamp_full_error
#print axioms archivedGaussianPrimitiveIndexMellin_eq
#print axioms archivedGaussianPrimitiveIndexMellin_same_pole
#check archivedGaussianPrimitiveIndexMellin_half_address
#print axioms archivedGaussianPrimitiveIndexMellin_half_address

end
end AlpogeSuperZeta
