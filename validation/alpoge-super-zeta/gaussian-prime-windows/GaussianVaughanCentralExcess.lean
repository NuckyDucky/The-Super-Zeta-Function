import GaussianVaughanRationalMainTerm
import GaussianVaughanBoundaryFree

/-! Remove the abelian comparison from the actual inert band. The
remaining count reads the negative marked class against its density. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Filter Finset QuarticModel Set ArtinPrimitiveRootsConjecture
open scoped Classical

noncomputable section

private abbrev H (v : ℝ) : ℂ := archivedGaussianVaughanKernel v
private abbrev splitPrimes := primePart archivedGaussianSplitMangoldt
private abbrev splitPowers := primePowerTail 2 archivedGaussianSplitMangoldt

private theorem split_prime_and_powers :
    splitPrimes + splitPowers = archivedGaussianSplitMangoldt := by
  apply primePart_add_tail_two
  intro n hn
  simp [archivedGaussianSplitMangoldt, vonMangoldt_eq_zero_iff.mpr hn]

private theorem splitPowers_summable {s : ℝ} (hs : 1 / 2 < s) :
    LSeriesSummable splitPowers (s : ℂ) := by
  apply primePowerTail_summable 2 _ (by norm_num : (0 : ℝ) ≤ 4) archivedGaussianSplitMangoldt_norm_le
  · change 0 < s
    linarith
  · change 1 < (2 : ℝ) * s
    linarith

private theorem splitPrimes_summable : LSeriesSummable splitPrimes (2 : ℂ) := by
  have he : (splitPrimes : ℕ → ℂ) = archivedGaussianSplitMangoldt - (splitPowers : ℕ → ℂ) := by
    funext n
    exact eq_sub_of_add_eq (congrArg (fun f : ArithmeticFunction ℂ => f n) split_prime_and_powers)
  rw [he]
  exact (archivedGaussianSplitMangoldt_summable (by norm_num)).sub
    (splitPowers_summable (by norm_num : (1 / 2 : ℝ) < 2))

private theorem real_kernel_sum {f : ArithmeticFunction ℂ} {v : ℝ} (hv : 0 < v)
    (hf : LSeriesSummable f (2 : ℂ)) :
    (dirichletKernelSum f H v).re =
      ∑' n : ℕ, (f n).re * archivedGaussianVaughanKernel (n * v) := by
  obtain ⟨D, _, hK⟩ := archivedGaussianVaughanKernel_powerBound (a := 2) (by norm_num)
  have hK' (u : ℝ) (hu : 0 < u) : ‖H u‖ ≤ D * u ^ (-(2 : ℝ)) := by
    simpa only [H, norm_real, Real.norm_eq_abs] using hK u hu
  have hs := (dirichletKernelSum_summable hv hK' hf).of_norm
  simp only [dirichletKernelSum, Complex.re_tsum hs, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

private theorem split_kernel_eq_prime_add_powers {v : ℝ} (hv : 0 < v) :
    archivedGaussianSplitKernel v =
      dirichletKernelSum splitPrimes H v + dirichletKernelSum splitPowers H v := by
  obtain ⟨D, _, hK⟩ := archivedGaussianVaughanKernel_powerBound (a := 2) (by norm_num)
  have hK' (u : ℝ) (hu : 0 < u) : ‖H u‖ ≤ D * u ^ (-(2 : ℝ)) := by
    simpa only [H, norm_real, Real.norm_eq_abs] using hK u hu
  have hp := (dirichletKernelSum_summable hv hK' splitPrimes_summable).of_norm
  have he := (dirichletKernelSum_summable hv hK'
    (splitPowers_summable (by norm_num : (1 / 2 : ℝ) < 2))).of_norm
  rw [archivedGaussianSplitKernel, ← split_prime_and_powers]
  simpa only [dirichletKernelSum, ArithmeticFunction.add_apply, add_mul] using hp.tsum_add he

private def splitBand (X : ℝ) : ℝ :=
  ∑ p ∈ archivedGaussianVaughanBandPrimes X,
    (splitPrimes p).re * archivedGaussianVaughanKernel (p / X)

private theorem splitBand_main_term (hDir : DirichletLZerosOnLine)
    {a : ℝ} (ha : 1 / 2 < a) (ha₁ : a ≤ 1) :
    ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop,
      |splitBand X - X * (archivedGaussianVaughanMultiplier 1).re| ≤ C * X ^ a := by
  obtain ⟨A, hA, hFull⟩ := archivedGaussianSplitKernel_scaled hDir ha ha₁
  obtain ⟨B, hB, hBand⟩ := gaussianVaughan_prime_restriction_error splitPrimes
    splitPrimes_summable (fun p hp => by simp [primePart, hp])
  obtain ⟨D, hD, hK⟩ := archivedGaussianVaughanKernel_powerBound (a := a) (by linarith)
  have hS := splitPowers_summable ha
  let E := D * ∑' n : ℕ, ‖LSeries.term splitPowers (a : ℂ) n‖
  have hE : 0 ≤ E := mul_nonneg hD (tsum_nonneg fun _ => norm_nonneg _)
  refine ⟨A + B + E, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ), hBand] with X hX hBand
  have hx := zero_lt_one.trans_le hX
  have hv := inv_pos.mpr hx
  let P := (dirichletKernelSum splitPrimes H X⁻¹).re
  let R := (archivedGaussianSplitKernel X⁻¹).re
  let U := X * (archivedGaussianVaughanMultiplier 1).re
  have hP : |splitBand X - P| ≤ B / X := by
    rw [abs_sub_comm]
    dsimp only [P]
    rw [real_kernel_sum hv splitPrimes_summable]
    simpa only [splitBand, ← div_eq_mul_inv] using hBand
  have hR : |R - U| ≤ A * X ^ a := by
    have h := (abs_re_le_norm (archivedGaussianSplitKernel X⁻¹ -
      (X : ℂ) * archivedGaussianVaughanMultiplier 1)).trans (hFull X hX)
    simpa only [R, U, sub_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] using h
  have hT : |P - R| ≤ E * X ^ a := by
    have hK' (u : ℝ) (hu : 0 < u) : ‖H u‖ ≤ D * u ^ (-a) := by
      simpa only [H, norm_real, Real.norm_eq_abs] using hK u hu
    have hBound := dirichletKernelSum_norm_le hv hK' hS
    rw [Real.inv_rpow hx.le, Real.rpow_neg hx.le, inv_inv] at hBound
    rw [abs_sub_comm]
    change |(archivedGaussianSplitKernel X⁻¹).re - P| ≤ _
    rw [split_kernel_eq_prime_add_powers hv, add_re]
    change |P + (dirichletKernelSum splitPowers H X⁻¹).re - P| ≤ _
    rw [add_sub_cancel_left]
    exact (abs_re_le_norm _).trans hBound
  have hXpower : 1 ≤ X ^ a := Real.one_le_rpow hX (by linarith)
  calc
    |splitBand X - U| ≤ |splitBand X - P| + |P - R| + |R - U| :=
      (abs_sub_le _ _ _).trans (add_le_add_left (abs_sub_le _ _ _) _)
    _ ≤ B * X ^ a + E * X ^ a + A * X ^ a :=
      add_le_add (add_le_add (hP.trans ((div_le_self hB hX).trans
        (le_mul_of_one_le_right hB hXpower))) hT) hR
    _ = _ := by ring

/-- The original theta-weighted count of primes with Gaussian weight
`-2`, with the density `1/8` main term for this class. -/
def archivedGaussianVaughanCentralExcess (X : ℝ) : ℝ :=
  (∑ p ∈ archivedGaussianVaughanBandPrimes X,
    if archivedGaussianPrimeWeight p = -2 then
      Real.log (p : ℝ) * archivedGaussianVaughanKernel (p / X) else 0) -
    X * (archivedGaussianVaughanMultiplier 1).re / 8

private theorem eventually_band_above_level :
    ∀ᶠ X : ℝ in atTop,
      1 < X ∧ (archivedGaussianRationalLevel : ℝ) < X / (Real.log X) ^ (1 / 6 : ℝ) := by
  have hRoot := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually
    (eventually_gt_atTop (archivedGaussianRationalLevel : ℝ))
  have hLog := (isLittleO_log_rpow_rpow_atTop (1 / 6 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 2)).def one_pos
  filter_upwards [eventually_gt_atTop (1 : ℝ), hRoot, hLog] with X hX hRoot hLog
  have hx := zero_lt_one.trans hX
  have hL := Real.rpow_pos_of_pos (Real.log_pos hX) (1 / 6 : ℝ)
  have hU : (Real.log X) ^ (1 / 6 : ℝ) ≤ X ^ (1 / 2 : ℝ) := by
    simpa only [Real.norm_of_nonneg hL.le, Real.norm_of_nonneg
      (Real.rpow_nonneg hx.le (1 / 2 : ℝ)), one_mul] using hLog
  refine ⟨hX, hRoot.trans_le ((le_div_iff₀ hL).mpr ?_)⟩
  calc
    _ ≤ X ^ (1 / 2 : ℝ) * X ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hU (Real.rpow_nonneg hx.le _)
    _ = X := by rw [← Real.rpow_add hx, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, Real.rpow_one]

private theorem inertExcess_eq_center_sub_split {X : ℝ} (hX : 1 < X)
    (hStart : (archivedGaussianRationalLevel : ℝ) < X / (Real.log X) ^ (1 / 6 : ℝ)) :
    archivedGaussianVaughanInertExcess X - 4 * archivedGaussianVaughanCentralExcess X =
      (X * (archivedGaussianVaughanMultiplier 1).re - splitBand X) / 2 := by
  let S := archivedGaussianVaughanBandPrimes X
  let w (p : ℕ) := Real.log (p : ℝ) * archivedGaussianVaughanKernel (p / X)
  let r (p : ℕ) := (splitPrimes p).re * archivedGaussianVaughanKernel (p / X)
  let c (p : ℕ) := if archivedGaussianPrimeWeight p = -2 then w p else 0
  let b (p : ℕ) : ℝ := if p % 4 = 1 ∧ rationalNormSign p = 1 then 2 else 0
  have hPt (p : ℕ) (hp : p ∈ S) :
      (biquadraticInertDegreeOneWeight p - b p) * w p = 4 * c p - r p / 2 := by
    obtain ⟨⟨hlo, _⟩, hp'⟩ := (mem_archivedGaussianVaughanBandPrimes hX p).mp hp
    have hbig : archivedGaussianRationalLevel < p := by exact_mod_cast hStart.trans_le hlo
    have h₂ : p ≠ 2 := ne_of_gt ((by decide : (2 : ℕ) ≤ archivedGaussianRationalLevel).trans_lt hbig)
    have hD : p.Coprime 26509772707289 := hp'.coprime_iff_not_dvd.mpr fun h =>
      (not_le_of_gt ((by decide : (26509772707289 : ℕ) ≤ archivedGaussianRationalLevel).trans_lt hbig))
        (Nat.le_of_dvd (by decide) h)
    have hN : p.Coprime archivedGaussianRationalLevel := hp'.coprime_iff_not_dvd.mpr fun h =>
      hbig.not_ge (Nat.le_of_dvd (by decide) h)
    let : Fact p.Prime := ⟨hp'⟩
    have hI := biquadraticInertDegreeOneWeight_eq_if h₂ hD
    have hSplit := archivedGaussianSplitMangoldt_at_prime hp' h₂ hD hN
    have hrp : r p = (if p % 4 = 1 ∧ rationalNormSign p = 1 then 4 else 0) * w p := by
      simp only [r, primePart, ArithmeticFunction.coe_mk, if_pos hp', hSplit]
      by_cases h : p % 4 = 1 ∧ rationalNormSign p = 1
      · simp only [if_pos h]
        change (((4 : ℝ) : ℂ) * (Real.log (p : ℝ) : ℂ)).re * _ = _
        rw [← Complex.ofReal_mul, Complex.ofReal_re]
        dsimp only [w]
        ring
      · simp [h]
    rw [hI, hrp]
    by_cases h : p % 4 = 1 ∧ rationalNormSign p = 1 <;>
      by_cases h' : archivedGaussianPrimeWeight p = -2 <;>
      simp [h, h', b, c]
    all_goals ring
  have hEq : archivedGaussianVaughanInertExcess X =
      4 * (∑ p ∈ S, c p) - (∑ p ∈ S, r p) / 2 := by
    change (∑ p ∈ S, (biquadraticInertDegreeOneWeight p - b p) * w p) = _
    rw [mul_sum, div_eq_mul_inv, sum_mul, ← sum_sub_distrib]
    exact sum_congr rfl fun p hp => by rw [hPt p hp, div_eq_mul_inv]
  rw [hEq]
  change 4 * (∑ p ∈ S, c p) - (∑ p ∈ S, r p) / 2 -
    4 * ((∑ p ∈ S, c p) - X * (archivedGaussianVaughanMultiplier 1).re / 8) =
      (X * (archivedGaussianVaughanMultiplier 1).re - ∑ p ∈ S, r p) / 2
  ring

theorem archivedGaussianVaughanCentralExcess_error (hDir : DirichletLZerosOnLine)
    {a : ℝ} (ha : 1 / 2 < a) (ha₁ : a < 1) :
    ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop,
      |archivedGaussianVaughanInertExcess X - 4 * archivedGaussianVaughanCentralExcess X| ≤
        C * X ^ a := by
  obtain ⟨C, hC, h⟩ := splitBand_main_term hDir ha ha₁.le
  refine ⟨C / 2, by positivity, ?_⟩
  filter_upwards [h, eventually_band_above_level] with X h hX
  rw [inertExcess_eq_center_sub_split hX.1 hX.2, abs_div, abs_sub_comm, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ (C * X ^ a) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by ring

private theorem window_bound_of_eventual_upper_error {f g : ℝ → ℝ}
    (hE : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop, f X ≤ g X + C * X ^ θ)
    (hG : GaussianCutoffWindowBound g) : GaussianCutoffWindowBound f := by
  intro θ hθ hθ'
  obtain ⟨C, hC, hE⟩ := hE θ hθ hθ'
  obtain ⟨X₀, h₀⟩ := eventually_atTop.mp hE
  obtain ⟨δ, hδ, A, hA, hG⟩ := hG θ hθ hθ'
  refine ⟨δ, hδ, A + C, by positivity, fun Y₀ => ?_⟩
  obtain ⟨Y, hY, hy⟩ := hG (max X₀ Y₀)
  refine ⟨Y, (le_max_right _ _).trans hY, fun X hX => ?_⟩
  have hX₀ : X₀ ≤ X := (le_max_left _ _).trans (hY.trans hX.1)
  exact (h₀ X hX₀).trans ((add_le_add_left (hy X hX) _).trans_eq (add_mul _ _ _).symm)

theorem archivedGaussianVaughanCentralExcess_window_iff (hDir : DirichletLZerosOnLine) :
    GaussianCutoffWindowBound archivedGaussianVaughanCentralExcess ↔
      GaussianCutoffWindowBound archivedGaussianVaughanInertExcess := by
  let F := archivedGaussianVaughanInertExcess
  let G := fun X => 4 * archivedGaussianVaughanCentralExcess X
  have h₁ : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop, F X ≤ G X + C * X ^ θ := by
    intro θ hθ hθ'
    obtain ⟨C, hC, h⟩ := archivedGaussianVaughanCentralExcess_error hDir hθ hθ'
    exact ⟨C, hC, h.mono fun X hX => sub_le_iff_le_add'.mp ((le_abs_self _).trans hX)⟩
  have h₂ : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 →
      ∃ C ≥ 0, ∀ᶠ X : ℝ in atTop, G X ≤ F X + C * X ^ θ := by
    intro θ hθ hθ'
    obtain ⟨C, hC, h⟩ := archivedGaussianVaughanCentralExcess_error hDir hθ hθ'
    exact ⟨C, hC, h.mono fun X hX =>
      sub_le_iff_le_add'.mp ((le_abs_self _).trans (by rwa [abs_sub_comm]))⟩
  constructor
  · intro hG
    apply window_bound_of_eventual_upper_error h₁
    intro θ hθ hθ'
    obtain ⟨δ, hδ, C, hC, h⟩ := hG θ hθ hθ'
    refine ⟨δ, hδ, 4 * C, by positivity, fun Y₀ => ?_⟩
    obtain ⟨Y, hY, h⟩ := h Y₀
    refine ⟨Y, hY, fun X hX => ?_⟩
    exact (mul_le_mul_of_nonneg_left (h X hX) (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
      (mul_assoc _ _ _).symm
  · intro hF
    have hG := window_bound_of_eventual_upper_error h₂ hF
    intro θ hθ hθ'
    obtain ⟨δ, hδ, C, hC, h⟩ := hG θ hθ hθ'
    refine ⟨δ, hδ, C / 4, by positivity, fun Y₀ => ?_⟩
    obtain ⟨Y, hY, h⟩ := h Y₀
    refine ⟨Y, hY, fun X hX => ?_⟩
    calc
      _ ≤ (C * X ^ θ) / 4 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by
        rw [mul_comm (archivedGaussianVaughanCentralExcess X) 4]
        exact h X hX)
      _ = _ := by ring

theorem quartic_rh_of_archived_vaughan_central_class_windows
    (hDir : DirichletLZerosOnLine)
    (hpos : ∀ σ : ℝ, 0 < (QuarticRealFormula.completed (σ : ℂ)).re)
    (hcut : GaussianCutoffWindowBound archivedGaussianVaughanCentralExcess) :
    DedekindZetaRH QuarticModel.K :=
  quartic_rh_of_archived_vaughan_inert_windows_by_reflection hDir hpos
    ((archivedGaussianVaughanCentralExcess_window_iff hDir).mp hcut)

#check quartic_rh_of_archived_vaughan_central_class_windows
#print axioms archivedGaussianVaughanCentralExcess_error
#print axioms archivedGaussianVaughanCentralExcess_window_iff
#print axioms quartic_rh_of_archived_vaughan_central_class_windows

end
end AlpogeSuperZeta
