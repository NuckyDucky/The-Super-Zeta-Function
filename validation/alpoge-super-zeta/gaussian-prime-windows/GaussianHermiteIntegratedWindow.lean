import GaussianHermiteResidueLattice

/-! The exact Hermite reading supplies a one-sided integrated window
condition for the actual quartic, at a single exponent or at every exponent. -/

namespace AlpogeSuperZeta
namespace GaussianQuarticClosure

open ArtinPrimitiveRootsConjecture FieldTarget MeasureTheory QuarticModel Set

noncomputable section

theorem archivedGaussianDyadicMangoldtWindow_le_hermiteValue
    (hDir : DirichletLZerosOnLine) {θ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) :
    ∃ B ≥ (0 : ℝ), ∀ x ≥ 2 * (26509772707289 + 1 : ℝ),
      archivedGaussianDyadicMangoldtWindow x ≤
        4 * archivedGaussianHermiteValueExcess x + B * x ^ θ := by
  obtain ⟨C, hC, hMass⟩ := dyadicFrobeniusLogMass_pair_lower hDir hθ hθ₁
  obtain ⟨D, hD, hError⟩ := archivedGaussianDyadicPrimeWindow_error θ hθ hθ₁
  refine ⟨2 * C + D, by positivity, fun x hx => ?_⟩
  have hx₁ : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2 * (26509772707289 + 1)).trans hx
  have hPrime := (abs_le.mp (hError x hx₁)).2
  rw [archivedGaussianDyadicPrimeWindow_eq_frobenius hx] at hPrime
  rw [archivedGaussianHermiteValueExcess_eq hx, archivedGaussianCentralPrimeExcess]
  linarith only [hPrime, hMass x hx₁]

private theorem hermite_log_window_to_mangoldt (hDir : DirichletLZerosOnLine)
    {θ δ : ℝ} (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ)
    (hWindow : Deduction.WindowHypU (fun u => archivedGaussianHermiteValueExcess (Real.exp u)) θ δ) :
    Deduction.WindowHypU (fun u => archivedGaussianDyadicMangoldtWindow (Real.exp u)) θ δ := by
  obtain ⟨B, hB, hLe⟩ := archivedGaussianDyadicMangoldtWindow_le_hermiteValue hDir hθ hθ₁
  intro η hη U₀
  let X₀ : ℝ := 2 * (26509772707289 + 1)
  let A := 4 + 2 * B * δ / η
  let start := max (max U₀ (Real.log X₀)) (2 * A / η)
  obtain ⟨U, hU, R, hR, hUpper, hArea⟩ := hWindow (η / 2) (by positivity) start
  have hUU₀ : U₀ ≤ U := (le_max_left _ _).trans ((le_max_left _ _).trans hU)
  have hLog : Real.log X₀ ≤ U := (le_max_right _ _).trans ((le_max_left _ _).trans hU)
  have hX₀ : 1 ≤ X₀ := by norm_num [X₀]
  have hU₀ : 0 ≤ U := (Real.log_nonneg hX₀).trans hLog
  let Q (u : ℝ) := 4 * R u + B * Real.exp (θ * u)
  let W := Icc U ((1 + δ) * U)
  have hWeight : (fun u => Q u * Real.exp (-θ * u)) =
      fun u => 4 * (R u * Real.exp (-θ * u)) + B := by
    funext u
    dsimp only [Q]
    rw [add_mul, mul_assoc, mul_assoc B, ← Real.exp_add,
      show θ * u + -θ * u = 0 by ring, Real.exp_zero, mul_one]
  have hFour : IntegrableOn (fun u => 4 * (R u * Real.exp (-θ * u))) W :=
    hR.const_mul 4
  have hConst : IntegrableOn (fun _ : ℝ => B) W := integrableOn_const (by simp [W])
  refine ⟨U, hUU₀, Q, ?_, ?_, ?_⟩
  · rw [hWeight]
    exact hFour.add hConst
  · intro u hu
    obtain ⟨hRu, hER⟩ := hUpper u hu
    have hX : X₀ ≤ Real.exp u := by
      rw [← Real.exp_log (zero_lt_one.trans_le hX₀)]
      exact Real.exp_le_exp.mpr (hLog.trans hu.1)
    have h := hLe (Real.exp u) hX
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm u θ] at h
    exact ⟨by dsimp only [Q]; positivity, h.trans (by dsimp only [Q]; linarith only [hER])⟩
  · have hWidth : U ≤ (1 + δ) * U := by nlinarith [mul_nonneg hδ.le hU₀]
    rw [hWeight, integral_add hFour hConst, integral_const_mul, setIntegral_const,
      Real.volume_real_Icc_of_le hWidth, smul_eq_mul]
    let e := Real.exp ((η / 2) * U)
    have he : (η / 2) * U ≤ e := by linarith [Real.add_one_le_exp ((η / 2) * U)]
    have hAe : A ≤ e := by
      have hSize : 2 * A / η ≤ U := (le_max_right _ _).trans hU
      have hA := (div_le_iff₀ hη).mp hSize
      exact (show A ≤ (η / 2) * U by linarith only [hA]).trans he
    have hBudget : ((1 + δ) * U - U) * B ≤ (2 * B * δ / η) * e := by
      have hMult : 0 ≤ 2 * B * δ / η := by positivity
      calc
        ((1 + δ) * U - U) * B = (2 * B * δ / η) * ((η / 2) * U) := by
          field_simp [hη.ne']; ring
        _ ≤ (2 * B * δ / η) * e := mul_le_mul_of_nonneg_left he hMult
    calc
      4 * (∫ u in W, R u * Real.exp (-θ * u)) + ((1 + δ) * U - U) * B
          ≤ A * e := by dsimp only [A, e, W] at *; linarith only [hArea, hBudget]
      _ ≤ e * e := mul_le_mul_of_nonneg_right hAe (Real.exp_nonneg _)
      _ = Real.exp (η * U) := by dsimp only [e]; rw [← Real.exp_add]; congr 1; ring

/-- A single cofinal integrated estimate bounds the real parts of all
zeros of the archived Gaussian factor by the same exponent. -/
theorem archivedGaussianFactor_re_le_of_hermite_log_window
    (hDir : DirichletLZerosOnLine) {θ δ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ)
    (hWindow : Deduction.WindowHypU (fun u => archivedGaussianHermiteValueExcess (Real.exp u)) θ δ)
    {w : ℂ} (hw : archivedGaussianFactor w = 0) : w.re ≤ θ := by
  by_cases hp : 0 < w.re
  · exact gaussianPole_re_le_of_dyadic_full_log_window hθ hθ₁ hδ
      (hermite_log_window_to_mangoldt hDir hθ hθ₁ hδ hWindow) ⟨hp, hw⟩
  · linarith [le_of_not_gt hp]

theorem quartic_rh_of_archived_gaussian_hermite_log_windows
    (hDir : DirichletLZerosOnLine)
    (hcut : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ > 0,
      Deduction.WindowHypU (fun u => archivedGaussianHermiteValueExcess (Real.exp u)) θ δ) :
    DedekindZetaRH QuarticModel.K := by
  obtain ⟨hR, hB⟩ := cofactors_on_line hDir
  refine archivedQuarticRH_iff_upper_right.mpr ⟨hR, hB, ?_⟩
  intro w hl hr _ hw
  obtain ⟨θ, hθ, hwθ⟩ := exists_between hl
  have hθ₁ := hwθ.trans hr
  obtain ⟨δ, hδ, hW⟩ := hcut θ hθ hθ₁
  have hG := (archivedGaussianFactor_zero_iff_mellin (by linarith)).mpr hw
  exact (not_le_of_gt hwθ) (archivedGaussianFactor_re_le_of_hermite_log_window hDir hθ hθ₁ hδ hW hG)

/-- The positive excess, weighted at the logarithmic coordinate u = log x. -/
def archivedGaussianHermiteWeightedPositive (θ u : ℝ) : ℝ :=
  max 0 (archivedGaussianHermiteValueExcess (Real.exp u)) * Real.exp (-θ * u)

theorem archivedGaussianHermiteWeightedPositive_integrableOn
    {θ U V : ℝ} (hθ : 0 ≤ θ) (hU : Real.log (2 * (26509772707289 + 1)) ≤ U) :
    IntegrableOn (archivedGaussianHermiteWeightedPositive θ) (Icc U V) := by
  classical
  let N : ℕ := ⌊Real.exp V⌋₊ + 1
  let read (u : ℝ) (p : ℕ) : ℝ :=
    if (p.Prime ∧ Real.exp u / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.exp u) ∧
        closurePrimeLabel p = gaussianCentralElement then Real.log (p : ℝ) else 0
  let F (u : ℝ) := ∑ p ∈ Finset.range N, read u p
  have hEq (u : ℝ) (hu : u ∈ Icc U V) :
      archivedGaussianHermiteValueExcess (Real.exp u) = F u - Real.exp u / 16 := by
    have hX : (2 * (26509772707289 + 1) : ℝ) ≤ Real.exp u :=
      (Real.exp_log (by norm_num : (0 : ℝ) < 2 * (26509772707289 + 1))).ge.trans
        (Real.exp_le_exp.mpr (hU.trans hu.1))
    rw [archivedGaussianHermiteValueExcess_eq hX, archivedGaussianCentralPrimeExcess,
      dyadicFrobeniusLogMass, dyadicPrimes, Finset.filter_filter, Finset.sum_filter]
    change (∑ p ∈ Finset.range (⌊Real.exp u⌋₊ + 1), read u p) - _ = _
    congr 1
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ
      (Nat.floor_mono (Real.exp_le_exp.mpr hu.2))))
    intro p _ hp
    have hFloor : ⌊Real.exp u⌋₊ < p := Nat.lt_of_succ_le
      (by simpa only [Finset.mem_range, not_lt] using hp)
    have hP := (Nat.floor_lt (Real.exp_nonneg _)).mp hFloor
    simp [read, not_lt_of_ge hP.le]
  have hRead (p : ℕ) : Measurable fun u => read u p := by
    by_cases hp : p.Prime ∧ closurePrimeLabel p = gaussianCentralElement
    · have hs : MeasurableSet {u : ℝ | Real.exp u / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.exp u} :=
        (measurableSet_le (Real.measurable_exp.div_const 2) measurable_const).inter
          (measurableSet_lt measurable_const Real.measurable_exp)
      simpa only [read, hp.1, hp.2, true_and, and_true] using Measurable.ite hs
        (measurable_const (a := Real.log (p : ℝ))) (measurable_const (a := (0 : ℝ)))
    · have hZero (u : ℝ) : read u p = 0 :=
        if_neg (fun h => hp ⟨h.1.1, h.2⟩)
      exact measurable_const' (fun x y => (hZero x).trans (hZero y).symm)
  have hF : Measurable F := Finset.measurable_sum _ (fun p _ => hRead p)
  let G (u : ℝ) := max 0 (F u - Real.exp u / 16) * Real.exp (-θ * u)
  have hG : Measurable G :=
    (measurable_const.max (hF.sub (Real.measurable_exp.div_const 16))).mul
      (Real.measurable_exp.comp (measurable_id.const_mul (-θ)))
  let S : ℝ := ∑ p ∈ Finset.range N, Real.log (p : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have hBound (u : ℝ) : F u ≤ S := by
    apply Finset.sum_le_sum
    intro p _
    unfold read
    split <;> simp [Real.log_natCast_nonneg]
  have hConst : IntegrableOn (fun _ : ℝ => S * Real.exp (-θ * U)) (Icc U V) :=
    integrableOn_const (by simp)
  have hInt : IntegrableOn G (Icc U V) := hConst.mono' hG.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Icc : MeasurableSet (Icc U V))]
      with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp only [G]; positivity)]
    exact mul_le_mul
      (max_le hS ((sub_le_self _ (by positivity)).trans (hBound u)))
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hu.1 (neg_nonpos.mpr hθ)))
      (Real.exp_nonneg _) hS)
  refine hInt.congr_fun (fun u hu => ?_) measurableSet_Icc
  simp only [G, archivedGaussianHermiteWeightedPositive, hEq u hu]

def ArchivedGaussianHermiteAreaBound (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U ≥ U₀,
    ∫ u in Icc U ((1 + δ) * U), archivedGaussianHermiteWeightedPositive θ u ≤ Real.exp (η * U)

theorem archivedGaussianHermite_log_window_of_positive_area {θ δ : ℝ} (hθ : 0 ≤ θ)
    (hArea : ArchivedGaussianHermiteAreaBound θ δ) :
    Deduction.WindowHypU (fun u => archivedGaussianHermiteValueExcess (Real.exp u)) θ δ := by
  intro η hη U₀
  obtain ⟨U, hU, hI⟩ := hArea η hη (max U₀ (Real.log (2 * (26509772707289 + 1))))
  exact ⟨U, (le_max_left _ _).trans hU, fun u => max 0 (archivedGaussianHermiteValueExcess (Real.exp u)),
    archivedGaussianHermiteWeightedPositive_integrableOn hθ ((le_max_right _ _).trans hU),
    fun _ _ => ⟨le_max_left _ _, le_max_right _ _⟩, hI⟩

theorem archivedGaussianFactor_re_le_of_hermite_positive_area
    (hDir : DirichletLZerosOnLine) {θ δ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ) (hArea : ArchivedGaussianHermiteAreaBound θ δ)
    {w : ℂ} (hw : archivedGaussianFactor w = 0) : w.re ≤ θ :=
  archivedGaussianFactor_re_le_of_hermite_log_window hDir hθ hθ₁ hδ
    (archivedGaussianHermite_log_window_of_positive_area (by linarith) hArea) hw

/-- At one exponent the area bound confines the quartic's nontrivial zeros
to a symmetric band, using the two known cofactors and Gaussian reflection. -/
theorem archivedQuarticZeta_strip_of_hermite_positive_area
    (hDir : DirichletLZerosOnLine) {θ δ : ℝ}
    (hθ : 1 / 2 < θ) (hθ₁ : θ < 1) (hδ : 0 < δ) (hArea : ArchivedGaussianHermiteAreaBound θ δ)
    {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) (hw : archivedQuarticZeta w = 0) :
    1 - θ ≤ w.re ∧ w.re ≤ θ := by
  obtain ⟨hR, hB⟩ := cofactors_on_line hDir
  rcases (archivedQuarticZeta_zero_iff hw₀).mp hw with hζ | hβ | hG
  · have h := hR _ hw₀ hw₁ hζ
    constructor <;> linarith
  · have h := hB _ hw₀ hw₁ hβ
    constructor <;> linarith
  · have hr := archivedGaussianFactor_re_le_of_hermite_positive_area hDir hθ hθ₁ hδ hArea
      ((archivedGaussianFactor_zero_iff_mellin hw₀).mpr hG)
    have hm : 0 < (1 - w).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hl := archivedGaussianFactor_re_le_of_hermite_positive_area hDir hθ hθ₁ hδ hArea
      ((archivedGaussianFactor_zero_iff_mellin hm).mpr ((archivedMellin_functional_equation w).trans hG))
    rw [Complex.sub_re, Complex.one_re] at hl
    exact ⟨by linarith, hr⟩

theorem quartic_rh_of_archived_gaussian_hermite_positive_area
    (hDir : DirichletLZerosOnLine)
    (hcut : ∀ θ : ℝ, 1 / 2 < θ → θ < 1 → ∃ δ > 0, ArchivedGaussianHermiteAreaBound θ δ) :
    DedekindZetaRH QuarticModel.K := by
  apply quartic_rh_of_archived_gaussian_hermite_log_windows hDir
  intro θ hθ hθ₁
  obtain ⟨δ, hδ, hArea⟩ := hcut θ hθ hθ₁
  exact ⟨δ, hδ, archivedGaussianHermite_log_window_of_positive_area (by linarith) hArea⟩

#check archivedGaussianFactor_re_le_of_hermite_log_window
#check quartic_rh_of_archived_gaussian_hermite_log_windows
#print ArchivedGaussianHermiteAreaBound
#check archivedGaussianFactor_re_le_of_hermite_positive_area
#check archivedQuarticZeta_strip_of_hermite_positive_area
#check quartic_rh_of_archived_gaussian_hermite_positive_area
#print axioms archivedGaussianDyadicMangoldtWindow_le_hermiteValue
#print axioms hermite_log_window_to_mangoldt
#print axioms archivedGaussianFactor_re_le_of_hermite_log_window
#print axioms quartic_rh_of_archived_gaussian_hermite_log_windows
#print axioms archivedGaussianHermiteWeightedPositive_integrableOn
#print axioms archivedGaussianHermite_log_window_of_positive_area
#print axioms archivedGaussianFactor_re_le_of_hermite_positive_area
#print axioms archivedQuarticZeta_strip_of_hermite_positive_area
#print axioms quartic_rh_of_archived_gaussian_hermite_positive_area

end
end GaussianQuarticClosure
end AlpogeSuperZeta
