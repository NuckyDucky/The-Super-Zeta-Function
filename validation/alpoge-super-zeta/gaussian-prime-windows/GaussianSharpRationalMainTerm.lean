import GaussianShortPerronBounds
import GaussianVaughanRationalSplit
import GaussianVaughanPrimeInversion

/-! Shift the four-character reading past the principal pole, with the
dependence on the width of the short cutoff explicit on the left line. -/

namespace AlpogeSuperZeta

open ArithmeticFunction Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

private abbrev M := shortPerronMultiplier
private abbrev S := archivedGaussianSplitRegularSum

private def reference (v : ℝ) : ℂ := (v : ℂ) ^ (-1 : ℂ) • perronTent 1 v

private theorem reference_hasMellin {z : ℂ} (hz : 1 < z.re) :
    HasMellin reference z (1 / ((z - 1) * z)) := by
  have h := perronTent_hasMellin one_pos (z := z - 1) (by rw [sub_re, one_re]; linarith)
  have he : z + (-1) = z - 1 := by ring
  refine ⟨(MellinConvergent.cpow_smul (a := (-1 : ℂ))).mpr (he ▸ h.1), ?_⟩
  unfold reference
  rw [mellin_cpow_smul, he, h.2, ofReal_one, one_cpow, sub_add_cancel]

private def principalNumerator (d : ℝ) (z : ℂ) : ℂ := M d z - M d 1 / z

private def remainder (d : ℝ) := dslope (principalNumerator d) 1

private def residualMellin (d : ℝ) (z : ℂ) : ℂ := M d z * S z + remainder d z

private theorem principalNumerator_one (d : ℝ) : principalNumerator d 1 = 0 := by
  simp [principalNumerator]

private theorem principalNumerator_analytic {d : ℝ} (hd : 0 < d)
    {z : ℂ} (hz : 0 < z.re) : AnalyticAt ℂ (principalNumerator d) z :=
  (shortPerronMultiplier_analytic d hd hz).sub
    (analyticAt_const.div analyticAt_id (fun h => by simp [h] at hz))

private theorem remainder_analytic {d : ℝ} (hd : 0 < d) {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (remainder d) z := by
  by_cases h : z = 1
  · subst z
    exact Deduction.poleData_dslope (principalNumerator_analytic hd hz)
  have he : remainder d =ᶠ[𝓝 z] fun w => principalNumerator d w / (w - 1) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show z ∈ ({1} : Set ℂ)ᶜ from h)] with w hw
    rw [remainder, dslope_of_ne _ hw, slope_def_field, principalNumerator_one, sub_zero, div_eq_inv_mul]
  exact ((principalNumerator_analytic hd hz).div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr h)).congr he.symm

private theorem residualMellin_analytic (hDir : DirichletLZerosOnLine)
    {d : ℝ} (hd : 0 < d) {z : ℂ} (hz : 1 / 2 < z.re) :
    AnalyticAt ℂ (residualMellin d) z :=
  ((shortPerronMultiplier_analytic d hd (by linarith)).mul
    (archivedGaussianSplitRegularSum_analytic hDir hz)).add
    (remainder_analytic hd (by linarith))

def archivedGaussianSharpPerron (d v : ℝ) : ℂ :=
  dirichletKernelSum archivedGaussianSplitMangoldt (shortPerronKernel d) v

private theorem residual_hasMellin {d : ℝ} (hd : 0 < d)
    {z : ℂ} (hz : 1 < z.re) :
    HasMellin (fun v => archivedGaussianSharpPerron d v - M d 1 * reference v)
      z (residualMellin d z) := by
  have hR : HasMellin (archivedGaussianSharpPerron d) z
      (M d z * LSeries archivedGaussianSplitMangoldt z) :=
    dirichletKernelSum_hasMellin archivedGaussianSplitMangoldt
      (shortPerronKernel_hasMellin hd (one_pos.trans hz))
      (archivedGaussianSplitMangoldt_summable (by simpa using hz))
  have hE := reference_hasMellin hz
  have he := hasMellin_const_smul hE.1 (M d 1)
  have hf := hasMellin_sub hR.1 he.1
  refine ⟨hf.1, ?_⟩
  rw [show (fun v => archivedGaussianSharpPerron d v - M d 1 * reference v) =
      (fun v => archivedGaussianSharpPerron d v - M d 1 • reference v) from rfl,
    hf.2, he.2, hR.2, hE.2]
  have hz₁ : z ≠ 1 := by rintro rfl; norm_num at hz
  rw [archivedGaussianSplitMangoldt_LSeries_eq_regular hz, residualMellin, remainder, dslope_of_ne _ hz₁,
    slope_def_field, principalNumerator_one, sub_zero, principalNumerator]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
  ring

private theorem logarithmic_part_bound (hDir : DirichletLZerosOnLine) {a e : ℝ}
    (ha : 1 / 2 < a) (ha₁ : a ≤ 1) (he : 0 < e) (he₁ : e ≤ 1) :
    ∃ C ≥ 0, ∀ d : ℝ, 0 < d → d ≤ 1 → ∀ z : ℂ, a ≤ z.re → z.re ≤ 3 / 2 →
      ‖M d z * S z‖ ≤ C * d ^ (-e) / (1 + |z.im|) ^ (1 + e / 2) := by
  obtain ⟨A, hA, hS⟩ := archivedGaussianSplitRegularSum_logBound hDir ha ha₁
  let B := A * (1 + (e / 2)⁻¹)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨81 * B, by positivity, fun d hd hd₁ z hl hr => ?_⟩
  let U := 1 + |z.im|
  have hU₁ : 1 ≤ U := by dsimp [U]; linarith [abs_nonneg z.im]
  have hU : 0 < U := one_pos.trans_le hU₁
  have hS' : ‖S z‖ ≤ B * U ^ (e / 2) := by
    calc
      _ ≤ A * (1 + Real.log U) := hS z hl hr
      _ ≤ A * ((1 + (e / 2)⁻¹) * U ^ (e / 2)) :=
        mul_le_mul_of_nonneg_left (one_add_log_le_power hU₁ (by linarith)) hA.le
      _ = _ := by dsimp [B]; ring
  rw [norm_mul]
  calc
    _ ≤ ((81 * d ^ (-e)) / U ^ (1 + e)) * (B * U ^ (e / 2)) :=
      mul_le_mul (shortPerronMultiplier_norm_le hd hd₁ he he₁ (ha.le.trans hl) hr)
        hS' (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [show (1 + e : ℝ) = (1 + e / 2) + e / 2 by ring, Real.rpow_add hU]
      field_simp [ne_of_gt (Real.rpow_pos_of_pos hU (e / 2)),
        ne_of_gt (Real.rpow_pos_of_pos hU (1 + e / 2))]
      ring

private theorem remainder_height_bound {d B : ℝ} (hd : 0 < d) (hd₁ : d ≤ 1)
    {z : ℂ} (hL : 1 / 2 ≤ z.re) (hR : z.re ≤ 3 / 2)
    (hDist : 1 + |z.im| ≤ B * ‖z - 1‖) :
    ‖remainder d z‖ ≤ (18 * B) / (1 + |z.im|) ^ 2 := by
  let U := 1 + |z.im|
  have hU : 0 < U := by dsimp [U]; positivity
  have hZ := one_add_abs_im_le_three_norm hL
  have hz : 0 < ‖z‖ := by change U ≤ 3 * ‖z‖ at hZ; linarith
  have hz₁ : z ≠ 1 := by
    rintro rfl
    rw [sub_self, norm_zero, mul_zero] at hDist
    exact (not_le_of_gt hU) hDist
  have hz₁' : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz₁)
  have hM₁ : ‖M d 1‖ ≤ 2 := by
    change ‖shortPerronMultiplier d 1‖ ≤ 2
    rw [shortPerronMultiplier_one hd, norm_real, Real.norm_of_nonneg (by positivity)]
    linarith
  have hN : ‖principalNumerator d z‖ ≤ 18 / U := by
    calc
      _ ≤ ‖M d z‖ + ‖M d 1 / z‖ := norm_sub_le _ _
      _ ≤ 12 / U + 6 / U := by
        refine add_le_add (shortPerronMultiplier_two_bounds hd hd₁ hL hR).1 ?_
        rw [norm_div]
        exact (div_le_div_of_nonneg_right hM₁ hz.le).trans
          ((div_le_div_iff₀ hz hU).mpr (by linarith [show U ≤ 3 * ‖z‖ from hZ]))
      _ = _ := by ring
  rw [remainder, dslope_of_ne _ hz₁, slope_def_field, principalNumerator_one,
    sub_zero, norm_div]
  calc
    _ ≤ (18 / U) / ‖z - 1‖ := div_le_div_of_nonneg_right hN hz₁'.le
    _ = 18 / (U * ‖z - 1‖) := div_div _ _ _
    _ ≤ _ := by
      change _ ≤ (18 * B) / U ^ 2
      exact (div_le_div_iff₀ (mul_pos hU hz₁') (pow_pos hU 2)).mpr (by
        nlinarith [mul_le_mul_of_nonneg_left (show U ≤ B * ‖z - 1‖ from hDist)
          (show 0 ≤ 18 * U by positivity)])

private theorem remainder_strip_bound {a d : ℝ} (ha : 1 / 2 < a)
    (hd : 0 < d) (hd₁ : d ≤ 1) :
    ∃ C ≥ 0, ∀ z : ℂ, a ≤ z.re → z.re ≤ 3 / 2 →
      ‖remainder d z‖ ≤ C / (1 + |z.im|) ^ 2 := by
  let Q := reProdIm (Icc a (3 / 2 : ℝ)) (Icc (-1 : ℝ) 1)
  have hQ : IsCompact Q := isCompact_Icc.reProdIm isCompact_Icc
  have hCont : ContinuousOn (fun z => ‖remainder d z‖) Q := by
    intro z hz
    have h := remainder_analytic (z := z) hd (by linarith [(mem_reProdIm.mp hz).1.1])
    exact h.continuousAt.norm.continuousWithinAt
  obtain ⟨D, hD⟩ := hQ.bddAbove_image hCont
  let C := max 36 (4 * max 0 D)
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 36).trans (le_max_left _ _)
  refine ⟨C, hC, fun z hl hr => ?_⟩
  let U := 1 + |z.im|
  have hU : 0 < U := by dsimp [U]; positivity
  by_cases ht : 1 ≤ |z.im|
  · have hI := abs_im_le_norm (z - 1)
    rw [sub_im, one_im, sub_zero] at hI
    have hDist : U ≤ 2 * ‖z - 1‖ := by dsimp [U]; linarith
    exact (remainder_height_bound hd hd₁ (ha.le.trans hl) hr hDist).trans
      (div_le_div_of_nonneg_right (by norm_num; exact le_max_left _ _) (pow_nonneg hU.le 2))
  · have hz : z ∈ Q := mem_reProdIm.mpr ⟨⟨hl, hr⟩, abs_le.mp (le_of_not_ge ht)⟩
    have hB := hD (mem_image_of_mem _ hz)
    have h₂ : U ≤ 2 := by dsimp [U]; linarith
    have hS : 0 ≤ 2 + U := by positivity
    have h₄ : U ^ 2 ≤ 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr h₂) hS]
    apply (le_div_iff₀ (pow_pos hU 2)).mpr
    calc
      _ ≤ (max 0 D) * 4 :=
        mul_le_mul (hB.trans (le_max_right _ _)) h₄ (pow_nonneg hU.le 2) (le_max_left _ _)
      _ ≤ C := by rw [mul_comm]; exact le_max_right _ _

private theorem residual_continuousAt {d v : ℝ} (hd : 0 < d) (hd₁ : d ≤ 1) (hv : 0 < v) :
    ContinuousAt (fun u => archivedGaussianSharpPerron d u - M d 1 * reference u) v := by
  have hS : ContinuousAt (archivedGaussianSharpPerron d) v :=
    dirichletKernelSum_continuousAt_of_power (s := 2) (by norm_num) (by norm_num) hv
      (shortPerronKernel_continuous d).continuousOn (shortPerronKernel_norm_le_power hd hd₁)
      (archivedGaussianSplitMangoldt_summable (by norm_num))
  have hcp : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (-1 : ℂ)) v :=
    (continuousAt_cpow_const (ofReal_mem_slitPlane.mpr hv)).comp continuous_ofReal.continuousAt
  have hT : Continuous (perronTent 1) := by unfold perronTent; fun_prop
  exact hS.sub (continuousAt_const.mul (hcp.mul hT.continuousAt))

theorem archivedGaussianSharpPerron_main_term (hDir : DirichletLZerosOnLine) {a e : ℝ}
    (ha : 1 / 2 < a) (ha₁ : a < 1) (he : 0 < e) (he₁ : e ≤ 1) :
    ∃ A ≥ 0, ∀ d : ℝ, 0 < d → d ≤ 1 → ∀ v > (0 : ℝ),
      ‖archivedGaussianSharpPerron d v - M d 1 * reference v‖ ≤ A * d ^ (-e) * v ^ (-a) := by
  obtain ⟨C, hC, hB⟩ := logarithmic_part_bound hDir ha ha₁.le he he₁
  let r := 1 + e / 2
  have hr : 1 < r := by dsimp [r]; linarith
  let B := 1 + (1 - a)⁻¹
  have hB₀ : 0 ≤ B := by dsimp [B]; positivity
  let J := ∫ t : ℝ, ((1 + |t|) ^ r)⁻¹
  have hJ : 0 ≤ J := integral_nonneg fun t => by positivity
  let A := (1 / (2 * Real.pi)) * ((C + 18 * B) * J)
  refine ⟨A, by dsimp [A]; positivity, fun d hd hd₁ v hv => ?_⟩
  obtain ⟨D, hD, hRem⟩ := remainder_strip_bound ha hd hd₁
  let b : ℝ := 3 / 2
  have hab : a ≤ b := by dsimp [b]; linarith
  have hA (z : ℂ) (hl : a ≤ z.re) (_ : z.re ≤ b) : DifferentiableAt ℂ (residualMellin d) z :=
    (residualMellin_analytic hDir hd (ha.trans_le hl)).differentiableAt
  have hWeaken (z : ℂ) (L : ℝ) (hL : 0 ≤ L) :
      L / (1 + |z.im|) ^ 2 ≤ L * d ^ (-e) / (1 + |z.im|) ^ r := by
    let U := 1 + |z.im|
    have hU₁ : 1 ≤ U := by dsimp [U]; linarith [abs_nonneg z.im]
    have hU : 0 < U := one_pos.trans_le hU₁
    have hd' : 1 ≤ d ^ (-e) := by
      rw [← Real.rpow_zero d]
      exact Real.rpow_le_rpow_of_exponent_ge hd hd₁ (by linarith)
    have hP : U ^ r ≤ U ^ 2 := by
      rw [← Real.rpow_two]
      exact Real.rpow_le_rpow_of_exponent_le hU₁ (by dsimp [r]; linarith)
    calc
      _ ≤ L / U ^ r := div_le_div_of_nonneg_left hL (Real.rpow_pos_of_pos hU r) hP
      _ ≤ _ := div_le_div_of_nonneg_right (le_mul_of_one_le_right hL hd') (by positivity)
  have hDecay (z : ℂ) (hl : a ≤ z.re) (hu : z.re ≤ b) :
      ‖residualMellin d z‖ ≤ ((C + D) * d ^ (-e)) / (1 + |z.im|) ^ r := by
    refine (norm_add_le _ _).trans ?_
    exact (add_le_add (hB d hd hd₁ z hl hu)
      ((hRem z hl hu).trans (hWeaken z D hD))).trans_eq (by rw [← add_div, ← add_mul])
  have hI := verticalIntegrable_of_power_decay hr le_rfl hab hA hDecay
  have hRight := verticalIntegrable_of_power_decay hr hab le_rfl hA hDecay
  let f := fun u => archivedGaussianSharpPerron d u - M d 1 * reference u
  have hconv : MellinConvergent f (b : ℂ) := (residual_hasMellin hd (by norm_num [b])).1
  have hEq (t : ℝ) : mellin f ((b : ℂ) + (t : ℂ) * I) =
      residualMellin d ((b : ℂ) + (t : ℂ) * I) :=
    (residual_hasMellin hd (by norm_num [b, mul_re])).2
  have hInt : VerticalIntegrable (mellin f) b := hRight.congr (Eventually.of_forall fun t => (hEq t).symm)
  change ‖f v‖ ≤ _
  rw [← mellinInv_mellin_eq _ _ hv hconv hInt (residual_continuousAt hd hd₁ hv),
    show mellinInv b (mellin f) v = mellinInv b (residualMellin d) v by simp only [mellinInv, hEq],
    ← mellinInv_eq_of_power_decay hr hv hab hA hDecay]
  have hLine (t : ℝ) :
      ‖residualMellin d ((a : ℂ) + (t : ℂ) * I)‖ ≤
        ((C + 18 * B) * d ^ (-e)) * ((1 + |t|) ^ r)⁻¹ := by
    let z := (a : ℂ) + (t : ℂ) * I
    have hz : z.re = a := by simp [z, mul_re]
    have hi : z.im = t := by simp [z, mul_im]
    have hR : z.re ≤ 3 / 2 := by rw [hz]; linarith
    have hI := abs_im_le_norm (z - 1)
    rw [sub_im, one_im, sub_zero] at hI
    have hRe : 1 - a ≤ ‖z - 1‖ := by
      have h := abs_re_le_norm (z - 1)
      rw [sub_re, one_re, hz, abs_of_neg (by linarith : a - 1 < 0)] at h
      linarith
    have hUI : 1 ≤ (1 - a)⁻¹ * ‖z - 1‖ := by
      rw [← div_eq_inv_mul]
      exact (one_le_div (by linarith : 0 < 1 - a)).mpr hRe
    have hDist : 1 + |z.im| ≤ B * ‖z - 1‖ := by dsimp [B]; rw [add_mul, one_mul]; linarith
    change ‖residualMellin d z‖ ≤ _
    have h := (norm_add_le _ _).trans
      (add_le_add (hB d hd hd₁ z hz.ge hR)
        ((remainder_height_bound hd hd₁ (by rw [hz]; linarith) hR hDist).trans
          (hWeaken z (18 * B) (by positivity))))
    rw [← add_div, ← add_mul, hi, div_eq_mul_inv] at h
    exact h
  have hDom := (integrable_inverse_add_abs_rpow hr).const_mul ((C + 18 * B) * d ^ (-e))
  have hJ' := integral_mono hI.norm hDom hLine
  rw [integral_const_mul] at hJ'
  calc
    _ ≤ ((1 / (2 * Real.pi)) *
        ∫ t : ℝ, ‖residualMellin d ((a : ℂ) + (t : ℂ) * I)‖) * v ^ (-a) :=
      norm_mellinInv_le hv hI
    _ ≤ _ := by
      refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ' (by positivity))
        (Real.rpow_nonneg hv.le _)).trans_eq ?_
      dsimp only [A, J]
      ring

theorem archivedGaussianSharpPerron_scaled (hDir : DirichletLZerosOnLine) {a e : ℝ}
    (ha : 1 / 2 < a) (ha₁ : a < 1) (he : 0 < e) (he₁ : e ≤ 1) :
    ∃ C ≥ 0, ∀ y ≥ (1 : ℝ),
      ‖archivedGaussianSharpPerron (1 / (2 * y)) y⁻¹ - (y : ℂ)‖ ≤ C * y ^ (a + e) := by
  obtain ⟨A, hA, hE⟩ := archivedGaussianSharpPerron_main_term hDir ha ha₁ he he₁
  refine ⟨A * (2 : ℝ) ^ e + 1, by positivity, fun y hy => ?_⟩
  have hy₀ := one_pos.trans_le hy
  let d := 1 / (2 * y)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd₁ : d ≤ 1 := (div_le_one (by positivity : 0 < 2 * y)).mpr (by linarith)
  have hv : 0 < y⁻¹ := inv_pos.mpr hy₀
  have hM := hE d hd hd₁ y⁻¹ hv
  have hRef : reference y⁻¹ = ((y - 1 : ℝ) : ℂ) := by
    have h : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy
    rw [reference, perronTent, max_eq_left (sub_nonneg.mpr h), cpow_neg_one, ofReal_inv,
      inv_inv, smul_eq_mul, ← ofReal_mul]
    suffices y * (1 - y⁻¹) = y - 1 by exact_mod_cast this
    rw [mul_sub, mul_one, mul_inv_cancel₀ hy₀.ne']
  have hE' : ‖M d 1 * reference y⁻¹ - (y : ℂ)‖ ≤ 1 := by
    change ‖shortPerronMultiplier d 1 * reference y⁻¹ - (y : ℂ)‖ ≤ 1
    rw [shortPerronMultiplier_one hd, hRef, ← ofReal_mul, ← ofReal_sub, norm_real, Real.norm_eq_abs]
    rw [abs_le]
    have hD : d * y = 1 / 2 := by dsimp [d]; field_simp
    constructor <;> nlinarith [mul_nonneg hd.le (sub_nonneg.mpr hy)]
  have hdPow : d ^ (-e) = (2 : ℝ) ^ e * y ^ e := by
    dsimp [d]
    rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      Real.mul_rpow (by norm_num) hy₀.le]
  rw [Real.inv_rpow hy₀.le, Real.rpow_neg hy₀.le, inv_inv, hdPow] at hM
  calc
    _ ≤ ‖archivedGaussianSharpPerron d y⁻¹ - M d 1 * reference y⁻¹‖ +
        ‖M d 1 * reference y⁻¹ - (y : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub ..
    _ ≤ A * ((2 : ℝ) ^ e * y ^ e) * y ^ a + 1 := add_le_add hM hE'
    _ ≤ _ := by
      rw [Real.rpow_add hy₀, add_mul, one_mul]
      have h := Real.one_le_rpow hy (show 0 ≤ a + e by linarith)
      rw [Real.rpow_add hy₀] at h
      nlinarith only [h]

#print axioms archivedGaussianSharpPerron_main_term
#print axioms archivedGaussianSharpPerron_scaled

end
end AlpogeSuperZeta
