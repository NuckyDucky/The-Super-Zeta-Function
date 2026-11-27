import DottieHeightBand

/-! Calculate the admissible height shift from the margin we want to
retain, using a centered norm bound for Cauchy's derivative estimate. -/

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection

noncomputable section

private theorem height_budget_split {a M d : ℝ} (ha : 0 < a) (hM : 0 < M) (hd : 0 < d) :
    a * d / (M + a) + M * d / (M + a) = d ∧
    (M / (M * d / (M + a))) * (a * d / (M + a)) = a := by
  have hsum : 0 < M + a := add_pos hM ha
  constructor <;> field_simp [hsum.ne', hM.ne', hd.ne']
  all_goals ring

/-- The anchor margin is `m`, and `μ` is the part to keep at every new
height. The derivative estimate can use the norm after subtracting any
constant `k`. -/
theorem dottie_calculated_height_sign {H : ℂ → ℂ} {k : ℂ}
    {T₀ T R M m μ : ℝ} {n : ℕ}
    (hR : dottieScaledRadius n < R) (hM : 0 < M) (hgap : μ < m)
    (hH : DifferentiableOn ℂ H (closedBall (dottieScaledRightCenter T₀ n) R))
    (houter : ∀ z ∈ sphere (dottieScaledRightCenter T₀ n) R, ‖H z - k‖ ≤ M)
    (hsign : ∀ z ∈ sphere (dottieScaledRightCenter T₀ n) (dottieScaledRadius n),
      (H z).im ≤ -m)
    (hT : |T - T₀| ≤ (m - μ) * (R - dottieScaledRadius n) / (M + (m - μ))) :
    ∀ z ∈ sphere (dottieScaledRightCenter T n) (dottieScaledRadius n), (H z).im ≤ -μ := by
  let r := dottieScaledRadius n
  let a := m - μ
  let d := R - r
  let δ := a * d / (M + a)
  let ρ := M * d / (M + a)
  have ha : 0 < a := sub_pos.mpr hgap
  have hd : 0 < d := sub_pos.mpr hR
  have hρ : 0 < ρ := div_pos (mul_pos hM hd) (add_pos hM ha)
  have hsplit : δ + ρ = d ∧ (M / ρ) * δ = a := height_budget_split ha hM hd
  have hs : |T - T₀| ≤ δ := hT
  have hroom : r + |T - T₀| + ρ ≤ R := by
    have hsum := hsplit.1
    change δ + ρ = R - r at hsum
    linarith only [hs, hsum]
  have hHs := hH.sub (differentiableOn_const k)
  have hsign' (z : ℂ)
      (hz : z ∈ sphere (dottieScaledRightCenter T₀ n) (dottieScaledRadius n)) :
      (H z - k).im ≤ -(m + k.im) := by
    rw [sub_im]
    linarith only [hsign z hz]
  intro z hz
  have h := dottie_shifted_boundary_sign hρ hroom hHs houter hsign' z hz
  change (H z - k).im ≤ -(m + k.im) + (M / ρ) * |T - T₀| at h
  rw [sub_im] at h
  have hcost := (mul_le_mul_of_nonneg_left hs (div_nonneg hM.le hρ.le)).trans_eq hsplit.2
  change (M / ρ) * |T - T₀| ≤ m - μ at hcost
  linarith only [h, hcost]

/-- For a relative comparison, subtract the constant `-I` before taking
the outer norm. The resulting bound is the outer relative error itself. -/
theorem dottie_relative_calculated_height_band_nonzero
    {F P : ℂ → ℂ} {T₀ T R M q μ : ℝ} {n : ℕ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hFout : DifferentiableOn ℂ F (closedBall (dottieScaledRightCenter T₀ n) R))
    (hP : Differentiable ℂ P) (hp : ∀ z, P z ≠ 0)
    (hR : dottieScaledRadius n < R) (hM : 0 < M) (hμ : 0 < μ) (hgap : μ < 1 - q)
    (houter : ∀ z ∈ sphere (dottieScaledRightCenter T₀ n) R, ‖F z / P z - 1‖ ≤ M)
    (hinner : ∀ z ∈ sphere (dottieScaledRightCenter T₀ n) (dottieScaledRadius n),
      ‖F z / P z - 1‖ ≤ q)
    (hT : |T - T₀| ≤ (1 - q - μ) * (R - dottieScaledRadius n) / (M + (1 - q - μ)))
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    F w ≠ 0 := by
  let W : ℂ → ℂ := fun z => -I / P z
  have hW : Differentiable ℂ W := (differentiable_const (-I)).div hP hp
  have hval (z : ℂ) : W z * F z = -I * (F z / P z) := by
    simp only [W, div_eq_mul_inv]
    ring
  apply dottie_disk_nonzero_of_holomorphic_weight hF hW.differentiableOn hμ ?_ hw
  apply dottie_calculated_height_sign (k := -I) hR hM hgap
    (hW.differentiableOn.mul hFout) ?_ ?_ hT
  · intro z hz
    change ‖W z * F z - -I‖ ≤ M
    rw [hval, show -I * (F z / P z) - -I = -I * (F z / P z - 1) by ring,
      norm_mul, norm_neg, norm_I, one_mul]
    exact houter z hz
  · intro z hz
    have h := (abs_le.mp ((abs_re_le_norm _).trans (hinner z hz))).1
    rw [sub_re, one_re] at h
    change (W z * F z).im ≤ -(1 - q)
    rw [hval, neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
    linarith only [h]

/-- Keep a margin of `0.0396` on the ordinary Cayley circle. The verified
relative enclosures give the exact height half-width `1625 / 3460192`. -/
theorem ordinary_cayley_calculated_height_band_ne_zero {a b : ℂ} (ha : a ≠ 0) :
    let T₀ : ℝ := 100000001 + 1 / 512
    let c := dottieScaledRightCenter T₀ 0
    let P := contourExponentialModel a b c
    (∀ z ∈ sphere c (1 / 4), ‖riemannZeta z / P z - 1‖ ≤ 101631 / 100000) →
    (∀ z ∈ sphere c (dottieScaledRadius 0), ‖riemannZeta z / P z - 1‖ ≤ 4477 / 5000) →
    ∀ T : ℝ, |T - T₀| ≤ 1625 / 3460192 →
      ∀ w ∈ closedBall (dottieScaledRightCenter T 0) (dottieScaledRadius 0),
        riemannZeta w ≠ 0 := by
  intro T₀ c P houter hinner T hT w hw
  have hP : Differentiable ℂ P ∧ ∀ z : ℂ, P z ≠ 0 :=
    contourExponentialModel_regular ha b c
  have hF : DifferentiableOn ℂ riemannZeta (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
    intro z hz
    have hzr : z.re < 1 := hz.2
    have hz1 : z ≠ 1 := by intro he; norm_num [he] at hzr
    exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
  have hc : c.im = 100000001 := by norm_num [c, T₀, dottieScaledRightCenter]
  have hFout : DifferentiableOn ℂ riemannZeta (closedBall c (1 / 4)) := by
    intro z hz
    have hd : ‖z - c‖ ≤ 1 / 4 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hib := (abs_le.mp ((abs_im_le_norm (z - c)).trans hd)).1
    rw [sub_im, hc] at hib
    have hz1 : z ≠ 1 := by intro he; norm_num [he] at hib
    exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
  apply dottie_relative_calculated_height_band_nonzero (T₀ := T₀)
    (R := 1 / 4) (M := 101631 / 100000) (q := 4477 / 5000) (μ := 99 / 2500)
    hF hFout hP.1 hP.2 (by norm_num [dottieScaledRadius, dottieRingScale])
    (by norm_num) (by norm_num) (by norm_num) houter hinner ?_ hw
  convert hT using 1
  norm_num [dottieScaledRadius, dottieRingScale]

/-- The completed Dedekind reading supplies its own outer norm allowance.
A bound for the weight and a signed reference circle then give a band
for the original field continuation. -/
theorem mixedTheta_calculated_height_band_nonzero (K : Type) [Field K] [NumberField K]
    {W : ℂ → ℂ} {T₀ T R B m μ : ℝ} {n : ℕ}
    (hW : DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hR : dottieScaledRadius n < R)
    (hleft : 0 < (dottieScaledRightCenter T₀ n).re - R)
    (hright : 0 < 1 - (dottieScaledRightCenter T₀ n).re - R)
    (hB : 0 < B) (hμ : 0 < μ) (hgap : μ < m)
    (hweight : ∀ z ∈ sphere (dottieScaledRightCenter T₀ n) R, ‖W z‖ ≤ B)
    (hsign : ∀ z ∈ sphere (dottieScaledRightCenter T₀ n) (dottieScaledRadius n),
      (W z * mixedThetaCompletedReading K z).im ≤ -m)
    (hT : |T - T₀| ≤ (m - μ) * (R - dottieScaledRadius n) /
      (B * mixedThetaDiskMajorant K (dottieScaledRightCenter T₀ n) R + (m - μ)))
    {w : ℂ} (hw : w ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) :
    mixedThetaContinuation K w ≠ 0 := by
  let c := dottieScaledRightCenter T₀ n
  let r := dottieScaledRadius n
  let F := mixedThetaCompletedReading K
  let A := mixedThetaDiskMajorant K c R
  have hF := mixedThetaCompletedReading_differentiableOn K
  have hsub : closedBall c R ⊆ Complex.re ⁻¹' Ioo (0 : ℝ) 1 := by
    intro z hz
    have hd : ‖z - c‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hre := abs_le.mp ((abs_re_le_norm _).trans hd)
    rw [sub_re] at hre
    change 0 < z.re ∧ z.re < 1
    exact ⟨by linarith only [hleft, hre.1], by linarith only [hright, hre.2]⟩
  have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
  have hc : c + (r : ℂ) ∈ sphere c r := by
    rw [mem_sphere, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hne : F (c + (r : ℂ)) ≠ 0 := by
    intro hz
    have h := hsign _ hc
    change (W _ * F (c + (r : ℂ))).im ≤ -m at h
    rw [hz, mul_zero, zero_im] at h
    linarith only [h, hμ, hgap]
  have hA : 0 < A :=
    (norm_pos_iff.mpr hne).trans_le
      (mixedThetaCompletedReading_norm_le_on_disk K hleft hright
        (closedBall_subset_closedBall hR.le (sphere_subset_closedBall hc)))
  have houter (z : ℂ) (hz : z ∈ sphere c R) : ‖W z * F z - 0‖ ≤ B * A := by
    rw [sub_zero, norm_mul]
    exact mul_le_mul (hweight z hz)
      (mixedThetaCompletedReading_norm_le_on_disk K hleft hright (sphere_subset_closedBall hz))
      (norm_nonneg _) hB.le
  have hboundary := dottie_calculated_height_sign (k := 0) hR (mul_pos hB hA) hgap
    ((hW.mul hF).mono hsub) houter hsign hT
  have hreading := dottie_disk_nonzero_of_holomorphic_weight hF hW hμ hboundary hw
  obtain ⟨hwl, hwr⟩ := dottieScaledRightDisk_strip hw
  exact fun hz => hreading
    ((mixedThetaCompletedReading_zero_iff K w (by linarith only [hwl]) hwr).mpr hz)

#print axioms dottie_calculated_height_sign
#print axioms dottie_relative_calculated_height_band_nonzero
#print axioms ordinary_cayley_calculated_height_band_ne_zero
#print axioms mixedTheta_calculated_height_band_nonzero

end

end FieldTarget
