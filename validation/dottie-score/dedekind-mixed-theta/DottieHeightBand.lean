import DottieContourPhase
import ContourExponentialModel
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-! A strict sign on one Dottie circle persists under a height shift
whose Cauchy error fits inside the available margin. -/

namespace FieldTarget

open Complex Metric Set SuperZeta.StirlingCorrection

noncomputable section

/-- Every point on the moved circle is compared to the original point
with the same angle. A radius-`ρ` neighborhood around the segment between
them fits in the outer disk, giving a derivative bound of `M / ρ`. -/
theorem dottie_shifted_boundary_sign {H : ℂ → ℂ} {T₀ T R ρ M m : ℝ} {n : ℕ}
    (hρ : 0 < ρ) (hroom : dottieScaledRadius n + |T - T₀| + ρ ≤ R)
    (hH : DifferentiableOn ℂ H (closedBall (dottieScaledRightCenter T₀ n) R))
    (houter : ∀ u ∈ sphere (dottieScaledRightCenter T₀ n) R, ‖H u‖ ≤ M)
    (hsign : ∀ u ∈ sphere (dottieScaledRightCenter T₀ n) (dottieScaledRadius n),
      (H u).im ≤ -m) :
    ∀ w ∈ sphere (dottieScaledRightCenter T n) (dottieScaledRadius n),
      (H w).im ≤ -m + (M / ρ) * |T - T₀| := by
  intro w hw
  let c := dottieScaledRightCenter T₀ n
  let r := dottieScaledRadius n
  let Δ := ((T - T₀ : ℝ) : ℂ) * I
  let v := w - Δ
  let S := closedBall c (r + |T - T₀|)
  have hr : 0 < r := mul_pos (by norm_num) (dottieRingScale_pos n)
  have hR : 0 < R := by linarith only [hr, abs_nonneg (T - T₀), hρ, hroom]
  have hc : dottieScaledRightCenter T n = c + Δ := by
    apply Complex.ext
    · simp [c, Δ, dottieScaledRightCenter, mul_re]
    · simp [c, Δ, dottieScaledRightCenter, mul_im]
  have hΔ : ‖Δ‖ = |T - T₀| := by
    simp only [Δ, norm_mul, norm_I, mul_one, norm_real, Real.norm_eq_abs]
  have hv : v ∈ sphere c r := by
    rw [mem_sphere, dist_eq_norm]
    rw [show v - c = w - dottieScaledRightCenter T n by rw [hc]; dsimp [v]; ring]
    simpa only [mem_sphere, dist_eq_norm] using hw
  have hvr : ‖v - c‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hv
  have hvS : v ∈ S := by
    change v ∈ closedBall c (r + |T - T₀|)
    rw [mem_closedBall, dist_eq_norm, hvr]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hwS : w ∈ S := by
    change w ∈ closedBall c (r + |T - T₀|)
    rw [mem_closedBall, dist_eq_norm, show w - c = v - c + Δ by dsimp [v]; ring]
    exact (norm_add_le _ _).trans_eq (by rw [hvr, hΔ])
  have hHolClosure : DifferentiableOn ℂ H (closure (ball c R)) := by
    rwa [closure_ball c hR.ne']
  have hM (u : ℂ) (hu : u ∈ closedBall c R) : ‖H u‖ ≤ M := by
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      hHolClosure.diffContOnCl ?_ ?_
    · intro z hz
      rw [frontier_ball c hR.ne'] at hz
      exact houter z hz
    · rwa [closure_ball c hR.ne']
  have hAt (u : ℂ) (hu : u ∈ S) : DifferentiableAt ℂ H u := by
    have hdist : dist u c ≤ r + |T - T₀| := mem_closedBall.mp hu
    have hu' : u ∈ ball c R := mem_ball.mpr
      (by linarith only [hdist, hroom, hρ])
    exact (hH u (ball_subset_closedBall hu')).differentiableAt
      (closedBall_mem_nhds_of_mem hu')
  have hDeriv (u : ℂ) (hu : u ∈ S) : ‖deriv H u‖ ≤ M / ρ := by
    have hsub : closedBall u ρ ⊆ closedBall c R := by
      intro z hz
      rw [mem_closedBall]
      have hdist := add_le_add (mem_closedBall.mp hz) (mem_closedBall.mp hu)
      exact (dist_triangle z u c).trans (by linarith only [hdist, hroom])
    have hHo := hH.mono hsub
    rw [← closure_ball u hρ.ne'] at hHo
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ
      hHo.diffContOnCl (fun z hz => hM z (hsub (sphere_subset_closedBall hz)))
  have hdiff := (convex_closedBall c (r + |T - T₀|)).norm_image_sub_le_of_norm_deriv_le
    hAt hDeriv hvS hwS
  rw [show w - v = Δ by dsimp [v]; ring, hΔ] at hdiff
  have him := (abs_le.mp ((abs_im_le_norm (H w - H v)).trans hdiff)).2
  rw [sub_im] at him
  linarith only [him, hsign v hv]

/-- One reference circle and an outer norm bound certify every translated
disk in the height band, with one common lower bound for the signed gap. -/
theorem dottie_height_band_nonzero
    {F W : ℂ → ℂ} {T₀ T δ R ρ M m : ℝ} {n : ℕ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hW : DifferentiableOn ℂ W (Complex.re ⁻¹' Ioo (0 : ℝ) 1))
    (hρ : 0 < ρ) (hM : 0 ≤ M) (hroom : dottieScaledRadius n + δ + ρ ≤ R)
    (hbudget : (M / ρ) * δ < m)
    (hH : DifferentiableOn ℂ (fun z => W z * F z) (closedBall (dottieScaledRightCenter T₀ n) R))
    (houter : ∀ u ∈ sphere (dottieScaledRightCenter T₀ n) R, ‖W u * F u‖ ≤ M)
    (hsign : ∀ u ∈ sphere (dottieScaledRightCenter T₀ n) (dottieScaledRadius n),
      (W u * F u).im ≤ -m)
    (hT : |T - T₀| ≤ δ) {w : ℂ}
    (hw : w ∈ closedBall (dottieScaledRightCenter T n) (dottieScaledRadius n)) : F w ≠ 0 := by
  apply dottie_disk_nonzero_of_holomorphic_weight hF hW
    (sub_pos.mpr hbudget) ?_ hw
  intro z hz
  have hroom' : dottieScaledRadius n + |T - T₀| + ρ ≤ R := by
    linarith only [hroom, hT]
  have h := dottie_shifted_boundary_sign hρ hroom' hH houter hsign z hz
  have hdiff := mul_le_mul_of_nonneg_left hT (div_nonneg hM hρ.le)
  change (W z * F z).im ≤ -m + (M / ρ) * |T - T₀| at h
  linarith only [h, hdiff]

/-- The two relative enclosures from the ordinary Cayley test supply
one positive signed margin for the whole stated height band. -/
theorem ordinary_cayley_height_band_ne_zero {a b : ℂ} (ha : a ≠ 0) :
    let T₀ : ℝ := 100000001 + 1 / 512
    let c := dottieScaledRightCenter T₀ 0
    let P := contourExponentialModel a b c
    (∀ z ∈ sphere c (1 / 4), ‖riemannZeta z / P z - 1‖ ≤ 101631 / 100000) →
    (∀ z ∈ sphere c (dottieScaledRadius 0), ‖riemannZeta z / P z - 1‖ ≤ 4477 / 5000) →
    ∀ T : ℝ, |T - T₀| ≤ 1 / 4096 →
      ∀ w ∈ closedBall (dottieScaledRightCenter T 0) (dottieScaledRadius 0),
        riemannZeta w ≠ 0 := by
  intro T₀ c P houter hinner T hT w hw
  let W : ℂ → ℂ := fun z => -I / P z
  have hP : Differentiable ℂ P ∧ ∀ z : ℂ, P z ≠ 0 :=
    contourExponentialModel_regular ha b c
  have hW : Differentiable ℂ W := (differentiable_const (-I)).div hP.1 hP.2
  have hF : DifferentiableOn ℂ riemannZeta (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := by
    intro z hz
    have hzr : z.re < 1 := hz.2
    have hz1 : z ≠ 1 := by intro he; norm_num [he] at hzr
    exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
  have hc : c.im = 100000001 := by
    norm_num [c, T₀, dottieScaledRightCenter]
  have hFouter : DifferentiableOn ℂ riemannZeta (closedBall c (1 / 4)) := by
    intro z hz
    have hd : ‖z - c‖ ≤ 1 / 4 := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hib := (abs_le.mp ((abs_im_le_norm (z - c)).trans hd)).1
    rw [sub_im, hc] at hib
    have hz1 : z ≠ 1 := by intro he; norm_num [he] at hib
    exact (differentiableAt_riemannZeta hz1).differentiableWithinAt
  have hWval (z : ℂ) : W z * riemannZeta z = -I * (riemannZeta z / P z) := by
    simp only [W, div_eq_mul_inv]
    ring
  apply dottie_height_band_nonzero (δ := 1 / 4096) (R := 1 / 4) (ρ := 31 / 4096)
    (M := 201631 / 100000) (m := 523 / 5000) (T₀ := T₀) hF hW.differentiableOn
    (by norm_num) (by norm_num) (by norm_num [dottieScaledRadius, dottieRingScale])
    (by norm_num) (hW.differentiableOn.mul hFouter) ?_ ?_ hT hw
  · intro z hz
    have h := norm_add_le (riemannZeta z / P z - 1) 1
    rw [sub_add_cancel, norm_one] at h
    rw [hWval, norm_mul, norm_neg, norm_I, one_mul]
    linarith only [h, houter z hz]
  · intro z hz
    have h := (abs_le.mp ((abs_re_le_norm _).trans (hinner z hz))).1
    rw [sub_re, one_re] at h
    rw [hWval, neg_mul, neg_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add]
    linarith only [h]

#print axioms dottie_shifted_boundary_sign
#print axioms dottie_height_band_nonzero
#print axioms ordinary_cayley_height_band_ne_zero

end

end FieldTarget
