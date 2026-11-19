import SuperZeta.DeterminantProduct
import Mathlib.Analysis.Calculus.SmoothSeries

/-! For an absolutely summable list of reciprocal roots, differentiating the
normalized genus-zero product at the origin yields their sum. The local product
hypothesis in the last corollary is explicit. No root-sum value is assumed. -/
noncomputable section
namespace DottieOriented
open Complex Set Metric Filter
open scoped Topology

theorem canonical_product_first_derivative {ι : Type*} (a : ι → ℂ)
    (hs : Summable fun j => ‖a j‖) :
    HasDerivAt (fun z : ℂ => ∏' j, (1-z*a j)) (-(∑' j, a j)) 0 := by
  let B : ℝ := (∑' j, ‖a j‖) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let r : ℝ := (2*B)⁻¹
  have hr : 0 < r := inv_pos.mpr (by positivity)
  have small (j : ι) (z : ℂ) (hz : z ∈ ball (0:ℂ) r) : ‖z*a j‖ < 1/2 := by
    have hj : ‖a j‖ ≤ B := by
      have := hs.le_tsum j (fun i _ => norm_nonneg (a i))
      dsimp [B]
      linarith
    have hz' := mem_ball_zero_iff.mp hz
    rw [norm_mul]
    calc
      ‖z‖ * ‖a j‖ ≤ ‖z‖ * B := mul_le_mul_of_nonneg_left hj (norm_nonneg z)
      _ < r * B := mul_lt_mul_of_pos_right hz' hB
      _ = 1/2 := by dsimp [r]; field_simp; ring
  have slit (j : ι) (z : ℂ) (hz : z ∈ ball (0:ℂ) r) : 1-z*a j ∈ slitPlane := by
    rw [sub_eq_add_neg]
    apply mem_slitPlane_of_norm_lt_one
    rw [norm_neg]
    linarith [small j z hz]
  let f (j : ι) (z : ℂ) := Complex.log (1-z*a j)
  let g (j : ι) (z : ℂ) := -(a j)/(1-z*a j)
  have hd (j : ι) (z : ℂ) (hz : z ∈ ball (0:ℂ) r) : HasDerivAt (f j) (g j z) z := by
    simpa [f,g] using ((((hasDerivAt_id z).mul_const (a j)).const_sub (1:ℂ)).clog (slit j z hz))
  have hb (j : ι) (z : ℂ) (hz : z ∈ ball (0:ℂ) r) : ‖g j z‖ ≤ 2*‖a j‖ := by
    have ht := norm_sub_norm_le (1:ℂ) (z*a j)
    rw [norm_one] at ht
    have hlow : 1/2 < ‖1-z*a j‖ := by linarith [small j z hz]
    dsimp [g]
    rw [norm_div,norm_neg,div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (norm_nonneg (a j)) (sub_nonneg.mpr hlow.le)]
  have hz0 : (0:ℂ) ∈ ball (0:ℂ) r := mem_ball_self hr
  have hzero : Summable fun j => f j 0 := by simpa [f] using (summable_zero : Summable (fun _ : ι => (0:ℂ)))
  have hlog := hasDerivAt_tsum_of_isPreconnected (hs.mul_left 2) isOpen_ball
    (convex_ball (0:ℂ) r).isPreconnected hd hb hz0 hzero hz0
  have hseries : HasDerivAt (fun z : ℂ => Complex.exp (∑' j, f j z))
      (-(∑' j, a j)) 0 := by
    simpa [f,g,tsum_neg] using hlog.cexp
  apply hseries.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds (0:ℂ) hr] with z hz
  have ha : Summable a := Summable.of_norm hs
  have hf : Summable (fun j => f j z) := by
    simpa [f,neg_mul,sub_eq_add_neg] using
      (Complex.summable_log_one_add_of_summable (ha.mul_left (-z)))
  exact (Complex.hasProd_of_hasSum_log (fun j => slitPlane_ne_zero (slit j z hz))
    hf.hasSum).tprod_eq

/-- A product identity on any neighbourhood of the origin suffices. -/
theorem reciprocal_sum_of_local_product {ι : Type*} {E : ℂ → ℂ} (roots : ι → ℂ)
    (hs : Summable fun j => ‖(roots j)⁻¹‖)
    (product_near_zero : E =ᶠ[𝓝 0] (fun z => ∏' j, (1-z/roots j))) :
    (∑' j, (roots j)⁻¹) = -deriv E 0 := by
  have hd := canonical_product_first_derivative (fun j => (roots j)⁻¹) hs
  simp only [← div_eq_mul_inv] at hd
  rw [(hd.congr_of_eventuallyEq product_near_zero).deriv, neg_neg]

end DottieOriented
