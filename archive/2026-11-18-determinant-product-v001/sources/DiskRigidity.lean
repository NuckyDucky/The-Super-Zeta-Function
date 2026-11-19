import SuperZeta.DiskLog
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! Disk estimates for the normalized logarithm of a zero-free determinant quotient. -/

namespace SuperZeta.DiskRigidity

open Complex Metric Set

/-- Schwarz's lemma for the Cayley transform bounds a holomorphic logarithm
on the disk using only an upper bound for its real part. -/
theorem norm_le_of_re_lt {g : ℂ → ℂ} {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (hg : DifferentiableOn ℂ g (ball 0 R)) (h0 : g 0 = 0)
    (hre : ∀ y ∈ ball 0 R, (g y).re < A) {z : ℂ} (hz : ‖z‖ < R) :
    ‖g z‖ ≤ 2*A*‖z‖ / (R-‖z‖) := by
  let b : ℂ := ((2*A : ℝ) : ℂ)
  let f (y : ℂ) := g y / (b - g y)
  have hcomp {y : ℂ} (hy : y ∈ ball 0 R) : ‖g y‖ < ‖b-g y‖ := by
    have hs : ‖g y‖^2 < ‖b - g y‖^2 := by
      rw [Complex.sq_norm, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, b,
        Complex.ofReal_re, Complex.ofReal_im, zero_sub, neg_mul_neg]
      nlinarith [mul_pos hA (sub_pos.mpr (hre y hy))]
    nlinarith [norm_nonneg (g y), norm_nonneg (b-g y)]
  have hnonneg {y : ℂ} (hy : y ∈ ball 0 R) : 0 < ‖b-g y‖ :=
    (norm_nonneg _).trans_lt (hcomp hy)
  have hf : DifferentiableOn ℂ f (ball 0 R) :=
    hg.div ((differentiableOn_const b).sub hg) (fun y hy => norm_pos_iff.mp (hnonneg hy))
  have hf0 : f 0 = 0 := by simp [f, h0]
  have hm : MapsTo f (ball 0 R) (ball (f 0) 1) := by
    intro y hy
    simpa [Metric.mem_ball, hf0, f, norm_div, div_lt_one (hnonneg hy)] using hcomp hy
  have hmem : z ∈ ball 0 R := by simpa [Metric.mem_ball] using hz
  have hh := Complex.dist_le_div_mul_dist_of_mapsTo_ball hf hm hmem
  have hc : ‖g z‖ / ‖b-g z‖ ≤ ‖z‖/R := by
    rw [hf0, dist_zero_right, dist_zero_right] at hh
    simpa only [f, norm_div, one_div, div_eq_inv_mul, mul_one, norm_mul, norm_inv] using hh
  have hcross := (div_le_div_iff₀ (hnonneg hmem) hR).mp hc
  have hsum : ‖b-g z‖ ≤ 2*A+‖g z‖ := by
    simpa [b, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
      using norm_sub_le b (g z)
  apply (le_div_iff₀ (sub_pos.mpr hz)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsum (norm_nonneg z)]


/-- A normalized zero-free disk function has a logarithm at each interior point
whose size is controlled by its exponential growth bound and the disk radius. -/
theorem exists_log_bound {q : ℂ → ℂ} {R A : ℝ} (hR : 0 < R) (hA : 0 < A)
    (hq : DifferentiableOn ℂ q (ball 0 R)) (hne : ∀ z ∈ ball 0 R, q z ≠ 0)
    (h0 : q 0 = 1) (hbound : ∀ z ∈ ball 0 R, ‖q z‖ < Real.exp A)
    {z : ℂ} (hz : ‖z‖ < R / 2) :
    ∃ v : ℂ, Complex.exp v = q z ∧ ‖v‖ ≤ 2*A*‖z‖ / (R/2 - ‖z‖) := by
  obtain ⟨g, hg, hg0, he⟩ := DiskLog.disk_log hR hq hne h0
  have hsmall : ball (0 : ℂ) (R/2) ⊆ ball 0 R := Metric.ball_subset_ball (by linarith)
  have hre (y : ℂ) (hy : y ∈ ball 0 (R/2)) : (g y).re < A := by
    apply Real.exp_lt_exp.mp
    rw [← Complex.norm_exp, he y hy]
    exact hbound y (hsmall hy)
  exact ⟨g z, he z (by simpa [Metric.mem_ball] using hz),
    norm_le_of_re_lt (by positivity) hA hg hg0 hre hz⟩

end SuperZeta.DiskRigidity
