import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FunProp

namespace FieldTarget

open Complex Filter Metric Set
open scoped BigOperators NNReal ENNReal

/-- A polynomial in the displacement from the disk center, with rational
real and imaginary parts for each coefficient. -/
def dottieRationalWeight (c : ℂ) {N : ℕ} (a : Fin N → ℚ × ℚ) (z : ℂ) : ℂ :=
  ∑ k : Fin N,
    (((a k).1 : ℝ) + I * ((a k).2 : ℝ)) * (z - c) ^ (k : ℕ)

theorem dottieRationalWeight_differentiable (c : ℂ) {N : ℕ} (a : Fin N → ℚ × ℚ) :
    Differentiable ℂ (dottieRationalWeight c a) := by
  unfold dottieRationalWeight
  fun_prop

private theorem exists_rational_parts_near (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℚ × ℚ, ‖((a.1 : ℝ) + I * (a.2 : ℝ)) - z‖ < ε := by
  obtain ⟨x, hx₀, hx₁⟩ := exists_rat_btwn (show z.re - ε / 2 < z.re + ε / 2 by linarith)
  obtain ⟨y, hy₀, hy₁⟩ := exists_rat_btwn (show z.im - ε / 2 < z.im + ε / 2 by linarith)
  let w : ℂ := (x : ℝ) + I * (y : ℝ)
  have hre : |(w - z).re| < ε / 2 := by
    simp only [w, sub_re, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      zero_mul, one_mul, sub_zero, add_zero]
    exact abs_lt.mpr ⟨by linarith only [hx₀], by linarith only [hx₁]⟩
  have him : |(w - z).im| < ε / 2 := by
    simp only [w, sub_im, add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
      zero_mul, one_mul, zero_add]
    exact abs_lt.mpr ⟨by linarith only [hy₀], by linarith only [hy₁]⟩
  exact ⟨(x, y), (norm_le_abs_re_add_abs_im (w - z)).trans_lt
    ((add_lt_add hre him).trans_eq (by ring))⟩

private theorem exists_centered_complex_polynomial_approx
    {F : ℂ → ℂ} {c : ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {r R : ℝ≥0} {ε : ℝ} (hrR : r < R) (hε : 0 < ε)
    (hp : HasFPowerSeriesOnBall F p c (R : ℝ≥0∞)) :
    ∃ (N : ℕ) (b : ℕ → ℂ), ∀ z ∈ closedBall c r,
      ‖(∑ k : Fin N, b (k : ℕ) * (z - c) ^ (k : ℕ)) - F z‖ < ε := by
  obtain ⟨ρ, hrρ, hρR⟩ := exists_between hrR
  have hUniform : TendstoUniformlyOn (fun n z ↦ p.partialSum n (z - c)) F atTop
      (ball c (ρ : ℝ)) := hp.tendstoUniformlyOn' (ENNReal.coe_lt_coe.mpr hρR)
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp hUniform ε hε).exists
  refine ⟨N, p.coeff, fun z hz ↦ ?_⟩
  have hzρ : z ∈ ball c ρ := mem_ball.mpr ((mem_closedBall.mp hz).trans_lt hrρ)
  have heq : p.partialSum N (z - c) = ∑ k : Fin N, p.coeff (k : ℕ) * (z - c) ^ (k : ℕ) := by
    calc
      _ = ∑ k ∈ Finset.range N, p.coeff k * (z - c) ^ k :=
        Finset.sum_congr rfl fun k _ ↦
          (FormalMultilinearSeries.apply_eq_pow_smul_coeff (p := p) (n := k) (z := z - c)).trans
            (mul_comm _ _)
      _ = _ := (Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ p.coeff k * (z - c) ^ k) N).symm
  have hTaylor := hN z hzρ
  rwa [dist_comm, dist_eq_norm, heq] at hTaylor

private theorem exists_rationalWeight_approx_polynomial {c : ℂ} {r ε : ℝ} {N : ℕ}
    (b : ℕ → ℂ) (hε : 0 < ε) :
    ∃ a : Fin N → ℚ × ℚ, ∀ z ∈ closedBall c r,
      ‖dottieRationalWeight c a z - (∑ k : Fin N, b (k : ℕ) * (z - c) ^ (k : ℕ))‖ ≤ ε := by
  classical
  let B : ℝ := (max 1 r) ^ N
  have hB : 0 < B := pow_pos (zero_lt_one.trans_le (le_max_left (1 : ℝ) r)) N
  let δ := ε / (1 + (N : ℝ)) / B
  have hδ : 0 < δ := div_pos (div_pos hε (by positivity)) hB
  choose a ha using fun k : Fin N ↦ exists_rational_parts_near (b (k : ℕ)) hδ
  refine ⟨a, fun z hz ↦ ?_⟩
  have hpow (k : Fin N) : ‖z - c‖ ^ (k : ℕ) ≤ B := by
    have hz' : ‖z - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
    exact (pow_le_pow_left₀ (norm_nonneg _) (hz'.trans (le_max_right 1 r)) _).trans
      (pow_le_pow_right₀ (le_max_left 1 r) k.isLt.le)
  have hMass : (N : ℝ) * (δ * B) ≤ ε := by
    change (N : ℝ) * (ε / (1 + (N : ℝ)) / B * B) ≤ ε
    rw [div_mul_cancel₀ _ hB.ne', ← mul_div_assoc]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 1 + (N : ℝ))).mpr
    nlinarith only [hε]
  rw [dottieRationalWeight, ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _k : Fin N, δ * B := by
      apply Finset.sum_le_sum
      intro k _
      rw [← sub_mul, norm_mul, norm_pow]
      exact mul_le_mul (ha k).le (hpow k) (by positivity) hδ.le
    _ = (N : ℝ) * (δ * B) := by simp [nsmul_eq_mul]
    _ ≤ ε := hMass

/-- On a closed subdisk of a holomorphic disk, a centered polynomial with
rational complex coefficients can approximate the reading uniformly. -/
theorem exists_dottieRationalWeight_approx
    {F : ℂ → ℂ} {c : ℂ} {r R ε : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hε : 0 < ε)
    (hF : DifferentiableOn ℂ F (closedBall c R)) :
    ∃ (N : ℕ) (a : Fin N → ℚ × ℚ),
      ∀ z ∈ closedBall c r, ‖dottieRationalWeight c a z - F z‖ < ε := by
  have hhalf : 0 < ε / 2 := by positivity
  let r₀ : ℝ≥0 := ⟨r, hr⟩
  let R₀ : ℝ≥0 := ⟨R, hr.trans hrR.le⟩
  have hR₀ : 0 < R₀ := hr.trans_lt hrR
  have hp := hF.hasFPowerSeriesOnBall (R := R₀) hR₀
  obtain ⟨N, b, hb⟩ := exists_centered_complex_polynomial_approx
    (r := r₀) (R := R₀) hrR hhalf hp
  obtain ⟨a, ha⟩ := exists_rationalWeight_approx_polynomial (c := c) (r := r) (N := N) b hhalf
  refine ⟨N, a, fun z hz ↦ ?_⟩
  let v := ∑ k : Fin N, b (k : ℕ) * (z - c) ^ (k : ℕ)
  calc
    ‖dottieRationalWeight c a z - F z‖ ≤ ‖dottieRationalWeight c a z - v‖ + ‖v - F z‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (ha z hz) (hb z hz)
    _ = ε := by ring

#print axioms dottieRationalWeight_differentiable
#print axioms exists_dottieRationalWeight_approx

end FieldTarget
