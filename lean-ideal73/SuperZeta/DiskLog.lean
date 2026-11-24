import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A normalized holomorphic logarithm on a concentric disk, obtained by
integrating the Taylor series of the logarithmic derivative term by term. -/
namespace SuperZeta.DiskLog
open Complex Metric Set
noncomputable section

private theorem primitive {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) :
    ∃ g : ℂ → ℂ, g 0 = 0 ∧ ∀ z ∈ ball 0 (R/2), HasDerivAt g (f z) z := by
  let a (n : ℕ) := (n.factorial : ℂ)⁻¹ * iteratedDeriv n f 0
  have taylor {z : ℂ} (hz : z ∈ ball 0 R) :
      HasSum (fun n => a n * z^n) (f z) := by
    simpa only [a, sub_zero, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      (Complex.hasSum_taylorSeries_on_ball hf hz)
  let b (n : ℕ) (z : ℂ) := a n / (n+1 : ℂ) * z^(n+1)
  have db (n : ℕ) (z : ℂ) : HasDerivAt (b n) (a n*z^n) z := by
    apply ((hasDerivAt_pow (n+1) z).const_mul (a n / (n+1 : ℂ))).congr_deriv
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel]
    have hn : (n:ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    field_simp [hn]
  have hh : 0 < R/2 := by positivity
  have radial : ((R/2:ℝ):ℂ) ∈ ball 0 R := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg hh.le]
    linarith
  have summ := (taylor radial).summable.norm
  have bound (n : ℕ) (z : ℂ) (hz : z ∈ ball 0 (R/2)) :
      ‖a n*z^n‖ ≤ ‖a n*((R/2:ℝ):ℂ)^n‖ := by
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hh.le]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.mp hz).le _) (norm_nonneg _)
  refine ⟨fun z => ∑' n, b n z, by simp [b], ?_⟩
  intro z hz
  have der := hasDerivAt_tsum_of_isPreconnected summ isOpen_ball
    (convex_ball (0:ℂ) (R/2)).isPreconnected (fun n y _ => db n y) bound
    (mem_ball_self hh) (by simp [b]) hz
  exact der.congr_deriv (taylor ((ball_subset_ball (by linarith : R/2 ≤ R)) hz)).tsum_eq

/-- Integrate q'/q from the origin. Normalization fixes the logarithm at zero. -/
theorem disk_log {q : ℂ → ℂ} {R : ℝ} (hR : 0<R)
    (hq : DifferentiableOn ℂ q (ball 0 R)) (hne : ∀ z∈ball 0 R, q z ≠ 0)
    (h0 : q 0=1) : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 (R/2)) ∧
      g 0=0 ∧ ∀ z∈ball 0 (R/2), Complex.exp (g z)=q z := by
  have hd := (hq.deriv isOpen_ball).div hq hne
  obtain ⟨g,hg0,hg⟩ := primitive hR hd
  refine ⟨g,fun z hz => (hg z hz).differentiableAt.differentiableWithinAt,hg0,?_⟩
  have hsub := @ball_subset_ball ℂ _ (0:ℂ) _ _ (show R/2 ≤ R by linarith)
  let k (z : ℂ) := q z / Complex.exp (g z)
  have dk (z : ℂ) (hz : z ∈ ball 0 (R/2)) : HasDerivAt k 0 z := by
    have dq := (hq.differentiableAt (isOpen_ball.mem_nhds (hsub hz))).hasDerivAt
    apply (dq.div ((hg z hz).cexp) (Complex.exp_ne_zero _)).congr_deriv
    change (deriv q z * Complex.exp (g z) - q z * (Complex.exp (g z) * (deriv q z / q z))) / _ = 0
    field_simp [hne z (hsub hz)]
    ring
  intro z hz
  have hk := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0:ℂ) (R/2)).isPreconnected
    (fun w hw => (dk w hw).differentiableAt.differentiableWithinAt)
    (fun w hw => (dk w hw).deriv) hz (mem_ball_self (by positivity : 0 < R/2))
  have he : q z / Complex.exp (g z) = 1 := by simpa [k,hg0,h0] using hk
  simpa using ((div_eq_iff (Complex.exp_ne_zero _)).mp he).symm

end
end SuperZeta.DiskLog
