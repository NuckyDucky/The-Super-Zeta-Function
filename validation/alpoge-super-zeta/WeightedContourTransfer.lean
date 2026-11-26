import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Weighted circle moments and factor subtraction. Boundary nonvanishing is
enough for subtracting the moments of two factors, even if their zeros
coincide inside the circle.
-/
noncomputable section

namespace SuperZeta.WeightedContour

open Complex Metric Set Filter
open scoped Real Topology

def moment (c : ℂ) (r : ℝ) (f p : ℂ → ℂ) : ℂ :=
  (2 * π * I : ℂ)⁻¹ * ∮ z in C(c,r), p z * logDeriv f z

variable {O : Set ℂ} {c : ℂ} {r : ℝ} {f g p : ℂ → ℂ}

theorem moment_congr (hr : 0 ≤ r) (hO : IsOpen O) (hD : closedBall c r ⊆ O)
    (h : Set.EqOn f g O) : moment c r f p = moment c r g p := by
  unfold moment
  congr 1
  apply circleIntegral.integral_congr hr
  intro z hz
  have hloc : f =ᶠ[𝓝 z] g :=
    Filter.eventually_of_mem (hO.mem_nhds (hD (sphere_subset_closedBall hz))) h
  simp only [logDeriv_apply, hloc.deriv_eq, hloc.eq_of_nhds]

private theorem integrable_slope (hr : 0 ≤ r) (hO : IsOpen O) (hD : closedBall c r ⊆ O)
    (hf : DifferentiableOn ℂ f O) (hp : DifferentiableOn ℂ p O)
    (hn : ∀ z ∈ sphere c r, f z ≠ 0) : CircleIntegrable (fun z => p z * logDeriv f z) c r := by
  refine ContinuousOn.circleIntegrable hr fun z hz => ?_
  have h := hO.mem_nhds (hD (sphere_subset_closedBall hz))
  exact ((hp.differentiableAt h).mul
    (((hf.deriv hO).differentiableAt h).div (hf.differentiableAt h) (hn z hz))).continuousAt.continuousWithinAt

theorem moment_mul (hr : 0 ≤ r) (hO : IsOpen O) (hD : closedBall c r ⊆ O)
    (hf : DifferentiableOn ℂ f O) (hg : DifferentiableOn ℂ g O) (hp : DifferentiableOn ℂ p O)
    (fn : ∀ z ∈ sphere c r, f z ≠ 0) (gn : ∀ z ∈ sphere c r, g z ≠ 0) :
    moment c r (fun z => f z * g z) p = moment c r f p + moment c r g p := by
  let F := fun z => p z * logDeriv f z
  let G := fun z => p z * logDeriv g z
  have hsplit : Set.EqOn (fun z => p z * logDeriv (fun t => f t * g t) z) (F+G) (sphere c r) := by
    intro z hz
    have h := hO.mem_nhds (hD (sphere_subset_closedBall hz))
    change p z * logDeriv (fun t => f t * g t) z = F z + G z
    rw [logDeriv_mul z (fn z hz) (gn z hz) (hf.differentiableAt h) (hg.differentiableAt h)]
    exact mul_add _ _ _
  have hi := circleIntegral.integral_add (integrable_slope hr hO hD hf hp fn)
    (integrable_slope hr hO hD hg hp gn)
  unfold moment
  rw [circleIntegral.integral_congr hr hsplit]
  change ((2 * π * I : ℂ)⁻¹ * ∮ z in C(c,r), F z + G z) =
    (2 * π * I : ℂ)⁻¹ * (∮ z in C(c,r), F z) + (2 * π * I : ℂ)⁻¹ * ∮ z in C(c,r), G z
  rw [hi, mul_add]

theorem moment_unit (hr : 0 ≤ r) (hO : IsOpen O) (hD : closedBall c r ⊆ O)
    (hf : DifferentiableOn ℂ f O) (hp : DifferentiableOn ℂ p O)
    (hn : ∀ z ∈ closedBall c r, f z ≠ 0) : moment c r f p = 0 := by
  have hd (z : ℂ) (hz : z ∈ closedBall c r) :
      DifferentiableAt ℂ (fun t => p t * logDeriv f t) z := by
    have h := hO.mem_nhds (hD hz)
    exact (hp.differentiableAt h).mul
      (((hf.deriv hO).differentiableAt h).div (hf.differentiableAt h) (hn z hz))
  rw [moment, Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt)
    (fun z hz => hd z (ball_subset_closedBall hz.1)), mul_zero]

theorem moment_linear {a : ℂ} (ha : a ∈ ball c r) (hp : Differentiable ℂ p) :
    moment c r (fun z => z-a) p = p a := by
  have hr := (dist_nonneg.trans_lt (mem_ball.mp ha)).le
  have he : (fun z => p z * logDeriv (fun t => t-a) z) = fun z => (z-a)⁻¹ • p z := by
    funext z
    simp [logDeriv_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  unfold moment
  rw [he, ← smul_eq_mul]
  exact Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    countable_empty ha hp.continuous.continuousOn (fun z _ => hp z)

theorem moment_power {a : ℂ} (ha : a ∈ ball c r) (hp : Differentiable ℂ p) (n : ℕ) :
    moment c r (fun z => (z-a)^n) p = (n : ℂ) * p a := by
  have hr := (dist_nonneg.trans_lt (mem_ball.mp ha)).le
  have hne (z : ℂ) (hz : z ∈ sphere c r) : z-a ≠ 0 := by
    intro he
    obtain rfl := sub_eq_zero.mp he
    exact (ne_of_lt (mem_ball.mp ha)) (mem_sphere.mp hz)
  have hlin : Differentiable ℂ (fun z : ℂ => z-a) := differentiable_id.sub_const a
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact moment_unit hr isOpen_univ (subset_univ _) (differentiableOn_const _) hp.differentiableOn
      (fun _ _ => one_ne_zero)
  | succ n ih =>
    simp only [pow_succ]
    have hn : DifferentiableOn ℂ (fun z : ℂ => (z-a)^n) univ := (hlin.pow n).differentiableOn
    rw [moment_mul hr isOpen_univ (subset_univ _) hn hlin.differentiableOn hp.differentiableOn
      (fun z hz => pow_ne_zero _ (hne z hz)) hne, ih, moment_linear ha hp,
      Nat.cast_succ, add_mul, one_mul]

theorem moment_local_power {a : ℂ} (ha : a ∈ ball c r) (n : ℕ) (hp : Differentiable ℂ p)
    (hO : IsOpen O) (hD : closedBall c r ⊆ O)
    (hg : DifferentiableOn ℂ g O) (hn : ∀ z ∈ closedBall c r, g z ≠ 0)
    (h : Set.EqOn f (fun z => (z-a)^n * g z) O) : moment c r f p = (n : ℂ) * p a := by
  have hr := (dist_nonneg.trans_lt (mem_ball.mp ha)).le
  have hd : Differentiable ℂ (fun z : ℂ => z-a) := differentiable_id.sub_const a
  have hPow : DifferentiableOn ℂ (fun z : ℂ => (z-a)^n) O := (hd.pow n).differentiableOn
  have hz (z : ℂ) (hz' : z ∈ sphere c r) : z-a ≠ 0 := by
    intro e
    obtain rfl := sub_eq_zero.mp e
    exact (ne_of_lt (mem_ball.mp ha)) (mem_sphere.mp hz')
  rw [moment_congr hr hO hD h, moment_mul hr hO hD hPow hg
    hp.differentiableOn (fun z hz' => pow_ne_zero _ (hz z hz'))
    (fun z hz' => hn z (sphere_subset_closedBall hz')), moment_power ha hp,
    moment_unit hr hO hD hg hp.differentiableOn hn, add_zero]

/-- Additive bookkeeping for a field product and an independently marked
ordinary channel. Interior zeros of the factors may coincide. -/
theorem isolate_third_factor {F C W A Z B G : ℂ → ℂ}
    (hr : 0 ≤ r) (hO : IsOpen O) (hD : closedBall c r ⊆ O)
    (hp : DifferentiableOn ℂ p O)
    (hw : DifferentiableOn ℂ W O) (ha : DifferentiableOn ℂ A O)
    (hz : DifferentiableOn ℂ Z O) (hb : DifferentiableOn ℂ B O) (hg : DifferentiableOn ℂ G O)
    (wf : ∀ z ∈ sphere c r, W z ≠ 0) (af : ∀ z ∈ sphere c r, A z ≠ 0)
    (zf : ∀ z ∈ sphere c r, Z z ≠ 0) (bf : ∀ z ∈ sphere c r, B z ≠ 0)
    (gf : ∀ z ∈ sphere c r, G z ≠ 0)
    (hF : Set.EqOn F (fun z => (Z z * B z) * G z) O)
    (hC : Set.EqOn C (fun z => (W z * A z) * Z z) O) :
    moment c r G p = moment c r F p - moment c r C p +
      moment c r W p + moment c r A p - moment c r B p := by
  have hZB : DifferentiableOn ℂ (fun z => Z z * B z) O := hz.mul hb
  have hWA : DifferentiableOn ℂ (fun z => W z * A z) O := hw.mul ha
  rw [moment_congr hr hO hD hF, moment_congr hr hO hD hC]
  rw [moment_mul hr hO hD hZB hg hp (fun z hz' => mul_ne_zero (zf z hz') (bf z hz')) gf,
    moment_mul hr hO hD hWA hz hp (fun z hz' => mul_ne_zero (wf z hz') (af z hz')) zf,
    moment_mul hr hO hD hz hb hp zf bf, moment_mul hr hO hD hw ha hp wf af]
  ring

/-- The archived Gaussian prime detector contributes the same moments as the
zero reading. The derivative of its holomorphic remainder integrates to zero
even after introducing a holomorphic weight. -/
theorem moment_from_signed_detector {G H S : ℂ → ℂ}
    (hr : 0 ≤ r) (hO : IsOpen O) (hD : closedBall c r ⊆ O)
    (hp : DifferentiableOn ℂ p O) (hg : DifferentiableOn ℂ G O) (hh : DifferentiableOn ℂ H O)
    (gf : ∀ z ∈ sphere c r, G z ≠ 0)
    (he : ∀ z ∈ sphere c r, 2 * S z * G z = deriv H z * G z - deriv G z) :
    moment c r G p = -(π * I : ℂ)⁻¹ * ∮ z in C(c,r), p z * S z := by
  let D := fun z => p z * deriv H z
  let K := fun z => p z * logDeriv G z
  have hed : Set.EqOn (fun z => p z * S z) (fun z => (1/2:ℂ)*(D z-K z)) (sphere c r) := by
    intro z hz
    dsimp [D, K]
    rw [logDeriv_apply]
    have he' := he z hz
    have hs := (eq_div_iff (gf z hz)).2 he'
    rw [sub_div, mul_div_cancel_right₀ _ (gf z hz)] at hs
    linear_combination p z / 2 * hs
  have hDdiff (z : ℂ) (hz : z ∈ closedBall c r) : DifferentiableAt ℂ D z := by
    have h := hO.mem_nhds (hD hz)
    exact (hp.differentiableAt h).mul ((hh.deriv hO).differentiableAt h)
  have hDc : ContinuousOn D (closedBall c r) :=
    fun z hz => (hDdiff z hz).continuousAt.continuousWithinAt
  have hi : CircleIntegrable D c r :=
    ContinuousOn.circleIntegrable hr (hDc.mono sphere_subset_closedBall)
  have hk : CircleIntegrable K c r := integrable_slope hr hO hD hg hp gf
  have hd0 : (∮ z in C(c,r), D z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr countable_empty hDc
      (fun z hz => hDdiff z (ball_subset_closedBall hz.1))
  unfold moment
  rw [circleIntegral.integral_congr hr hed]
  have hentry : (∮ z in C(c,r), (1/2:ℂ)*(D z-K z)) =
      (1/2:ℂ)*((∮ z in C(c,r), D z)-(∮ z in C(c,r), K z)) := by
    simp only [← smul_eq_mul, circleIntegral.integral_smul, circleIntegral.integral_sub hi hk]
  rw [hentry, hd0, zero_sub]
  have hpI : (π*(I:ℂ)) ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) I_ne_zero
  rw [mul_assoc, mul_inv_rev]
  ring

#print axioms moment_mul
#print axioms moment_unit
#print axioms moment_power
#print axioms moment_local_power
#print axioms isolate_third_factor
#print axioms moment_from_signed_detector

end SuperZeta.WeightedContour
end
