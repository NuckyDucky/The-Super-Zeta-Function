import SuperZeta.Reciprocal
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Period-one capture in the outer part of the reciprocal parameter plane.
The first positive phase gives a sufficient test for entry after two updates. -/

noncomputable section

namespace SuperZeta.Reciprocal

open Complex Filter Function Set
open scoped NNReal Topology

private theorem exp_small_le_two : Real.exp (2/125) ≤ 2 :=
  (Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans (by norm_num)

theorem exp_neg_seven_lt : Real.exp (-7) < 1/1000 := by
  have he : (27/10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow := pow_lt_pow_left₀ he (by norm_num : (0:ℝ) ≤ 27/10) (by decide : 7 ≠ 0)
  have h7 : 1000 < Real.exp 7 := by
    rw [show (7:ℝ) = (7:ℕ) * 1 from by norm_num, Real.exp_nat_mul]
    exact lt_trans (by norm_num) hpow
  simpa only [Real.exp_neg, one_div] using
    one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 1000) h7

private theorem exp_mul_difference {a : ℂ} {D : Set ℂ} (hD : Convex ℝ D)
    {B : ℝ} (hB : ∀ z ∈ D, (a*z).re ≤ B) {u v : ℂ} (hu : u ∈ D) (hv : v ∈ D) :
    ‖exp (a*v) - exp (a*u)‖ ≤ (‖a‖ * Real.exp B) * ‖v-u‖ := by
  have hDeriv (z : ℂ) : HasDerivAt (fun w => exp (a*w)) (exp (a*z) * a) z := by
    simpa only [Function.comp_def, id, mul_one] using
      (Complex.hasDerivAt_exp (a*z)).comp z ((hasDerivAt_id z).const_mul a)
  exact hD.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hDeriv z).hasDerivWithinAt) (fun z hz => by
      rw [norm_mul, Complex.norm_exp, mul_comm]
      gcongr
      exact hB z hz) hu hv

private def scaledPair (p : ℂ × ℂ) : ℂ × ℂ := (p.1, 50*p.2)
private def unscalePair (p : ℂ × ℂ) : ℂ × ℂ := (p.1, p.2/50)
private def scaledStep (L : ℂ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (exp ((L/50)*p.2), 50*exp (-L*p.1))

private theorem unscale_step (L : ℂ) (p : ℂ × ℂ) :
    unscalePair (scaledStep L p) = step L (unscalePair p) := by
  apply Prod.ext
  · change exp ((L/50)*p.2) = exp (L*(p.2/50))
    congr 1
    ring
  · change (50:ℂ)*exp (-L*p.1)/50 = exp (-L*p.1)
    ring

private theorem unscale_scale (p : ℂ × ℂ) : unscalePair (scaledPair p) = p := by
  apply Prod.ext
  · rfl
  · change (50:ℂ)*p.2/50 = p.2
    ring

private theorem capOrbit_add_updates (L : ℂ) (N n : ℕ) :
    capOrbit L (N+n) = (step L)^[n] (capOrbit L N) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ, capOrbit, ih, Function.iterate_succ_apply']

private theorem neg_phase_re_le {L p : ℂ} (hre : 8 ≤ L.re) (hn : ‖L‖ ≤ 16)
    (hp : ‖p-1‖ ≤ 1/20) : (-L*p).re ≤ -7 := by
  rw [show -L*p = -L + -L*(p-1) by ring, add_re, neg_re]
  have hmul : (-L*(p-1)).re ≤ 4/5 := by
    calc
      _ ≤ ‖-L*(p-1)‖ := Complex.re_le_norm _
      _ = ‖L‖ * ‖p-1‖ := by rw [norm_mul, norm_neg]
      _ ≤ 16 * (1/20 : ℝ) := mul_le_mul hn hp (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  linarith

private theorem neg_phase_small {L p : ℂ} (hre : 8 ≤ L.re) (hn : ‖L‖ ≤ 16)
    (hp : ‖p-1‖ ≤ 1/20) : ‖exp (-L*p)‖ ≤ 1/1000 := by
  rw [Complex.norm_exp]
  exact (Real.exp_le_exp.mpr (neg_phase_re_le hre hn hp)).trans exp_neg_seven_lt.le

theorem pos_phase_near_one {L q : ℂ} (hn : ‖L‖ ≤ 16)
    (hq : ‖q‖ ≤ 1/1000) : ‖exp (L*q)-1‖ ≤ 1/20 := by
  have ha : ‖L*q‖ ≤ 2/125 := by
    rw [norm_mul]
    exact (mul_le_mul hn hq (norm_nonneg _) (by norm_num)).trans (by norm_num)
  have ht := Complex.norm_exp_sub_one_sub_id_le (ha.trans (by norm_num))
  have htel : exp (L*q)-1 = (exp (L*q)-1-L*q) + L*q := by ring
  have hsq := pow_le_pow_left₀ (norm_nonneg (L*q)) ha 2
  calc
    ‖exp (L*q)-1‖ = ‖(exp (L*q)-1-L*q) + L*q‖ := congrArg norm htel
    _ ≤ ‖exp (L*q)-1-L*q‖ + ‖L*q‖ := norm_add_le _ _
    _ ≤ ‖L*q‖^2 + ‖L*q‖ := add_le_add ht le_rfl
    _ ≤ 1/20 := by linarith

/-- Entry at any finite update into the two trapping disks forces the
whole cap orbit to converge to a fixed pair. -/
theorem cap_tendsto_fixed_of_box_entry {L : ℂ} (hre : 8 ≤ L.re) (hn : ‖L‖ ≤ 16)
    {N : ℕ} (hpentry : ‖(capOrbit L N).1-1‖ ≤ 1/20)
    (hqentry : ‖(capOrbit L N).2‖ ≤ 1/1000) :
    ∃ z : ℂ × ℂ, step L z = z ∧ ‖z.1-1‖ ≤ 1/20 ∧ ‖z.2‖ ≤ 1/1000 ∧
      Tendsto (capOrbit L) atTop (𝓝 z) := by
  let P := Metric.closedBall (1:ℂ) (1/20)
  let Q := Metric.closedBall (0:ℂ) (1/20)
  let D := P ×ˢ Q
  have hn' : ‖L/50‖ ≤ 8/25 := by rw [norm_div]; norm_num; linarith
  have hP (p : ℂ) (hp : p ∈ P) : ‖p-1‖ ≤ 1/20 :=
    by simpa only [P, Metric.mem_closedBall, dist_eq_norm] using hp
  have hQ (q : ℂ) (hq : q ∈ Q) : ‖q‖ ≤ 1/20 :=
    by simpa only [Q, Metric.mem_closedBall, dist_zero_right] using hq
  have hpos (q : ℂ) (hq : q ∈ Q) : ((L/50)*q).re ≤ 2/125 := by
    calc
      _ ≤ ‖(L/50)*q‖ := Complex.re_le_norm _
      _ = ‖L/50‖ * ‖q‖ := norm_mul _ _
      _ ≤ (8/25 : ℝ) * (1/20) := mul_le_mul hn' (hQ q hq) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hneg (p : ℂ) (hp : p ∈ P) : (-L*p).re ≤ -7 :=
    neg_phase_re_le hre hn (hP p hp)
  have hplus {u v : ℂ} (hu : u ∈ Q) (hv : v ∈ Q) :
      ‖exp ((L/50)*v) - exp ((L/50)*u)‖ ≤ (16/25) * ‖v-u‖ := by
    refine (exp_mul_difference (convex_closedBall _ _) hpos hu hv).trans ?_
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (mul_le_mul hn' exp_small_le_two (Real.exp_pos _).le (by norm_num)).trans (by norm_num)
  have hminus {u v : ℂ} (hu : u ∈ P) (hv : v ∈ P) :
      ‖(50:ℂ)*exp (-L*v) - 50*exp (-L*u)‖ ≤ (4/5) * ‖v-u‖ := by
    rw [← mul_sub, norm_mul, show ‖(50:ℂ)‖ = 50 by norm_num]
    have hward := exp_mul_difference (convex_closedBall _ _) hneg hu hv
    rw [norm_neg] at hward
    calc
      _ ≤ 50 * ((‖L‖ * Real.exp (-7)) * ‖v-u‖) := by gcongr
      _ = (50 * (‖L‖ * Real.exp (-7))) * ‖v-u‖ := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        have hval := mul_le_mul hn exp_neg_seven_lt.le (Real.exp_pos _).le (by norm_num : (0:ℝ) ≤ 16)
        linarith
  have hplus_maps {q : ℂ} (hq : q ∈ Q) : exp ((L/50)*q) ∈ P := by
    have h0 : (0:ℂ) ∈ Q := by simp [Q]
    have h := hplus h0 hq
    simp only [mul_zero, exp_zero, sub_zero] at h
    change exp ((L/50)*q) ∈ Metric.closedBall (1:ℂ) (1/20)
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hsq := hQ q hq
    linarith
  have hminus_maps {p : ℂ} (hp : p ∈ P) : (50:ℂ)*exp (-L*p) ∈ Q := by
    change (50:ℂ)*exp (-L*p) ∈ Metric.closedBall (0:ℂ) (1/20)
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_exp,
      show ‖(50:ℂ)‖ = 50 by norm_num]
    have h := (Real.exp_le_exp.mpr (hneg p hp)).trans exp_neg_seven_lt.le
    linarith
  have hmap : MapsTo (scaledStep L) D D := fun _ h =>
    ⟨hplus_maps h.2, hminus_maps h.1⟩
  have hclosed : IsClosed D := Metric.isClosed_closedBall.prod Metric.isClosed_closedBall
  have hcapture : scaledPair (capOrbit L N) ∈ D := by
    refine ⟨?_, ?_⟩
    · simpa only [P, scaledPair, Metric.mem_closedBall, dist_eq_norm] using hpentry
    · change (50:ℂ)*(capOrbit L N).2 ∈ Metric.closedBall (0:ℂ) (1/20)
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul, show ‖(50:ℂ)‖ = 50 by norm_num]
      linarith
  have hcontract : ContractingWith (4/5 : ℝ≥0) (hmap.restrict (scaledStep L) D D) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul fun p q => ?_⟩
    change dist (scaledStep L p.val) (scaledStep L q.val) ≤ (4/5 : ℝ) * dist p.val q.val
    rw [Prod.dist_eq, Prod.dist_eq]
    simp only [dist_eq_norm, scaledStep]
    apply max_le
    · have hd := hplus q.property.2 p.property.2
      refine hd.trans ?_
      have h := le_max_right (‖p.val.1-q.val.1‖) (‖p.val.2-q.val.2‖)
      have h₀ := norm_nonneg (p.val.2 - q.val.2)
      linarith
    · have hd := hminus q.property.1 p.property.1
      exact hd.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))
  obtain ⟨p, hp, hfix, hlim, _⟩ :=
    hcontract.exists_fixedPoint' hclosed.isComplete hmap hcapture (edist_ne_top _ _)
  refine ⟨unscalePair p, ?_, ?_, ?_, ?_⟩
  · rw [← unscale_step, hfix.eq]
  · exact hP p.1 hp.1
  · change ‖p.2/50‖ ≤ _
    rw [norm_div, show ‖(50:ℂ)‖ = 50 by norm_num]
    have h := hQ p.2 hp.2
    linarith
  · have hcont : Continuous unscalePair :=
      continuous_fst.prodMk (continuous_snd.div_const _)
    have hlim' := hcont.continuousAt.tendsto.comp hlim
    apply (tendsto_add_atTop_iff_nat N).mp
    have hsem : Semiconj unscalePair (scaledStep L) (step L) := unscale_step L
    apply hlim'.congr
    intro n
    change unscalePair ((scaledStep L)^[n] (scaledPair (capOrbit L N))) = capOrbit L (n+N)
    rw [hsem.iterate_right, unscale_scale, Nat.add_comm n N, capOrbit_add_updates]

/-- A bound on the exponent fed by the first positive phase forces the
original cap to converge to a fixed pair. -/
theorem cap_tendsto_fixed_of_first_phase {L : ℂ} (hre : 8 ≤ L.re) (hn : ‖L‖ ≤ 16)
    (hfirst : (-L * exp L).re ≤ -8) :
    ∃ z : ℂ × ℂ, step L z = z ∧ ‖z.1-1‖ ≤ 1/20 ∧ ‖z.2‖ ≤ 1/1000 ∧
      Tendsto (capOrbit L) atTop (𝓝 z) := by
  apply cap_tendsto_fixed_of_box_entry hre hn (N := 2)
  · have hq1 : ‖exp (-L)‖ ≤ 1/1000 := by
      simpa only [mul_one] using neg_phase_small hre hn (p := 1) (by norm_num)
    simpa [capOrbit, step] using pos_phase_near_one hn hq1
  · simp only [capOrbit, step, mul_one, Complex.norm_exp]
    exact (Real.exp_le_exp.mpr (hfirst.trans (by norm_num))).trans exp_neg_seven_lt.le

/-- The even first phase stays in its small disk regardless of the size
of the interleaved second-phase orbit. -/
theorem cap_even_first_near_one {L : ℂ} (hre : 8 ≤ L.re) (hn : ‖L‖ ≤ 16)
    (n : ℕ) : ‖(capOrbit L (2*n)).1-1‖ ≤ 1/20 := by
  induction n with
  | zero => norm_num [capOrbit]
  | succ n ih =>
    rw [Nat.mul_succ]
    change ‖exp (L*exp (-L*(capOrbit L (2*n)).1))-1‖ ≤ 1/20
    exact pos_phase_near_one hn (neg_phase_small hre hn ih)

/-- The exponent in the capture test is determined by the real and imaginary
parts of the lift after the first positive update. -/
theorem first_phase_exponent_re (L : ℂ) :
    (-L*exp L).re = Real.exp L.re * (L.im * Real.sin L.im - L.re * Real.cos L.im) := by
  rw [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.exp_re, Complex.exp_im]
  ring

/-- In the extended atlas these parameters lie in certified period-one
bands around each even multiple of pi within the plotted range. -/
theorem cap_tendsto_fixed_near_even_pi {L : ℂ} (hre : 8 ≤ L.re) (hmax : L.re ≤ 12)
    (him : |L.im| ≤ 3*Real.pi) (k : ℤ)
    (hnear : |L.im - k*(2*Real.pi)| ≤ 1/2) :
    ∃ z : ℂ × ℂ, step L z = z ∧ ‖z.1-1‖ ≤ 1/20 ∧ ‖z.2‖ ≤ 1/1000 ∧
      Tendsto (capOrbit L) atTop (𝓝 z) := by
  have hImTen : |L.im| ≤ 10 := by linarith [Real.pi_lt_d2]
  have hN : ‖L‖ ≤ 16 := by
    have hRe2 : L.re^2 ≤ 12^2 := by nlinarith
    have hIm2 : L.im^2 ≤ 10^2 := by
      have hh := abs_le.mp hImTen
      nlinarith
    have hsq := Complex.sq_norm L
    rw [Complex.normSq_apply] at hsq
    nlinarith [norm_nonneg L]
  let u := L.im - k*(2*Real.pi)
  have hphase : u + k*(2*Real.pi) = L.im := by dsimp [u]; ring
  have hsin : |Real.sin L.im| ≤ 1/2 := by
    rw [← hphase, Real.sin_add_int_mul_two_pi]
    exact (Real.abs_sin_le_abs).trans hnear
  have hcos : 7/8 ≤ Real.cos L.im := by
    rw [← hphase, Real.cos_add_int_mul_two_pi]
    have hb := abs_le.mp hnear
    have hs : u^2 ≤ 1/4 := by nlinarith
    have hc := Real.one_sub_sq_div_two_le_cos (x := u)
    linarith
  have hS : L.im * Real.sin L.im ≤ 5 := by
    calc
      _ ≤ |L.im * Real.sin L.im| := le_abs_self _
      _ ≤ _ := by rw [abs_mul]; calc
        |L.im| * |Real.sin L.im| ≤ 10 * (1/2 : ℝ) :=
          mul_le_mul hImTen hsin (abs_nonneg _) (by norm_num)
        _ = _ := by norm_num
  have hC : 7 ≤ L.re * Real.cos L.im := by
    have h := mul_le_mul hre hcos (by norm_num : (0:ℝ) ≤ 7/8) (by linarith : 0 ≤ L.re)
    norm_num at h
    exact h
  have hE : 4 ≤ Real.exp L.re := by linarith [Real.add_one_le_exp L.re]
  have hfirst : (-L*exp L).re ≤ -8 := by
    rw [first_phase_exponent_re]
    have hs : L.im * Real.sin L.im - L.re * Real.cos L.im ≤ -2 := by linarith
    calc
      _ ≤ Real.exp L.re * (-2) := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ ≤ _ := by linarith
  exact cap_tendsto_fixed_of_first_phase hre hN hfirst

/-- Parameter negation swaps the two phases, so the capture bands hold
on both outer sides of the extended atlas. -/
theorem cap_tendsto_fixed_in_outer_bands {L : ℂ} (hre : 8 ≤ |L.re|) (hmax : |L.re| ≤ 12)
    (him : |L.im| ≤ 3*Real.pi) (k : ℤ)
    (hnear : |L.im - k*(2*Real.pi)| ≤ 1/2) :
    ∃ z : ℂ × ℂ, step L z = z ∧ Tendsto (capOrbit L) atTop (𝓝 z) := by
  by_cases hpos : 0 ≤ L.re
  · rw [abs_of_nonneg hpos] at hre hmax
    obtain ⟨z, hz, _, _, hcap⟩ := cap_tendsto_fixed_near_even_pi hre hmax him k hnear
    exact ⟨z, hz, hcap⟩
  · have hn : L.re ≤ 0 := le_of_not_ge hpos
    rw [abs_of_nonpos hn] at hre hmax
    have hRe : 8 ≤ (-L).re := by rwa [neg_re]
    have hRe' : (-L).re ≤ 12 := by rwa [neg_re]
    have hi : |(-L).im| ≤ 3*Real.pi := by simpa only [neg_im, abs_neg]
    have hh : |(-L).im - (-k : ℤ)*(2*Real.pi)| ≤ 1/2 := by
      rw [show (-L).im - (-k : ℤ)*(2*Real.pi) = -(L.im - k*(2*Real.pi)) by
        simp only [neg_im, Int.cast_neg]; ring, abs_neg]
      exact hnear
    obtain ⟨z, hz, _, _, hcap⟩ := cap_tendsto_fixed_near_even_pi hRe hRe' hi (-k) hh
    refine ⟨z.swap, ?_, ?_⟩
    · have hs : step L z.swap = (step (-L) z).swap := by simp [step, Prod.swap]
      rw [hs, hz]
    · have hs : Continuous (Prod.swap : (ℂ × ℂ) → ℂ × ℂ) := continuous_swap
      apply (hs.continuousAt.tendsto.comp hcap).congr
      intro n
      simp only [Function.comp_apply, cap_neg, Prod.swap_swap]

#print axioms cap_tendsto_fixed_of_box_entry
#print axioms cap_even_first_near_one
#print axioms cap_tendsto_fixed_of_first_phase
#print axioms first_phase_exponent_re
#print axioms cap_tendsto_fixed_near_even_pi
#print axioms cap_tendsto_fixed_in_outer_bands

end SuperZeta.Reciprocal
