import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

namespace AlpogeSuperZeta

open Complex Filter Metric Set
open scoped Topology

private theorem differentiableOn_log_lift {R : ℝ} {f l : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hl : ContinuousOn l (ball 0 R))
    (he : EqOn (Complex.exp ∘ l) f (ball 0 R))
    (hn : ∀ z ∈ ball (0 : ℂ) R, f z ≠ 0) :
    DifferentiableOn ℂ l (ball 0 R) := by
  intro z hz
  have hball : ball (0 : ℂ) R ∈ 𝓝 z := isOpen_ball.mem_nhds hz
  have hcont : ContinuousAt (fun v => (l v - l z).im) z :=
    Complex.continuous_im.continuousAt.comp
      ((hl.continuousAt hball).sub continuousAt_const)
  have hphase : ∀ᶠ v in 𝓝 z, (l v - l z).im ∈ Ioo (-Real.pi) Real.pi := by
    apply hcont.eventually
    apply isOpen_Ioo.mem_nhds
    simpa only [sub_self, zero_im, mem_Ioo, neg_lt_zero] using
      And.intro Real.pi_pos Real.pi_pos
  have hloc : l =ᶠ[𝓝 z] (fun v => l z + Complex.log (f v / f z)) := by
    filter_upwards [hball, hphase] with v hv hp
    have hquot : Complex.exp (l v - l z) = f v / f z := by
      rw [Complex.exp_sub]
      exact congrArg₂ (· / ·) (he hv) (he hz)
    rw [← hquot, Complex.log_exp hp.1 hp.2.le, add_sub_cancel]
  have hq : DifferentiableAt ℂ (fun v => f v / f z) z :=
    (hf.differentiableAt hball).div_const (f z)
  have hq₁ : f z / f z ∈ slitPlane := by simp [hn z hz]
  have hd : DifferentiableAt ℂ (fun v => l z + Complex.log (f v / f z)) z :=
    ((Complex.differentiableAt_log hq₁).comp z hq).const_add _
  exact (hd.congr_of_eventuallyEq hloc).differentiableWithinAt

/-- Bound the logarithmic derivative using a disk of radius `d` about the
evaluation point and an enclosing zero-free disk of radius `R`. -/
theorem logDeriv_le_disk_buffer {f : ℂ → ℂ} {b B R r d : ℝ}
    (hd : 0 < d) (hr : 0 ≤ r) (hrd : r + d < R)
    (hb : 0 < b) (hcenter : b ≤ ‖f 0‖)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hn : ∀ z ∈ ball (0 : ℂ) R, f z ≠ 0)
    (hupper : ∀ z ∈ ball (0 : ℂ) R, ‖f z‖ ≤ B)
    {u : ℂ} (hu : ‖u‖ ≤ r) :
    ‖logDeriv f u‖ ≤ (2 * (r + d) / (R - (r + d)) / d) *
      (Real.log B - Real.log b + 1) := by
  have hR : 0 < R := by linarith
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hB : b ≤ B := hcenter.trans (hupper 0 hzero)
  let M := Real.log B - Real.log b + 1
  have hM : 0 < M := by
    have hlog := Real.log_le_log hb hB
    dsimp [M]
    linarith
  have hs : IsSimplyConnected (ball (0 : ℂ) R) := by
    have := Metric.contractibleSpace_ball (x := (0 : ℂ)) hR
    exact inferInstanceAs (SimplyConnectedSpace (ball (0 : ℂ) R))
  have hno : (0 : ℂ) ∉ f '' ball (0 : ℂ) R := by
    rintro ⟨z, hz, hfz⟩
    exact hn z hz hfz
  obtain ⟨l, hcont, he⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hs isOpen_ball hf.continuousOn hno
  have hld := differentiableOn_log_lift hf hcont he hn
  let L := fun z => l z - l 0
  have hL : DifferentiableOn ℂ L (ball 0 R) := hld.sub_const _
  have hL₀ : L 0 = 0 := sub_self _
  have hre (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      (l z).re = Real.log ‖f z‖ := by
    have he' : Complex.exp (l z) = f z := he hz
    rw [← he', Complex.norm_exp, Real.log_exp]
  have hRe : MapsTo L (ball 0 R) {z | z.re ≤ M} := by
    intro z hz
    have hlog₁ := Real.log_le_log (norm_pos_iff.mpr (hn z hz)) (hupper z hz)
    have hlog₂ := Real.log_le_log hb hcenter
    change (L z).re ≤ M
    simp only [L, sub_re, hre z hz, hre 0 hzero]
    dsimp [M]
    linarith
  have huR : u ∈ ball (0 : ℂ) R := (mem_ball_zero_iff).mpr (by linarith)
  have hdist : ∀ v ∈ closedBall u d, ‖v‖ ≤ r + d := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm] at hv
    have htri : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
      simpa only [sub_add_cancel] using norm_add_le (v - u) u
    linarith
  have hsubset : closedBall u d ⊆ ball 0 R :=
    fun v hv => mem_ball_zero_iff.mpr (by linarith [hdist v hv])
  have hbd : ∀ v ∈ sphere u d, ‖L v‖ ≤ 2 * M * (r + d) / (R - (r + d)) := by
    intro v hv
    have hv' := sphere_subset_closedBall hv
    have hnr := hdist v hv'
    have hbc := Complex.borelCaratheodory_zero hM hL hRe hR (hsubset hv') hL₀
    refine hbc.trans ?_
    have hden : 0 < R - (r + d) := sub_pos.mpr hrd
    calc
      _ ≤ (2 * M * (r + d)) / (R - ‖v‖) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnr (by positivity))
          (by linarith)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hden (by linarith)
  have hderiv := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hd
    (hL.diffContOnCl_ball hsubset) hbd
  have hlAt := (hld.differentiableAt (isOpen_ball.mem_nhds huR)).hasDerivAt
  have hLAt : deriv L u = deriv l u := hlAt.sub_const (l 0) |>.deriv
  have hExp : HasDerivAt f (Complex.exp (l u) * deriv l u) u := by
    apply ((Complex.hasDerivAt_exp (l u)).comp u hlAt).congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds huR] with v hv
    exact (he hv).symm
  have hEq : logDeriv f u = deriv L u := by
    rw [logDeriv_apply, hExp.deriv, hLAt]
    change Complex.exp (l u) * deriv l u / f u = _
    have he' : Complex.exp (l u) = f u := he huR
    rw [he', mul_comm, mul_div_cancel_right₀ _ (hn u huR)]
  rw [hEq]
  calc
    ‖deriv L u‖ ≤ (2 * M * (r + d) / (R - (r + d))) / d := hderiv
    _ = _ := by dsimp [M]; ring

/-- The fixed strip used for the higher-power estimate. -/
theorem logDeriv_le_disk {f : ℂ → ℂ} {b B : ℝ}
    (hb : 0 < b) (hcenter : b ≤ ‖f 0‖)
    (hf : DifferentiableOn ℂ f (ball 0 (7 / 5)))
    (hn : ∀ z ∈ ball (0 : ℂ) (7 / 5), f z ≠ 0)
    (hupper : ∀ z ∈ ball (0 : ℂ) (7 / 5), ‖f z‖ ≤ B)
    {u : ℂ} (hu : ‖u‖ ≤ 5 / 4) :
    ‖logDeriv f u‖ ≤ 520 * (Real.log B - Real.log b + 1) := by
  have h := logDeriv_le_disk_buffer (R := 7 / 5) (r := 5 / 4) (d := 1 / 20)
    (by norm_num) (by norm_num) (by norm_num)
    hb hcenter hf hn hupper hu
  norm_num at h
  exact h

#print axioms logDeriv_le_disk_buffer
#print axioms logDeriv_le_disk

end AlpogeSuperZeta
