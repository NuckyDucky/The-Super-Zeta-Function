import SuperZeta.Oriented.LiuConnection
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting

/-! What pointwise derivative and center residual bounds certify about an actual
    zero of the bilateral Hurwitz reference. The arithmetic evaluation of these
    bounds is external. No zero ordinate occurs in these theorems. -/
noncomputable section
namespace DottieOriented.CertificateLogic
open Complex DottieOriented.LiuConnection
open scoped NNReal

/-- The preconditioner D stays fixed throughout each certified disk. -/
def newtonStep (b : ℝ) (D z : ℂ) : ℂ := z - reference b z / D

/-- These are analytic inequalities on the actual reference, rather than a
    supplied root or an assertion of branch uniqueness. -/
structure DiskBounds (b : ℝ) (D c : ℂ) (r : ℝ) (q : ℝ≥0) : Prop where
  denominator : D ≠ 0
  radius : 0 ≤ r
  contracts : q < 1
  residual : ‖reference b c / D‖ + (q:ℝ)*r ≤ r
  derivative : ∀ z ∈ Metric.closedBall c r, DifferentiableAt ℂ (reference b) z ∧
    ‖1 - deriv (reference b) z / D‖ ≤ (q:ℝ)

variable {b : ℝ} {D c : ℂ} {r : ℝ} {q : ℝ≥0}

theorem newton_lipschitz (h : DiskBounds b D c r q)
    {x y : ℂ} (hx : x ∈ Metric.closedBall c r) (hy : y ∈ Metric.closedBall c r) :
    ‖newtonStep b D y - newtonStep b D x‖ ≤ (q:ℝ)*‖y-x‖ := by
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s:=Metric.closedBall c r) (f':=fun z => 1 - deriv (reference b) z / D)
  · intro z hz
    exact ((hasDerivAt_id z).sub ((h.derivative z hz).1.hasDerivAt.div_const D)).hasDerivWithinAt
  · exact fun z hz => (h.derivative z hz).2
  · exact convex_closedBall _ _
  · exact hx
  · exact hy

theorem reference_derivative_ne_zero (h : DiskBounds b D c r q)
    {z : ℂ} (hz : z ∈ Metric.closedBall c r) : deriv (reference b) z ≠ 0 := by
  intro hzero
  have hv := (h.derivative z hz).2
  simp [hzero] at hv
  exact (not_le_of_gt (show (q:ℝ)<1 from h.contracts)) hv

private theorem fixed_iff_zero (hD : D ≠ 0) (z : ℂ) :
    Function.IsFixedPt (newtonStep b D) z ↔ reference b z = 0 := by
  change z - reference b z / D = z ↔ reference b z = 0
  constructor
  · intro h
    have hz : reference b z / D = 0 := by linear_combination -h
    exact (div_eq_zero_iff.mp hz).resolve_right hD
  · intro h; simp [h]

/-- Banach and the complex mean-value estimate give existence and uniqueness.
    Neither conclusion appears among the inputs. -/
theorem unique_reference_zero (h : DiskBounds b D c r q) :
    ∃! z : ℂ, z ∈ Metric.closedBall c r ∧ reference b z = 0 := by
  let S := Metric.closedBall c r
  let f := newtonStep b D
  have hc : c ∈ S := Metric.mem_closedBall_self h.radius
  have hmap : Set.MapsTo f S S := by
    intro z hz
    have tri := norm_sub_le_norm_sub_add_norm_sub (f z) (f c) c
    have hb := newton_lipschitz h hc hz
    have hm := mul_le_mul_of_nonneg_left
      (show ‖z-c‖≤r by simpa [S,Metric.mem_closedBall,dist_eq_norm] using hz) q.coe_nonneg
    have he : ‖f c-c‖ = ‖reference b c / D‖ := by
      simp [f,newtonStep,sub_sub_cancel_left]
    rw [he] at tri
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    exact tri.trans (by linarith only [hb,hm,h.residual])
  have ht : ContractingWith q (hmap.restrict f S S) :=
    ⟨h.contracts, LipschitzWith.of_dist_le_mul fun x y => by
      change dist (f x.val) (f y.val) ≤ (q:ℝ)*dist x.val y.val
      simpa only [dist_eq_norm] using newton_lipschitz h y.property x.property⟩
  obtain ⟨z,hz,hfix,_⟩ := ht.exists_fixedPoint' Metric.isClosed_closedBall.isComplete
    hmap hc (edist_ne_top _ _)
  refine ⟨z,⟨hz,(fixed_iff_zero h.denominator z).mp hfix⟩,?_⟩
  intro y hy
  have hfy := (fixed_iff_zero h.denominator y).mpr hy.2
  have heq : (⟨y,hy.1⟩ : S) = ⟨z,hz⟩ := ht.fixedPoint_unique'
    (Subtype.ext hfy) (Subtype.ext hfix)
  exact congrArg Subtype.val heq

/-- At a joint parameter, two small endpoint disks in a common contracting
    disk select the same root. Closed-ball inclusions can be obtained directly
    from the center distances and radii. -/
theorem glue_at_endpoint (h : DiskBounds b D c r q) {u v x y : ℂ} {a d : ℝ}
    (hleft : dist u c + a ≤ r) (hright : dist v c + d ≤ r)
    (hx : x ∈ Metric.closedBall u a) (hy : y ∈ Metric.closedBall v d)
    (hfx : reference b x = 0) (hfy : reference b y = 0) : x = y := by
  obtain ⟨z,_,hu⟩ := unique_reference_zero h
  have hm {w p : ℂ} {e : ℝ} (hi : dist p c + e ≤ r) (hw : w ∈ Metric.closedBall p e) :
      w ∈ Metric.closedBall c r := by
    exact Metric.mem_closedBall.mpr ((dist_triangle w p c).trans (by
      linarith only [Metric.mem_closedBall.mp hw,hi]))
  exact (hu x ⟨hm hleft hx,hfx⟩).trans (hu y ⟨hm hright hy,hfy⟩).symm

/-- A zero at a second shift moves by at most the residual at its former
    address divided by the contraction gap. This addresses continuity as b
    varies, in addition to existence at each fixed shift. -/
theorem root_motion (h : DiskBounds b D c r q) {t : ℝ} {x y : ℂ}
    (hx : x ∈ Metric.closedBall c r) (hy : y ∈ Metric.closedBall c r)
    (hbx : reference b x = 0) (hty : reference t y = 0) :
    (1 - (q:ℝ))*‖y-x‖ ≤ ‖(reference b y - reference t y) / D‖ := by
  have hl := newton_lipschitz h hx hy
  have hfix : newtonStep b D x = x := by simp [newtonStep,hbx]
  rw [hfix] at hl
  have ht := norm_sub_le_norm_sub_add_norm_sub y (newtonStep b D y) x
  have hres : y - newtonStep b D y = reference b y / D := by simp [newtonStep]
  rw [hres] at ht
  simp only [hty,sub_zero]
  linarith only [ht,hl]

/-- A uniform parameter derivative/variation bound gives a Lipschitz bound
    for the isolated zero section. K bounds changes of the scaled reference
    at a fixed w per unit change in the real Hurwitz shift. -/
theorem branch_lipschitz (I : Set ℝ) (root : ℝ → ℂ) (K : ℝ)
    (h : ∀ b ∈ I, DiskBounds b D c r q)
    (hz : ∀ t ∈ I, root t ∈ Metric.closedBall c r ∧ reference t (root t) = 0)
    (hb : ∀ b ∈ I, ∀ t ∈ I, ∀ w ∈ Metric.closedBall c r,
        ‖(reference b w - reference t w) / D‖ ≤ K * ‖t-b‖)
    {b t : ℝ} (hbi : b ∈ I) (hti : t ∈ I) :
    ‖root t - root b‖ ≤ (K / (1 - (q:ℝ))) * ‖t-b‖ := by
  have bound := root_motion (h b hbi) (hz b hbi).1 (hz t hti).1 (hz b hbi).2 (hz t hti).2
  have full := bound.trans (hb b hbi t hti (root t) (hz t hti).1)
  have gap : 0 < 1 - (q:ℝ) := sub_pos.mpr ((h b hbi).contracts : (q:ℝ)<1)
  rw [div_mul_eq_mul_div, le_div_iff₀ gap]
  simpa only [mul_comm (1-(q:ℝ))] using full

/-- The branch itself is constructed from the interval inequalities. No
    choice of incoming roots or a pre-existing continuous section is an input. -/
theorem exists_lipschitz_branch (I : Set ℝ) (K : ℝ)
    (h : ∀ b ∈ I, DiskBounds b D c r q)
    (hb : ∀ b ∈ I, ∀ t ∈ I, ∀ w ∈ Metric.closedBall c r,
        ‖(reference b w - reference t w) / D‖ ≤ K * ‖t-b‖) :
    ∃ root : ℝ → ℂ,
      (∀ t ∈ I, root t ∈ Metric.closedBall c r ∧ reference t (root t) = 0) ∧
      (∀ b ∈ I, ∀ t ∈ I, ‖root t-root b‖ ≤ (K/(1-(q:ℝ)))*‖t-b‖) ∧
      (∀ t ∈ I, ∀ y ∈ Metric.closedBall c r, reference t y = 0 → y = root t) := by
  classical
  let root (t : ℝ) := if ht : t ∈ I then (unique_reference_zero (h t ht)).choose else c
  have hz (t : ℝ) (ht : t ∈ I) : root t ∈ Metric.closedBall c r ∧ reference t (root t) = 0 := by
    simpa [root,ht] using (unique_reference_zero (h t ht)).choose_spec.1
  refine ⟨root,hz,fun _ hbi _ hti => branch_lipschitz I root K h hz hb hbi hti,?_⟩
  intro t ht y hy hfy
  simpa [root,ht] using (unique_reference_zero (h t ht)).choose_spec.2 y ⟨hy,hfy⟩

end DottieOriented.CertificateLogic
