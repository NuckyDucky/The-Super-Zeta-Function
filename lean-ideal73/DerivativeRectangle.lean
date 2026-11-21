import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Order.IntermediateValue

/-! A one-sided derivative test on a closed rectangle meeting the critical line.
All derivative and sign premises are displayed. The numerical prefix and the
infinite Gaussian remainder must be identified separately to apply this result. -/

namespace GaussianRectangle
open Set Complex

def point (x t : ℝ) : ℂ := (x : ℂ) + (t : ℂ) * I

theorem real_on_line_of_reflection {F : ℂ → ℂ}
    (h : ∀ w, F (1 - (starRingEnd ℂ) w) = (starRingEnd ℂ) (F w)) (t : ℝ) :
    (F (point (1/2) t)).im = 0 := by
  have e : 1 - (starRingEnd ℂ) (point (1/2) t) = point (1/2) t := by
    apply Complex.ext <;> norm_num [point]
  have hi := congrArg Complex.im (h (point (1/2) t))
  rw [e, Complex.conj_im] at hi
  linarith

private lemma horizontal {F : ℂ → ℂ} {d : ℂ} {x t : ℝ}
    (h : HasDerivAt F d (point x t)) :
    HasDerivAt (fun u : ℝ => (F (point u t)).im) d.im x := by
  have g : HasDerivAt (fun u : ℂ => F (u + (t : ℂ) * I)) d (x : ℂ) := by
    simpa [point, Function.comp_def] using h.comp (x : ℂ) ((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ) * I))
  exact imCLM.hasFDerivAt.comp_hasDerivAt x g.comp_ofReal

private lemma vertical {F : ℂ → ℂ} {d : ℂ} {x t : ℝ}
    (h : HasDerivAt F d (point x t)) :
    HasDerivAt (fun v : ℝ => (F (point x v)).re) (-d.im) t := by
  have g : HasDerivAt (fun v : ℂ => F ((x : ℂ) + v * I)) (d * I) (t : ℂ) := by
    simpa [point, Function.comp_def] using h.comp (t : ℂ)
      (((hasDerivAt_id (t : ℂ)).mul_const I).const_add (x : ℂ))
  simpa [point] using g.real_of_complex

variable {F D : ℂ → ℂ} {a b l u : ℝ}

/-- A strictly decreasing imaginary part along each horizontal segment has its
only possible zero at the point on the real-valued symmetry line. -/
theorem zero_on_line
    (hc : (1/2 : ℝ) ∈ Icc a b)
    (hreal : ∀ t ∈ Icc l u, (F (point (1/2) t)).im = 0)
    (hd : ∀ x ∈ Icc a b, ∀ t ∈ Icc l u, HasDerivAt F (D (point x t)) (point x t))
    (hneg : ∀ x ∈ Icc a b, ∀ t ∈ Icc l u, (D (point x t)).im < 0)
    {x t : ℝ} (hx : x ∈ Icc a b) (ht : t ∈ Icc l u) (hz : F (point x t) = 0) :
    x = 1/2 := by
  let g := fun r : ℝ => (F (point r t)).im
  have dg (r : ℝ) (hr : r ∈ Icc a b) : HasDerivAt g (D (point r t)).im r :=
    horizontal (hd r hr t ht)
  have mono : StrictAntiOn g (Icc a b) := strictAntiOn_of_deriv_neg (convex_Icc a b)
    (fun r hr => (dg r hr).continuousAt.continuousWithinAt) (fun r hr => by
      rw [(dg r (interior_subset hr)).deriv]
      exact hneg r (interior_subset hr) t ht)
  apply mono.injOn hx hc
  change (F (point x t)).im = (F (point (1/2) t)).im
  rw [hz, hreal t ht, Complex.zero_im]

/-- Endpoint signs give exactly one zero height on the line. The nonzero
complex derivative there makes the zero simple. Combine with `zero_on_line`
to exhaust the whole rectangle. -/
theorem unique_simple_on_line
    (hlu : l ≤ u)
    (hreal : ∀ t ∈ Icc l u, (F (point (1/2) t)).im = 0)
    (hd : ∀ t ∈ Icc l u, HasDerivAt F (D (point (1/2) t)) (point (1/2) t))
    (hneg : ∀ t ∈ Icc l u, (D (point (1/2) t)).im < 0)
    (hl : (F (point (1/2) l)).re ≤ 0) (hu : 0 ≤ (F (point (1/2) u)).re) :
    ∃ t ∈ Icc l u, F (point (1/2) t) = 0 ∧ D (point (1/2) t) ≠ 0 ∧
      ∀ s ∈ Icc l u, F (point (1/2) s) = 0 → s = t := by
  let g := fun r : ℝ => (F (point (1/2) r)).re
  have dg (r : ℝ) (hr : r ∈ Icc l u) : HasDerivAt g (-(D (point (1/2) r)).im) r :=
    vertical (hd r hr)
  have cont : ContinuousOn g (Icc l u) := fun r hr => (dg r hr).continuousAt.continuousWithinAt
  have mono : StrictMonoOn g (Icc l u) := strictMonoOn_of_deriv_pos (convex_Icc l u) cont
    (fun r hr => by rw [(dg r (interior_subset hr)).deriv]; exact neg_pos.mpr (hneg r (interior_subset hr)))
  obtain ⟨t, ht, hgt⟩ := intermediate_value_Icc hlu cont (show 0 ∈ Icc (g l) (g u) from ⟨hl, hu⟩)
  refine ⟨t, ht, Complex.ext hgt (hreal t ht), ?_, ?_⟩
  · intro hz
    have hn := hneg t ht
    rw [hz, Complex.zero_im] at hn
    exact (lt_irrefl 0) hn
  · intro s hs hz
    apply mono.injOn hs ht
    exact (show g s = 0 by change (F _).re = 0; rw [hz, Complex.zero_re]).trans hgt.symm

/-- Explicit separation of the derivative measured for a finite prefix from
the independent one-sided estimate needed for the remainder. -/
theorem zero_on_line_of_remainder {P R DP DR : ℂ → ℂ} {margin : ℝ}
    (hc : (1/2 : ℝ) ∈ Icc a b)
    (hreal : ∀ t ∈ Icc l u, (P (point (1/2) t) + R (point (1/2) t)).im = 0)
    (hp : ∀ x ∈ Icc a b, ∀ t ∈ Icc l u, HasDerivAt P (DP (point x t)) (point x t))
    (hr : ∀ x ∈ Icc a b, ∀ t ∈ Icc l u, HasDerivAt R (DR (point x t)) (point x t))
    (hpneg : ∀ x ∈ Icc a b, ∀ t ∈ Icc l u, (DP (point x t)).im < -margin)
    (hrbound : ∀ x ∈ Icc a b, ∀ t ∈ Icc l u, (DR (point x t)).im ≤ margin)
    {x t : ℝ} (hx : x ∈ Icc a b) (ht : t ∈ Icc l u)
    (hz : P (point x t) + R (point x t) = 0) : x = 1/2 := by
  apply zero_on_line (F := fun z => P z + R z) (D := fun z => DP z + DR z) hc hreal
    (fun v hv s hs => (hp v hv s hs).add (hr v hv s hs)) _ hx ht hz
  intro v hv s hs
  simpa using add_lt_add_of_lt_of_le (hpneg v hv s hs) (hrbound v hv s hs)

/-- A hypothetical zero forces a positive derivative excess on the same
horizontal segment between that zero and the critical line. -/
theorem off_line_zero_forces_remainder_slope {P R DP DR : ℂ → ℂ} {margin x t : ℝ}
    (hreal : (P (point (1/2) t) + R (point (1/2) t)).im = 0)
    (hp : ∀ v ∈ uIcc x (1/2), HasDerivAt P (DP (point v t)) (point v t))
    (hr : ∀ v ∈ uIcc x (1/2), HasDerivAt R (DR (point v t)) (point v t))
    (hpneg : ∀ v ∈ uIcc x (1/2), (DP (point v t)).im < -margin)
    (hoff : x ≠ 1/2) (hz : P (point x t) + R (point x t) = 0) :
    ∃ v ∈ uIcc x (1/2), margin < (DR (point v t)).im := by
  by_contra h
  apply hoff
  apply zero_on_line_of_remainder (l := t) (u := t) (a := min x (1/2)) (b := max x (1/2))
    (P := P) (R := R) (DP := DP) (DR := DR) (margin := margin) right_mem_uIcc
  · intro s hs
    simpa only [le_antisymm hs.2 hs.1] using hreal
  · intro v hv s hs
    simpa only [le_antisymm hs.2 hs.1] using hp v hv
  · intro v hv s hs
    simpa only [le_antisymm hs.2 hs.1] using hr v hv
  · intro v hv s hs
    simpa only [le_antisymm hs.2 hs.1] using hpneg v hv
  · intro v hv s hs
    rw [le_antisymm hs.2 hs.1]
    exact le_of_not_gt (fun hh => h ⟨v, hv, hh⟩)
  · exact left_mem_uIcc
  · exact ⟨le_rfl, le_rfl⟩
  · exact hz

#print axioms real_on_line_of_reflection
#print axioms zero_on_line
#print axioms unique_simple_on_line
#print axioms zero_on_line_of_remainder
#print axioms off_line_zero_forces_remainder_slope
end GaussianRectangle
