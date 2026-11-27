import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Compact folded Mellin integrals and derivative bounds on a vertical strip. -/

namespace FieldTarget

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

/-- The two radial weights of a folded Mellin reading. -/
def foldedMellinWeight (w : ℂ) (x : ℝ) : ℂ :=
  Complex.exp ((w - 1) * (Real.log x : ℂ)) + Complex.exp (-w * (Real.log x : ℂ))

theorem foldedMellinWeight_eq_cpow (w : ℂ) {x : ℝ} (hx : 0 < x) :
    foldedMellinWeight w x = (x : ℂ) ^ (w - 1) + (x : ℂ) ^ (-w) := by
  have h (z : ℂ) : (x : ℂ) ^ z = Complex.exp (z * (Real.log x : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
      ← Complex.ofReal_log hx.le, mul_comm]
  rw [foldedMellinWeight, h, h]

/-- Expanding the critical strip by rho costs only a radial weight. -/
theorem foldedMellinWeight_norm_le {w : ℂ} {ρ x : ℝ} (hx : 1 ≤ x)
    (hlo : -ρ ≤ w.re) (hhi : w.re ≤ 1 + ρ) :
    ‖foldedMellinWeight w x‖ ≤ 2 * x ^ ρ := by
  have hpos := zero_lt_one.trans_le hx
  have h₁ : ‖(x : ℂ) ^ (w - 1)‖ ≤ x ^ ρ := by
    rw [norm_cpow_eq_rpow_re_of_pos hpos, sub_re, one_re]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hhi])
  have h₂ : ‖(x : ℂ) ^ (-w)‖ ≤ x ^ ρ := by
    rw [norm_cpow_eq_rpow_re_of_pos hpos, neg_re]
    exact Real.rpow_le_rpow_of_exponent_le hx (by linarith only [hlo])
  rw [foldedMellinWeight_eq_cpow w hpos]
  exact (norm_add_le _ _).trans (by linarith only [h₁, h₂])

/-- The derivative of the radial weight with respect to the complex input. -/
def foldedMellinWeightDeriv (w : ℂ) (x : ℝ) : ℂ :=
  (Real.log x : ℂ) *
    (Complex.exp ((w - 1) * (Real.log x : ℂ)) - Complex.exp (-w * (Real.log x : ℂ)))

private theorem foldedMellinWeight_hasDerivAt (w : ℂ) (x : ℝ) :
    HasDerivAt (fun z ↦ foldedMellinWeight z x) (foldedMellinWeightDeriv w x) w := by
  let L : ℂ := Real.log x
  have ha : HasDerivAt (fun z : ℂ ↦ (z - 1) * L) L w := by
    simpa only [id, one_mul] using ((hasDerivAt_id w).sub_const (1 : ℂ)).mul_const L
  have hb : HasDerivAt (fun z : ℂ ↦ -z * L) (-L) w := by
    simpa only [Pi.neg_apply, id, neg_one_mul] using (hasDerivAt_id w).neg.mul_const L
  convert ((Complex.hasDerivAt_exp _).comp w ha).add
    ((Complex.hasDerivAt_exp _).comp w hb) using 1
  · rfl
  · dsimp only [L, foldedMellinWeightDeriv]
    ring

/-- A finite radial integral, with any integrable kernel on the cutoff interval. -/
def foldedMellinTruncation (f : ℝ → ℂ) (R : ℝ) (w : ℂ) : ℂ :=
  ∫ x in (1 : ℝ)..R, foldedMellinWeight w x * f x

theorem foldedMellinTruncation_hasDerivAt {f : ℝ → ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hf : IntervalIntegrable f volume 1 R) (w : ℂ) :
    HasDerivAt (foldedMellinTruncation f R)
      (∫ x in (1 : ℝ)..R, foldedMellinWeightDeriv w x * f x) w := by
  let J : Set ℝ := [[(1 : ℝ), R]]
  have hJ (x : ℝ) (hx : x ∈ J) : 0 < x := by
    have ht : x ∈ Icc (1 : ℝ) R := by simpa only [J, uIcc_of_le hR] using hx
    exact zero_lt_one.trans_le ht.1
  have hlog : ContinuousOn (fun x : ℝ ↦ (Real.log x : ℂ)) J :=
    Complex.continuous_ofReal.comp_continuousOn fun x hx ↦
      (Real.continuousAt_log (hJ x hx).ne').continuousWithinAt
  have hWeight (z : ℂ) : ContinuousOn (foldedMellinWeight z) J := by
    unfold foldedMellinWeight
    fun_prop
  let S : Set (ℂ × ℝ) := Metric.closedBall w 1 ×ˢ J
  have hS : IsCompact S := (isCompact_closedBall _ _).prod isCompact_uIcc
  have hLogS : ContinuousOn (fun p : ℂ × ℝ ↦ (Real.log p.2 : ℂ)) S :=
    hlog.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2)
  have hSlope : ContinuousOn (fun p : ℂ × ℝ ↦ foldedMellinWeightDeriv p.1 p.2) S := by
    unfold foldedMellinWeightDeriv
    fun_prop
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hSlope
  have hSlopeW : ContinuousOn (foldedMellinWeightDeriv w) J :=
    hSlope.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun x hx ↦ ⟨Metric.mem_closedBall_self (by norm_num), hx⟩)
  have hInt (z : ℂ) : IntervalIntegrable (fun x ↦ foldedMellinWeight z x * f x) volume 1 R :=
    hf.continuousOn_mul (hWeight z)
  have hDerivInt : IntervalIntegrable (fun x ↦ foldedMellinWeightDeriv w x * f x) volume 1 R :=
    hf.continuousOn_mul hSlopeW
  have hbound (x : ℝ) (hx : x ∈ Ι (1 : ℝ) R)
      (z : ℂ) (hz : z ∈ Metric.ball w 1) :
      ‖foldedMellinWeightDeriv z x * f x‖ ≤ B * ‖f x‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hB (z, x) ⟨Metric.ball_subset_closedBall hz,
      uIoc_subset_uIcc hx⟩) (norm_nonneg _)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x ↦ foldedMellinWeight z x * f x)
    (F' := fun z x ↦ foldedMellinWeightDeriv z x * f x)
    (bound := fun x ↦ B * ‖f x‖)
    (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun z ↦ (hInt z).aestronglyMeasurable_restrict_uIoc)
    (hInt w) hDerivInt.aestronglyMeasurable_restrict_uIoc
    (Filter.Eventually.of_forall hbound) (hf.norm.const_mul B)
    (Filter.Eventually.of_forall fun x _ z _ ↦ (foldedMellinWeight_hasDerivAt z x).mul_const _)).2

theorem foldedMellinTruncation_differentiable {f : ℝ → ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hf : IntervalIntegrable f volume 1 R) :
    Differentiable ℂ (foldedMellinTruncation f R) :=
  fun w ↦ (foldedMellinTruncation_hasDerivAt hR hf w).differentiableAt

/-- One complex error on an expanded strip controls every derivative on the
closed critical strip. -/
theorem iteratedDeriv_error_le_of_strip {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (n : ℕ)
    {ρ E : ℝ} (hρ : 0 < ρ)
    (hError : ∀ z : ℂ, -ρ ≤ z.re → z.re ≤ 1 + ρ → ‖f z - g z‖ ≤ E)
    {w : ℂ} (hlo : 0 ≤ w.re) (hhi : w.re ≤ 1) :
    ‖iteratedDeriv n f w - iteratedDeriv n g w‖ ≤ n.factorial * E / ρ ^ n := by
  rw [← iteratedDeriv_sub hf.contDiff.contDiffAt hg.contDiff.contDiffAt]
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hρ (hf.sub hg).diffContOnCl
  intro z hz
  have hdist := Metric.mem_sphere.mp hz
  rw [dist_eq_norm] at hdist
  have hRe := (Complex.abs_re_le_norm (z - w)).trans_eq hdist
  rw [Complex.sub_re] at hRe
  exact hError z (by linarith only [(abs_le.mp hRe).1, hlo])
    (by linarith only [(abs_le.mp hRe).2, hhi])

#check @foldedMellinTruncation_hasDerivAt
#check @iteratedDeriv_error_le_of_strip
#print axioms foldedMellinWeight_norm_le
#print axioms foldedMellinTruncation_hasDerivAt
#print axioms iteratedDeriv_error_le_of_strip

end
end FieldTarget
