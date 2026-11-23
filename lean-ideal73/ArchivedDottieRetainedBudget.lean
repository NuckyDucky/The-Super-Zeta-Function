import ArchivedDottieSmoothedIdentity

/-! Transfer a signed bound for the weight-one prefix on the exact Dottie
outer circle to the retained smoothed sum. The numerical bounds enter as
hypotheses in the same reference units as the archived circle replay. -/

namespace QuarticModel

open Complex Finset SuperZeta.StirlingCorrection
open scoped ComplexConjugate
open private dottieSharpSide from ArchivedDottieTailPartition
open private dottieBoundary_mem_strip from ArchivedDottieSmoothedIdentity

/-- The normalized weight-one prefix through the fixed retained cutoff. -/
noncomputable def dottieSharpPrefix (w : ℂ) : ℂ :=
  ∑ n ∈ range (dottiePrefixEnd+1),
    (dottieSharpSide w n + conj (dottieSharpSide (1-conj w) n))

/-- The same prefix with the exact archived smoothing on both sides. -/
noncomputable def dottieSmoothedPrefix (w : ℂ) : ℂ :=
  ∑ n ∈ range (dottiePrefixEnd+1), dottieSmoothTerm w n

/-- The retained terms beyond the prefix, selected by the original six bands
and far-tail predicate. -/
noncomputable def dottieRetainedBeyondPrefix (w : ℂ) : ℂ :=
  ∑' n : ℕ, if n ≤ dottiePrefixEnd then 0
    else if dottieRetainedNorm n then dottieSmoothTerm w n else 0

theorem dottieRetained_eq_smoothedPrefix_add_beyond {w : ℂ}
    (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    dottieRetained w = dottieSmoothedPrefix w + dottieRetainedBeyondPrefix w := by
  let p (n : ℕ) := if n ≤ dottiePrefixEnd then dottieSmoothTerm w n else 0
  let q (n : ℕ) := if n ≤ dottiePrefixEnd then 0
    else if dottieRetainedNorm n then dottieSmoothTerm w n else 0
  have ha := dottieSmoothTerm_norm_summable hw₀ hw₁
  have hp : Summable p := Summable.of_norm_bounded ha fun n => by
    by_cases hn : n ≤ dottiePrefixEnd <;> simp [p, hn]
  have hq : Summable q := Summable.of_norm_bounded ha fun n => by
    by_cases hn : n ≤ dottiePrefixEnd <;> by_cases hk : dottieRetainedNorm n = true <;>
      simp [q, hn, hk]
  have he (n : ℕ) : (if dottieRetainedNorm n then dottieSmoothTerm w n else 0) = p n + q n := by
    by_cases hn : n ≤ dottiePrefixEnd
    · have hk : dottieRetainedNorm n = true := by simp [dottieRetainedNorm, hn]
      simp [p, q, hn, hk]
    · simp [p, q, hn]
  have hs : (∑' n, p n) = dottieSmoothedPrefix w := by
    rw [tsum_eq_sum (s := range (dottiePrefixEnd+1)) (fun n hn => by
      have hn' : ¬ n ≤ dottiePrefixEnd := by simpa only [mem_range, Nat.lt_succ_iff] using hn
      simp [p, hn'])]
    apply Finset.sum_congr rfl
    intro n hn
    simp [p, Nat.le_of_lt_succ (mem_range.mp hn)]
  calc
    dottieRetained w = (∑' n, (p n + q n)) := tsum_congr he
    _ = (∑' n, p n) + (∑' n, q n) := hp.tsum_add hq
    _ = dottieSmoothedPrefix w + dottieRetainedBeyondPrefix w := by rw [hs]; rfl

/-- If the uniform error is at most `(margin - 190) / 2048` in units of `S`,
then the exact circle has enough horizontal gap to absorb the error. -/
theorem archivedDottie_model_margin_of_uniform_error {sharp model : ℂ → ℂ} {S margin error : ℝ}
    (hS : 0 < S) (hm : 190 ≤ margin) (hbudget : error ≤ (margin-190)/2048)
    (hsharp : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (sharp w).im ≤ -(margin*((w.re-1/2)*S)))
    (herror : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      ‖model w - sharp w‖ ≤ error*S) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (model w).im ≤ -(190*((w.re-1/2)*S)) := by
  intro w hw
  have hx := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  have hrel : error ≤ (margin-190)*(w.re-1/2) := calc
    error ≤ (margin-190)/2048 := hbudget
    _ = (margin-190)*(1/2048) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hm)
  have hscaled := mul_le_mul_of_nonneg_right hrel hS.le
  have him : (model w).im - (sharp w).im ≤ ‖model w - sharp w‖ := by
    simpa only [Complex.sub_im] using
      (le_abs_self ((model w - sharp w).im)).trans (Complex.abs_im_le_norm (model w - sharp w))
  nlinarith only [hsharp w hw, him.trans (herror w hw), hscaled]

/-- A sharp quotient margin of `190.01` and total absolute error at most
`10⁻⁶` times the original reference give the retained model bound. -/
theorem dottieRetained_model_of_sharp_budget (hS : 0 < dottieCircleReference)
    (hsharp : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.01*((w.re-1/2)*dottieCircleReference)))
    (herror : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      ‖dottieRetained w - dottieSharpPrefix w‖ ≤ (1/1000000)*dottieCircleReference) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieRetained w).im ≤ -(190*((w.re-1/2)*dottieCircleReference)) :=
  archivedDottie_model_margin_of_uniform_error hS (by norm_num) (by norm_num) hsharp herror

/-- Separate numerical targets for replacing the prefix smoothing and adding
the six retained bands and the far tail. Their total budget is `10⁻⁶` times
the reference. -/
theorem dottieRetained_model_of_split_budget (hS : 0 < dottieCircleReference)
    (hsharp : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieSharpPrefix w).im ≤ -(190.01*((w.re-1/2)*dottieCircleReference)))
    (hprefix : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      ‖dottieSmoothedPrefix w - dottieSharpPrefix w‖ ≤ (1/100000000)*dottieCircleReference)
    (hbeyond : ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      ‖dottieRetainedBeyondPrefix w‖ ≤ (99/100000000)*dottieCircleReference) :
    ∀ w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (dottieRetained w).im ≤ -(190*((w.re-1/2)*dottieCircleReference)) := by
  apply dottieRetained_model_of_sharp_budget hS hsharp
  intro w hw
  obtain ⟨hw₀, hw₁⟩ := dottieBoundary_mem_strip hw
  rw [dottieRetained_eq_smoothedPrefix_add_beyond hw₀ hw₁]
  rw [show dottieSmoothedPrefix w + dottieRetainedBeyondPrefix w - dottieSharpPrefix w =
      (dottieSmoothedPrefix w - dottieSharpPrefix w) + dottieRetainedBeyondPrefix w by ring]
  exact (norm_add_le _ _).trans ((add_le_add (hprefix w hw) (hbeyond w hw)).trans_eq (by ring))

#print axioms dottieRetained_eq_smoothedPrefix_add_beyond
#print axioms archivedDottie_model_margin_of_uniform_error
#print axioms dottieRetained_model_of_sharp_budget
#print axioms dottieRetained_model_of_split_budget

end QuarticModel
