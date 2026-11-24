import DottieJointOmittedDerivative
import DottieMomentArchiveScores

/-! On a reflected horizontal segment, signed derivative bounds can be
checked in separate cells and added with their exact lengths. The Dottie
specialization uses the original sharp part and the shorter smooth part. -/

namespace QuarticModel

open Complex Finset Set SuperZeta.StirlingCorrection
open scoped ComplexConjugate
set_option autoImplicit false

private theorem horizontal_im_hasDerivAt {f : ℂ → ℂ} {t r : ℝ} {d : ℂ}
    (h : HasDerivAt f d (⟨r,t⟩ : ℂ)) :
    HasDerivAt (fun x : ℝ => (f ⟨x,t⟩).im) d.im r := by
  have he (x : ℝ) : (⟨x,t⟩ : ℂ) = (x:ℂ)+(t:ℂ)*I := by
    apply Complex.ext <;> simp
  rw [he] at h
  have hz : HasDerivAt (fun z : ℂ => f (z+(t:ℂ)*I)) d (r:ℂ) := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      h.comp (r:ℂ) ((hasDerivAt_id (r:ℂ)).add_const ((t:ℂ)*I))
  have hg := Complex.imCLM.hasFDerivAt.comp_hasDerivAt r hz.comp_ofReal
  change HasDerivAt (fun x : ℝ => (f ((x : ℂ)+(t:ℂ)*I)).im) d.im r at hg
  have hf : (fun x : ℝ => (f ((x : ℂ)+(t:ℂ)*I)).im) =
      fun x : ℝ => (f ⟨x,t⟩).im := funext (fun x => by rw [he x])
  rwa [hf] at hg

/-- An upper bound for the reflected imaginary reading from signed upper
derivative bounds on each cell of the same horizontal segment. -/
theorem reflected_im_le_of_partition_slopes {f d : ℂ → ℂ} (w : ℂ)
    (n : ℕ) (point upper : ℕ → ℝ) (hmono : Monotone point)
    (hstart : point 0 = 1-w.re) (hend : point n = w.re)
    (hderiv : ∀ r ∈ Icc (1-w.re) w.re, HasDerivAt f (d ⟨r,w.im⟩) ⟨r,w.im⟩)
    (hupper : ∀ j < n, ∀ r ∈ Ioo (point j) (point (j+1)), (d ⟨r,w.im⟩).im ≤ upper j) :
    (f w+conj (f (1-conj w))).im ≤ ∑ j ∈ range n, upper j*(point (j+1)-point j) := by
  let g := fun r : ℝ => (f ⟨r,w.im⟩).im
  have hG (r : ℝ) (hr : r ∈ Icc (1-w.re) w.re) : HasDerivAt g (d ⟨r,w.im⟩).im r :=
    horizontal_im_hasDerivAt (hderiv r hr)
  have cell (j : ℕ) (hj : j < n) :
      g (point (j+1))-g (point j) ≤ upper j*(point (j+1)-point j) := by
    have hcell (r : ℝ) (hr : r ∈ Icc (point j) (point (j+1))) : r ∈ Icc (1-w.re) w.re := by
      rw [← hstart, ← hend]
      exact ⟨(hmono (Nat.zero_le j)).trans hr.1, hr.2.trans (hmono (Nat.succ_le_of_lt hj))⟩
    have hc : ContinuousOn g (Icc (point j) (point (j+1))) :=
      fun r hr => (hG r (hcell r hr)).continuousAt.continuousWithinAt
    have hd : DifferentiableOn ℝ g (Ioo (point j) (point (j+1))) :=
      fun r hr => (hG r (hcell r ⟨hr.1.le,hr.2.le⟩)).differentiableAt.differentiableWithinAt
    have hu : ∀ r ∈ Ioo (point j) (point (j+1)), deriv g r ≤ upper j := by
      intro r hr
      rw [(hG r (hcell r ⟨hr.1.le,hr.2.le⟩)).deriv]
      exact hupper j hj r hr
    have hle : point j ≤ point (j+1) := hmono (Nat.le_succ j)
    exact (convex_Icc (point j) (point (j+1))).image_sub_le_mul_sub_of_deriv_le hc
      (by rwa [interior_Icc]) (by rwa [interior_Icc]) _ ⟨le_rfl,hle⟩ _ ⟨hle,le_rfl⟩ hle
  have htel (k : ℕ) : ∑ j ∈ range k, (g (point (j+1))-g (point j)) = g (point k)-g (point 0) := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ,ih]; ring
  have hw : (⟨w.re,w.im⟩ : ℂ) = w := by cases w; rfl
  have hmirror : (⟨1-w.re,w.im⟩ : ℂ) = 1-conj w := by apply Complex.ext <;> simp
  rw [add_im,conj_im,← sub_eq_add_neg,← hw,← hmirror]
  change g w.re-g (1-w.re) ≤ _
  calc
    g w.re-g (1-w.re) = g (point n)-g (point 0) := by rw [hend,hstart]
    _ = ∑ j ∈ range n, (g (point (j+1))-g (point j)) := (htel n).symm
    _ ≤ _ := sum_le_sum (fun j hj => cell j (mem_range.mp hj))

private def shorterMiddleNorms : Finset ℕ :=
  dottieOmittedNorms.filter (fun n => dottieOmittedSharpEnd < n ∧ n ≤ dottieEarlierFarCut)

noncomputable def dottieShorterOmittedSide (w : ℂ) : ℂ :=
  dottieSharpFactor w * dottieNormBlock dottiePrefixEnd (dottieOmittedSharpEnd-dottiePrefixEnd) w +
    dottieRangeSide shorterMiddleNorms w

noncomputable def dottieShorterOmittedDerivative (w : ℂ) : ℂ :=
  let h := dottiePrefixEnd
  let len := dottieOmittedSharpEnd-dottiePrefixEnd
  dottieSharpFactor w *
    (((Real.log archivedThetaScale : ℂ)+digamma w-(Real.log (h:ℝ):ℂ)) *
      dottieNormBlock h len w - dottieCenteredLogBlock h len w) +
    dottieRangeSideDerivative shorterMiddleNorms w

private theorem shorterMiddleNorms_pos (n : ℕ) (hn : n ∈ shorterMiddleNorms) : n ≠ 0 := by
  have h := (Finset.mem_filter.mp hn).2.1
  omega

theorem dottie_shorter_omitted_hasDerivAt {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt dottieShorterOmittedSide (dottieShorterOmittedDerivative w) w :=
  (dottie_completed_norm_block_hasDerivAt dottiePrefixEnd
    (dottieOmittedSharpEnd-dottiePrefixEnd) hw).add
    (dottie_range_side_hasDerivAt _ (by linarith) shorterMiddleNorms_pos)

theorem dottie_shorter_omitted_eq_two_sides {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    dottieOmittedSharpBlock w + dottieShorterMiddleSmooth w =
      dottieShorterOmittedSide w + conj (dottieShorterOmittedSide (1-conj w)) := by
  have hwr : 0 < (1-conj w).re+1 := by
    simp only [sub_re,one_re,conj_re]
    linarith
  have hm : dottieShorterMiddleSmooth w = dottieRangeSide shorterMiddleNorms w +
      conj (dottieRangeSide shorterMiddleNorms (1-conj w)) := by
    rw [dottie_range_side_eq_sum shorterMiddleNorms (by linarith : 0 < w.re+1) shorterMiddleNorms_pos,
      dottie_range_side_eq_sum shorterMiddleNorms hwr shorterMiddleNorms_pos,
      map_sum, ← Finset.sum_add_distrib]
    rfl
  rw [dottie_omitted_sharp_eq_norm_block,hm,dottieShorterOmittedSide,dottieShorterOmittedSide,map_add]
  ring

theorem dottie_shorter_ring_budget_of_partition_slopes {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048))
    (n : ℕ) (point upper : ℕ → ℝ) (hmono : Monotone point)
    (hstart : point 0 = 1-w.re) (hend : point n = w.re)
    (hupper : ∀ j < n, ∀ r ∈ Ioo (point j) (point (j+1)),
      (dottieShorterOmittedDerivative ⟨r,w.im⟩).im ≤ upper j)
    (haverage : (∑ j ∈ range n, upper j*(point (j+1)-point j)) ≤
      188*((w.re-1/2)*dottieCircleReference)) :
    (dottieOmittedSharpBlock w + dottieShorterMiddleSmooth w).im ≤
      188*((w.re-1/2)*dottieCircleReference) := by
  obtain ⟨hr,_⟩ := dottie_right_sphere_coordinate_bounds hw
  have hw₀ : 0 < w.re := by linarith only [hr.1]
  have hw₁ : w.re < 1 := by linarith only [hr.2]
  rw [dottie_shorter_omitted_eq_two_sides hw₀ hw₁]
  refine (reflected_im_le_of_partition_slopes w n point upper hmono hstart hend ?_ hupper).trans haverage
  intro r h
  exact dottie_shorter_omitted_hasDerivAt (show 0 < r by linarith only [h.1,hw₁])

/-- Divide the segment from the mirror to the original input into equal cells. -/
noncomputable def dottieHorizontalGrid (w : ℂ) (n j : ℕ) : ℝ :=
  1-w.re + (j:ℝ)*((w.re-(1-w.re))/(n:ℝ))

/-- On an equal-cell grid, the needed budget is a bound on the mean of the
cell bounds. Each cell retains its sign. -/
theorem dottie_shorter_ring_budget_of_uniform_slopes {w : ℂ}
    (hw : w ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048))
    (n : ℕ) (hn : 0 < n) (upper : ℕ → ℝ)
    (hupper : ∀ j < n, ∀ r ∈ Ioo (dottieHorizontalGrid w n j) (dottieHorizontalGrid w n (j+1)),
      (dottieShorterOmittedDerivative ⟨r,w.im⟩).im ≤ upper j)
    (hmean : (∑ j ∈ range n, upper j) ≤ (n:ℝ)*(94*dottieCircleReference)) :
    (dottieOmittedSharpBlock w + dottieShorterMiddleSmooth w).im ≤
      188*((w.re-1/2)*dottieCircleReference) := by
  have hgap := archivedRightDisk_horizontal_gap (Metric.mem_closedBall.mpr (Metric.mem_sphere.mp hw).le)
  let step := (w.re-(1-w.re))/(n:ℝ)
  have hwidth : 0 ≤ w.re-(1-w.re) := by linarith only [hgap]
  have hn' : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hstep : 0 ≤ step := div_nonneg hwidth (Nat.cast_nonneg n)
  have hmono : Monotone (dottieHorizontalGrid w n) := by
    intro i j hij
    have hcast : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    change 1-w.re+(i:ℝ)*step ≤ 1-w.re+(j:ℝ)*step
    exact add_le_add_right (mul_le_mul_of_nonneg_right hcast hstep) _
  have hstart : dottieHorizontalGrid w n 0 = 1-w.re := by simp [dottieHorizontalGrid]
  have hend : dottieHorizontalGrid w n n = w.re := by
    unfold dottieHorizontalGrid
    field_simp
    ring
  apply dottie_shorter_ring_budget_of_partition_slopes hw n (dottieHorizontalGrid w n)
    upper hmono hstart hend hupper
  calc
    _ = (∑ j ∈ range n, upper j)*step := by
      rw [sum_mul]
      apply sum_congr rfl
      intro j _
      congr 1
      simp only [dottieHorizontalGrid, Nat.cast_add, Nat.cast_one, step]
      ring
    _ ≤ (n:ℝ)*(94*dottieCircleReference)*step := mul_le_mul_of_nonneg_right hmean hstep
    _ = _ := by
      dsimp [step]
      field_simp
      ring

/-- Combine the archive score checks and the signed cell bounds at the
same recovered Dottie input. -/
theorem dottie_right_field_nonzero_of_uniform_slopes
    (hscore : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 16638 = dottiePairedCandidateTicks)
    (h₄ : DottieBandIntegerSums 1854467118035498894 1854467118035634061 438 12)
    (h₂ : DottieBandIntegerSums 3708934236071001884 3708934236071268123 998 482)
    (h₁ : DottieBandIntegerSums 7417868472142007863 7417868472142536246 1550 1338)
    (hsharp : ∀ k < 11, (DottieFixedIntervals.archivedScoredMomentBox dottiePrefixEnd k).fits
      (DottieFixedIntervals.fixedSharpInput k) = true)
    (href : ∀ k < 6, (DottieFixedIntervals.archivedScoredMomentBox 276824064 k).fits
      (DottieFixedIntervals.fixedReferenceInput k) = true)
    (n : ℕ) (hn : 0 < n) (upper : ℂ → ℕ → ℝ)
    (hslope : ∀ z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      ∀ j < n, ∀ r ∈ Ioo (dottieHorizontalGrid z n j) (dottieHorizontalGrid z n (j+1)),
      (dottieShorterOmittedDerivative ⟨r,z.im⟩).im ≤ upper z j)
    (hmean : ∀ z ∈ Metric.sphere (archivedRightCenter dottieHeight) (31/2048),
      (∑ j ∈ range n, upper z j) ≤ (n:ℝ)*(94*dottieCircleReference))
    {w : ℂ} (hw : w ∈ archivedDottieRightRing) (ink : ℂ → ℂ)
    (hR : riemannZeta w ≠ 0) (hB : FieldCoefficientTransfer.chi4.LFunction w ≠ 0) :
    archivedQuarticZeta w ≠ 0 := by
  apply DottieFixedIntervals.dottie_right_field_nonzero_of_archive_score_checks
    hscore h₄ h₂ h₁ hsharp href ?_ hw ink hR hB
  intro z hz
  exact dottie_shorter_ring_budget_of_uniform_slopes hz n hn (upper z) (hslope z hz) (hmean z hz)

#print axioms reflected_im_le_of_partition_slopes
#print axioms dottie_shorter_omitted_hasDerivAt
#print axioms dottie_shorter_omitted_eq_two_sides
#print axioms dottie_shorter_ring_budget_of_partition_slopes
#print axioms dottie_shorter_ring_budget_of_uniform_slopes
#print axioms dottie_right_field_nonzero_of_uniform_slopes

end QuarticModel
