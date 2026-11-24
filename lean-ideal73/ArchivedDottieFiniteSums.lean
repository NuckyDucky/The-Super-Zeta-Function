import ArchivedDottieSmoothedIdentity

/-! Separate the finite archived norm ranges from the infinite far tail.
The cutoffs and tilt are those of the original Gaussian circle test. -/

open Complex Finset
open scoped BigOperators

namespace QuarticModel

open SuperZeta.StirlingCorrection

/-- The first norm past the four omitted intervals. All subsequent norms
are assigned to the retained sum by the archived partition. -/
def dottieTailStart : ℕ := 179178262476838746198975365

def dottieOmittedNorms : Finset ℕ :=
  Ico 1442840577 1854467118035498894 ∪
  Ico 1854467118035634062 3708934236071001884 ∪
  Ico 3708934236071268124 7417868472142007863 ∪
  Ico 7417868472142536247 dottieTailStart

theorem dottie_omitted_norm_iff (n : ℕ) :
    dottieRetainedNorm n = false ↔ n ∈ dottieOmittedNorms := by
  unfold dottieRetainedNorm
  rw [decide_eq_false_iff_not]
  simp only [dottieOmittedNorms, Finset.mem_union,
    Finset.mem_Ico, dottiePrefixEnd, dottieTailStart]
  omega

theorem dottie_omitted_eq_finite_sum (w : ℂ) :
    dottieOmitted w = ∑ n ∈ dottieOmittedNorms, dottieSmoothTerm w n := by
  classical
  unfold dottieOmitted
  calc
    _ = ∑ n ∈ dottieOmittedNorms, (if dottieRetainedNorm n then 0 else dottieSmoothTerm w n) :=
      tsum_eq_sum (fun n hn => by
        have h : dottieRetainedNorm n = true := by
          cases h : dottieRetainedNorm n
          · exact (hn ((dottie_omitted_norm_iff n).1 h)).elim
          · rfl
        simp [h])
    _ = ∑ n ∈ dottieOmittedNorms, dottieSmoothTerm w n := by
      apply sum_congr rfl
      intro n hn
      simp [(dottie_omitted_norm_iff n).2 hn]

/-- The finite part of the retained calculation, including its prefix and
six archived bands. The remaining retained part starts at `dottieTailStart`. -/
noncomputable def dottieFiniteRetained (w : ℂ) : ℂ :=
  ∑ n ∈ (range dottieTailStart).filter (fun n => dottieRetainedNorm n = true), dottieSmoothTerm w n

noncomputable def dottieFarTail (w : ℂ) : ℂ :=
  ∑' n : ℕ, dottieSmoothTerm w (n+dottieTailStart)

theorem dottie_retained_eq_finite_add_far_tail {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    dottieRetained w = dottieFiniteRetained w + dottieFarTail w := by
  let f := fun n : ℕ => if dottieRetainedNorm n then dottieSmoothTerm w n else 0
  have hf : Summable f := Summable.of_norm_bounded (dottieSmoothTerm_norm_summable hw₀ hw₁) (fun n => by
    by_cases h : dottieRetainedNorm n = true <;> simp [f, h])
  have htail (n : ℕ) : f (n+dottieTailStart) = dottieSmoothTerm w (n+dottieTailStart) := by
    have h : dottieRetainedNorm (n+dottieTailStart) = true := by
      apply decide_eq_true_iff.mpr
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by
        unfold dottieTailStart
        omega)))))))
    simp [f, h]
  change (∑' n, f n) = dottieFiniteRetained w + dottieFarTail w
  rw [← hf.sum_add_tsum_nat_add dottieTailStart, tsum_congr htail]
  simp only [dottieFarTail, dottieFiniteRetained, Finset.sum_filter, f]

theorem dottie_full_sum_finite_partition {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    archivedMellin w/(archivedDottieCompletionScale : ℂ) =
      dottieFiniteRetained w + dottieFarTail w + ∑ n ∈ dottieOmittedNorms, dottieSmoothTerm w n := by
  have h := dottie_normalized_remainder_eq_signed_norm_sum hw₀ hw₁
  rw [dottie_retained_eq_finite_add_far_tail hw₀ hw₁, dottie_omitted_eq_finite_sum] at h
  exact eq_add_of_sub_eq h |>.trans (add_comm _ _)

#print axioms dottie_omitted_norm_iff
#print axioms dottie_omitted_eq_finite_sum
#print axioms dottie_retained_eq_finite_add_far_tail
#print axioms dottie_full_sum_finite_partition

end QuarticModel
