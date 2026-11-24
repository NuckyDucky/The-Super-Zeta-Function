import DottieRightContourShift

/-! The exact lower smoothing difference, with the finite polynomial and
the reflected input in the same normalization as the archived ring. -/

namespace QuarticModel

open Complex Finset
open scoped ComplexConjugate
open private dottieSharpSide from ArchivedDottieTailPartition

noncomputable def dottieFiniteSharpSide (S : Finset ℕ) (w : ℂ) : ℂ :=
  dottieRangePolynomial S w * Gamma w / (archivedDottieCompletionScale : ℂ)

private theorem dottie_finite_sharp_side_eq_sum (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (w : ℂ) :
    dottieFiniteSharpSide S w = ∑ n ∈ S, dottieSharpSide w n := by
  simp only [dottieFiniteSharpSide, dottieRangePolynomial, Finset.sum_mul, Finset.sum_div]
  exact sum_congr rfl (fun n hn => by rw [dottieSharpSide, if_neg (hS n hn)])

theorem dottie_lower_smoothing_eq_two_sides {w : ℂ} (hw₀ : 0 < w.re) (hw₁ : w.re < 1) :
    let S := Ioc dottiePrefixEnd dottieOmittedSharpEnd
    dottieOmittedLowerSmoothingError w =
      (dottieRangeSide S w - dottieFiniteSharpSide S w) +
      conj (dottieRangeSide S (1-conj w) - dottieFiniteSharpSide S (1-conj w)) := by
  dsimp only
  let S := Ioc dottiePrefixEnd dottieOmittedSharpEnd
  have hS : ∀ n ∈ S, n ≠ 0 := fun n hn =>
    (Nat.zero_le dottiePrefixEnd |>.trans_lt (mem_Ioc.mp hn).1).ne'
  have hm : 0 < (1-conj w).re+1 := by simp only [sub_re, one_re, conj_re]; linarith
  have hs :
      (∑ n ∈ S, dottieSmoothTerm w n) =
        dottieRangeSide S w + conj (dottieRangeSide S (1-conj w)) := by
    rw [dottie_range_side_eq_sum S (by linarith : 0 < w.re+1) hS,
      dottie_range_side_eq_sum S hm hS, map_sum, ← Finset.sum_add_distrib]
    rfl
  have hp :
      dottieOmittedSharpBlock w =
        dottieFiniteSharpSide S w + conj (dottieFiniteSharpSide S (1-conj w)) := by
    rw [dottie_finite_sharp_side_eq_sum S hS, dottie_finite_sharp_side_eq_sum S hS,
      map_sum, ← Finset.sum_add_distrib]
    rfl
  change (∑ n ∈ S, dottieSmoothTerm w n) - dottieOmittedSharpBlock w = _
  rw [hs,hp,map_sub]
  ring

#print axioms dottie_lower_smoothing_eq_two_sides

end QuarticModel
