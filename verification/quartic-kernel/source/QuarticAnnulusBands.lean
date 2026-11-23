import QuarticKernelStrict

namespace QuarticKernel

open Lean in
elab "annulusAux(" function:ident ")" : term =>
  pure (mkConst (.str (.str (.num (.str (.str .anonymous "_private") "QuarticKernelAnnulus") 0)
    "QuarticKernel") function.getId.toString))

def annulusRowCount : ℕ → ℕ := annulusAux(kernelSqrt)

private def bandPoints (lo hi a n : ℕ) : List (ℕ × ℕ) :=
  annulusAux(annulusPointsSweep) lo hi n a
    (annulusRowCount (lo-a^2)) (annulusRowCount (hi-a^2))

private theorem bandPoints_eq (lo hi a n : ℕ) :
    bandPoints lo hi a n = (List.range n).flatMap (fun k =>
      let i := a+k
      let y := annulusAux(rowStart) lo i
      (List.range (annulusAux(rowStop) hi i-y)).map (fun j => (i+1,y+j))) := by
  unfold bandPoints
  apply annulusAux(annulusPointsSweep_eq) <;> simp only [annulusRowCount, annulusAux(kernelSqrt_eq), le_refl]

private theorem bandPoints_append (lo hi a m n : ℕ) :
    bandPoints lo hi a (m+n) = bandPoints lo hi a m ++ bandPoints lo hi (a+m) n := by
  simp only [bandPoints_eq, List.range_add, List.flatMap_append, List.flatMap_map,
    Function.comp_apply, Nat.add_assoc]

def bandStats (lo hi a n : ℕ) : AnnulusStats :=
  annulusAux(scanDirect) hi (bandPoints lo hi a n) 0 0 0

theorem bandStats_append (lo hi a m n : ℕ) :
    bandStats lo hi a (m+n) = bandStats lo hi a m + bandStats lo hi (a+m) n := by
  simp only [bandStats, annulusAux(scanDirect_eq), show ((0,0,0) : AnnulusStats) = 0 by rfl,
    zero_add, bandPoints_append, List.map_append, List.sum_append]

theorem annulusStats_band (lo hi : ℕ) :
    annulusStats lo hi = bandStats lo hi 0 (annulusRowCount hi) := by
  rw [← sweepAnnulusStats_eq]
  rfl

theorem checkSpans_of_annulus {i w : ℕ} {s c m n t v : ℤ} {ws : List ℕ}
    (stats : annulusStats i (i+w) = (c,m,n))
    (positive : 1 ≤ s + if w = 1 then c else n)
    (tail : checkSpans (i+w) (s+c) ws = (t,v,true)) :
    checkSpans i s (w::ws) = (t,(w:ℤ)*s+m+v,true) := by
  simp only [checkSpans, stats, tail, Bool.and_true]
  change (_, _, decide (1 ≤ s + if w = 1 then c else n)) = _
  rw [decide_eq_true positive]

#print axioms bandStats_append
#print axioms annulusStats_band
#print axioms checkSpans_of_annulus
end QuarticKernel
