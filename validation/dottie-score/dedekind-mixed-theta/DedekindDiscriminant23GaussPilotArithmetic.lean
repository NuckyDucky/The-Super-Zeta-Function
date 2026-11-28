import DedekindDiscriminant23GaussEndpoint
import Mathlib.Tactic.FinCases

/-! Check the pilot endpoints one panel at a time before adding their bounds. -/
namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

private def boxEnd (positive : Bool) (b : Box) : ℤ :=
  if positive then b.lo else b.hi

private theorem sum_eq_panelEnds (f : ℕ → ℤ) (ends : List ℤ)
    (h : ∀ j : Fin 16, f j.val = ends.getD j.val 0) :
    (∑ j ∈ Finset.range 16, f j) = ∑ j ∈ Finset.range 16, ends.getD j 0 := by
  apply Finset.sum_congr rfl
  intro j hj
  exact h ⟨j, Finset.mem_range.mp hj⟩

private theorem clearsError_of_panelEnds (m : ℤ) (positive : Bool) (ends : List ℤ)
    (hEnds : ∀ j : Fin 16, boxEnd positive (gauss23CriticalPanelBox m 16 j.val) =
      ends.getD j.val 0)
    (hBudget : if positive then 200000 < ∑ j ∈ Finset.range 16, ends.getD j 0
      else (∑ j ∈ Finset.range 16, ends.getD j 0) < -200000) :
    gauss23ClearsError m 16 positive := by
  cases positive
  · simp only [boxEnd, Bool.false_eq_true, ↓reduceIte] at hEnds
    simp only [Bool.false_eq_true, ↓reduceIte] at hBudget
    simp only [gauss23ClearsError, Bool.false_eq_true, ↓reduceIte]
    rw [gauss23_criticalValueBox_eq_sums]
    exact lt_of_eq_of_lt
      (sum_eq_panelEnds (fun j ↦ (gauss23CriticalPanelBox m 16 j).hi) ends hEnds) hBudget
  · simp only [boxEnd, ↓reduceIte] at hEnds
    simp only [↓reduceIte] at hBudget
    simp only [gauss23ClearsError, ↓reduceIte]
    rw [gauss23_criticalValueBox_eq_sums]
    exact lt_of_lt_of_eq hBudget
      (sum_eq_panelEnds (fun j ↦ (gauss23CriticalPanelBox m 16 j).lo) ends hEnds).symm

private def firstLowerEnds : List ℤ :=
  [39404326140345990248851, -88764753767091189618609, 80468041869425083325119, -39947861568158763255846, 7712138577291208202703, 2725508696149028769707, -2014097077977014339631, 454312938058680171053,
    -38149193875735077070, 451039981103066449, 44710541521264452, -811817453404753, 2236686382328, -691249391, -2046, 14]

private def firstUpperEnds : List ℤ :=
  [38310808771255059042474, -86882310999371395121928, 80040504468124603583239, -41214247779202107808877, 9194434228163957810054, 1999963976813630743109, -1861239241041096363000, 453437098282716106872,
    -42242642508837051868, 893631610844032002, 32280259775944047, -746627592707654, 2329951953056, -877575712, 14011, -29]

private def twentyEnds : List ℤ :=
  [-31984446689899574914035, 19343442525298161108408, 24989306303558941319887, -4701168152391327622565, -8893567773771877310669, 89740757087607237669, 1133945808008161352595, 52794569271917485711,
    -29101382300102717486, -998805501350177301, 52345438879395777, 496214753034733, -1189379297711, -985225649, 18042, 19]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_firstLower_clearsError : gauss23ClearsError 164 16 false := by
  refine clearsError_of_panelEnds 164 false firstLowerEnds ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_firstUpper_clearsError : gauss23ClearsError 165 16 true := by
  refine clearsError_of_panelEnds 165 true firstUpperEnds ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_twenty_clearsError : gauss23ClearsError 320 16 false := by
  refine clearsError_of_panelEnds 320 false twentyEnds ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_firstLower_clearsError
#print axioms gauss23_firstUpper_clearsError
#print axioms gauss23_twenty_clearsError

end FieldTarget
