import MellinFixedTable
import Init.Data.List.Nat.Range

/-! Independent batches can be joined by their exact panel endpoints. -/

namespace DottieOriented.NativeSpectrum.MellinFixed

def checkTableRange (start count : Nat) : Bool :=
  (List.range' start count).all checkTablePanel

theorem joinTableRanges (start first second : Nat)
    (hl : checkTableRange start first = true)
    (hr : checkTableRange (start+first) second = true) :
    checkTableRange start (first+second) = true := by
  rw [checkTableRange, ← List.range'_append_1, List.all_append, Bool.and_eq_true_iff]
  exact ⟨hl,hr⟩

#print axioms joinTableRanges

end DottieOriented.NativeSpectrum.MellinFixed
