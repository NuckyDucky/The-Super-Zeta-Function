import DedekindDiscriminant23ReadingCells
import DedekindDiscriminant23CoefficientData

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

private def valueRow := discriminant23StoredReadingCoefficientBox false

/-! Negative real part in both halves of the upper band. Each cell has its own kernel reduction. -/

private theorem leftCell0 :
    (discriminant23AboveBox valueRow false 0).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem leftCell1 :
    (discriminant23AboveBox valueRow false 1).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem leftCell2 :
    (discriminant23AboveBox valueRow false 2).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem leftCell3 :
    (discriminant23AboveBox valueRow false 3).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem leftCell4 :
    (discriminant23AboveBox valueRow false 4).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem leftCell5 :
    (discriminant23AboveBox valueRow false 5).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem leftCell6 :
    (discriminant23AboveBox valueRow false 6).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem leftCell7 :
    (discriminant23AboveBox valueRow false 7).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem rightCell0 :
    (discriminant23AboveBox valueRow true 0).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem rightCell1 :
    (discriminant23AboveBox valueRow true 1).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem rightCell2 :
    (discriminant23AboveBox valueRow true 2).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem rightCell3 :
    (discriminant23AboveBox valueRow true 3).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem rightCell4 :
    (discriminant23AboveBox valueRow true 4).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem rightCell5 :
    (discriminant23AboveBox valueRow true 5).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem rightCell6 :
    (discriminant23AboveBox valueRow true 6).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

private theorem rightCell7 :
    (discriminant23AboveBox valueRow true 7).re.hi < -discriminant23ReadingMargin := by
  decide +kernel

/-- All cells in this band meet the signed polynomial margin. -/
theorem discriminant23_above_cell_signs (side : Bool) (j : Fin 8) :
    (discriminant23AboveBox valueRow side j).re.hi < -discriminant23ReadingMargin := by
  cases side <;> fin_cases j
  · exact leftCell0
  · exact leftCell1
  · exact leftCell2
  · exact leftCell3
  · exact leftCell4
  · exact leftCell5
  · exact leftCell6
  · exact leftCell7
  · exact rightCell0
  · exact rightCell1
  · exact rightCell2
  · exact rightCell3
  · exact rightCell4
  · exact rightCell5
  · exact rightCell6
  · exact rightCell7

#print axioms discriminant23_above_cell_signs

end

end FieldTarget
