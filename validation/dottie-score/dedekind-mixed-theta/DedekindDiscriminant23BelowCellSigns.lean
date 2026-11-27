import DedekindDiscriminant23ReadingCells
import DedekindDiscriminant23CoefficientData

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

private def valueRow := discriminant23StoredReadingCoefficientBox false

/-! Positive real part in the lower band. Each cell has its own kernel reduction. -/

private theorem cell0 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 0).re.lo := by
  decide +kernel

private theorem cell1 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 1).re.lo := by
  decide +kernel

private theorem cell2 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 2).re.lo := by
  decide +kernel

private theorem cell3 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 3).re.lo := by
  decide +kernel

private theorem cell4 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 4).re.lo := by
  decide +kernel

private theorem cell5 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 5).re.lo := by
  decide +kernel

private theorem cell6 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 6).re.lo := by
  decide +kernel

private theorem cell7 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 7).re.lo := by
  decide +kernel

private theorem cell8 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 8).re.lo := by
  decide +kernel

private theorem cell9 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 9).re.lo := by
  decide +kernel

private theorem cell10 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 10).re.lo := by
  decide +kernel

private theorem cell11 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 11).re.lo := by
  decide +kernel

private theorem cell12 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 12).re.lo := by
  decide +kernel

private theorem cell13 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 13).re.lo := by
  decide +kernel

private theorem cell14 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 14).re.lo := by
  decide +kernel

private theorem cell15 :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow 15).re.lo := by
  decide +kernel

/-- All cells in this band meet the signed polynomial margin. -/
theorem discriminant23_below_cell_signs (j : Fin 16) :
    discriminant23ReadingMargin < (discriminant23BelowBox valueRow j).re.lo := by
  fin_cases j
  · exact cell0
  · exact cell1
  · exact cell2
  · exact cell3
  · exact cell4
  · exact cell5
  · exact cell6
  · exact cell7
  · exact cell8
  · exact cell9
  · exact cell10
  · exact cell11
  · exact cell12
  · exact cell13
  · exact cell14
  · exact cell15

#print axioms discriminant23_below_cell_signs

end

end FieldTarget
