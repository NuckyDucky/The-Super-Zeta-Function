import DedekindDiscriminant23ReadingCells
import DedekindDiscriminant23CoefficientData

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

private def slopeRow := discriminant23StoredReadingCoefficientBox true

/-! Positive imaginary slope in the transition band. Each cell has its own kernel reduction. -/

private theorem cell0 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 0).im.lo := by
  decide +kernel

private theorem cell1 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 1).im.lo := by
  decide +kernel

private theorem cell2 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 2).im.lo := by
  decide +kernel

private theorem cell3 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 3).im.lo := by
  decide +kernel

private theorem cell4 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 4).im.lo := by
  decide +kernel

private theorem cell5 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 5).im.lo := by
  decide +kernel

private theorem cell6 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 6).im.lo := by
  decide +kernel

private theorem cell7 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 7).im.lo := by
  decide +kernel

private theorem cell8 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 8).im.lo := by
  decide +kernel

private theorem cell9 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 9).im.lo := by
  decide +kernel

private theorem cell10 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 10).im.lo := by
  decide +kernel

private theorem cell11 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 11).im.lo := by
  decide +kernel

private theorem cell12 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 12).im.lo := by
  decide +kernel

private theorem cell13 :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow 13).im.lo := by
  decide +kernel

/-- All cells in this band meet the signed polynomial margin. -/
theorem discriminant23_slope_cell_signs (j : Fin 14) :
    discriminant23ReadingMargin < (discriminant23SlopeBox slopeRow j).im.lo := by
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

#print axioms discriminant23_slope_cell_signs

end

end FieldTarget
