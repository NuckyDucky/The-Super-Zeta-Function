import DedekindDiscriminant23ReadingCells
import DedekindDiscriminant23CoefficientData
import MellinFixedTaylorTail

/-! Directed integer comparisons for the next half-unit height band. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

noncomputable section

def discriminant23SixBandBox (side : Bool) (j : Fin 16) : ComplexBox :=
  discriminant23ReadingCellBox (discriminant23StoredReadingCoefficientBox false)
    (353 + 2 * (j.val : ℤ)) 1 384 (if side then 0 else -1) (if side then 1 else 0)

def discriminant23SixBandMargin : ℤ := 600 * 10 ^ 18

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

private theorem leftCell0 :
    (discriminant23SixBandBox false 0).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell1 :
    (discriminant23SixBandBox false 1).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell2 :
    (discriminant23SixBandBox false 2).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell3 :
    (discriminant23SixBandBox false 3).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell4 :
    (discriminant23SixBandBox false 4).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell5 :
    (discriminant23SixBandBox false 5).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell6 :
    (discriminant23SixBandBox false 6).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell7 :
    (discriminant23SixBandBox false 7).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell8 :
    (discriminant23SixBandBox false 8).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell9 :
    (discriminant23SixBandBox false 9).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell10 :
    (discriminant23SixBandBox false 10).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell11 :
    (discriminant23SixBandBox false 11).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell12 :
    (discriminant23SixBandBox false 12).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell13 :
    (discriminant23SixBandBox false 13).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell14 :
    (discriminant23SixBandBox false 14).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem leftCell15 :
    (discriminant23SixBandBox false 15).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell0 :
    (discriminant23SixBandBox true 0).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell1 :
    (discriminant23SixBandBox true 1).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell2 :
    (discriminant23SixBandBox true 2).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell3 :
    (discriminant23SixBandBox true 3).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell4 :
    (discriminant23SixBandBox true 4).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell5 :
    (discriminant23SixBandBox true 5).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell6 :
    (discriminant23SixBandBox true 6).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell7 :
    (discriminant23SixBandBox true 7).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell8 :
    (discriminant23SixBandBox true 8).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell9 :
    (discriminant23SixBandBox true 9).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell10 :
    (discriminant23SixBandBox true 10).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell11 :
    (discriminant23SixBandBox true 11).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell12 :
    (discriminant23SixBandBox true 12).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell13 :
    (discriminant23SixBandBox true 13).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell14 :
    (discriminant23SixBandBox true 14).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

private theorem rightCell15 :
    (discriminant23SixBandBox true 15).re.hi < -discriminant23SixBandMargin := by
  decide +kernel

theorem discriminant23_six_band_cell_signs (side : Bool) (j : Fin 16) :
    (discriminant23SixBandBox side j).re.hi < -discriminant23SixBandMargin := by
  cases side <;> fin_cases j
  · exact leftCell0
  · exact leftCell1
  · exact leftCell2
  · exact leftCell3
  · exact leftCell4
  · exact leftCell5
  · exact leftCell6
  · exact leftCell7
  · exact leftCell8
  · exact leftCell9
  · exact leftCell10
  · exact leftCell11
  · exact leftCell12
  · exact leftCell13
  · exact leftCell14
  · exact leftCell15
  · exact rightCell0
  · exact rightCell1
  · exact rightCell2
  · exact rightCell3
  · exact rightCell4
  · exact rightCell5
  · exact rightCell6
  · exact rightCell7
  · exact rightCell8
  · exact rightCell9
  · exact rightCell10
  · exact rightCell11
  · exact rightCell12
  · exact rightCell13
  · exact rightCell14
  · exact rightCell15

theorem discriminant23_value_weighted_tail_at_101_over_100 :
    ComplexBox.weightedTailMass
      (fun k ↦ ComplexBox.real (discriminant23StoredReadingCoefficientBox false k))
      101 100 discriminant23ReadingTerms 72 ≤ (55 : ℤ) * 10 ^ 18 * (100 : ℤ) ^ 72 := by
  decide +kernel

#print axioms discriminant23_six_band_cell_signs
#print axioms discriminant23_value_weighted_tail_at_101_over_100

end

end FieldTarget
