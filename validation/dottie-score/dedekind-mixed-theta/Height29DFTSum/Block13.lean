import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_65 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 65 128 =
      height29DFTSumWitness 65 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_66 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 66 128 =
      height29DFTSumWitness 66 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_67 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 67 128 =
      height29DFTSumWitness 67 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_68 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 68 128 =
      height29DFTSumWitness 68 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_69 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 69 128 =
      height29DFTSumWitness 69 := by
  decide +kernel

/-- The coefficient block beginning at 65 in the exact Fourier table. -/
theorem height29_dft_sum_block_13 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (65 + k.val) 128 =
      height29DFTSumWitness (65 + k.val) := by
  fin_cases k
  · exact dot_65
  · exact dot_66
  · exact dot_67
  · exact dot_68
  · exact dot_69

#print axioms height29_dft_sum_block_13

end FieldTarget
