import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_80 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 80 128 =
      height29DFTSumWitness 80 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_81 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 81 128 =
      height29DFTSumWitness 81 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_82 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 82 128 =
      height29DFTSumWitness 82 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_83 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 83 128 =
      height29DFTSumWitness 83 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_84 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 84 128 =
      height29DFTSumWitness 84 := by
  decide +kernel

/-- The coefficient block beginning at 80 in the exact Fourier table. -/
theorem height29_dft_sum_block_16 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (80 + k.val) 128 =
      height29DFTSumWitness (80 + k.val) := by
  fin_cases k
  · exact dot_80
  · exact dot_81
  · exact dot_82
  · exact dot_83
  · exact dot_84

#print axioms height29_dft_sum_block_16

end FieldTarget
