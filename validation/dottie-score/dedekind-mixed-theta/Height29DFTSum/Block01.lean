import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_5 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 5 128 =
      height29DFTSumWitness 5 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_6 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 6 128 =
      height29DFTSumWitness 6 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_7 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 7 128 =
      height29DFTSumWitness 7 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_8 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 8 128 =
      height29DFTSumWitness 8 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_9 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 9 128 =
      height29DFTSumWitness 9 := by
  decide +kernel

/-- The coefficient block beginning at 5 in the exact Fourier table. -/
theorem height29_dft_sum_block_01 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (5 + k.val) 128 =
      height29DFTSumWitness (5 + k.val) := by
  fin_cases k
  · exact dot_5
  · exact dot_6
  · exact dot_7
  · exact dot_8
  · exact dot_9

#print axioms height29_dft_sum_block_01

end FieldTarget
