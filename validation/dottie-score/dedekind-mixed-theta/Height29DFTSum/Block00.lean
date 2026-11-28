import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_0 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 0 128 =
      height29DFTSumWitness 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_1 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 1 128 =
      height29DFTSumWitness 1 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_2 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 2 128 =
      height29DFTSumWitness 2 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_3 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 3 128 =
      height29DFTSumWitness 3 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_4 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 4 128 =
      height29DFTSumWitness 4 := by
  decide +kernel

/-- The coefficient block beginning at 0 in the exact Fourier table. -/
theorem height29_dft_sum_block_00 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (0 + k.val) 128 =
      height29DFTSumWitness (0 + k.val) := by
  fin_cases k
  · exact dot_0
  · exact dot_1
  · exact dot_2
  · exact dot_3
  · exact dot_4

#print axioms height29_dft_sum_block_00

end FieldTarget
