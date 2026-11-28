import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_10 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 10 128 =
      height29DFTSumWitness 10 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_11 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 11 128 =
      height29DFTSumWitness 11 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_12 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 12 128 =
      height29DFTSumWitness 12 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_13 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 13 128 =
      height29DFTSumWitness 13 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_14 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 14 128 =
      height29DFTSumWitness 14 := by
  decide +kernel

/-- The coefficient block beginning at 10 in the exact Fourier table. -/
theorem height29_dft_sum_block_02 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (10 + k.val) 128 =
      height29DFTSumWitness (10 + k.val) := by
  fin_cases k
  · exact dot_10
  · exact dot_11
  · exact dot_12
  · exact dot_13
  · exact dot_14

#print axioms height29_dft_sum_block_02

end FieldTarget
