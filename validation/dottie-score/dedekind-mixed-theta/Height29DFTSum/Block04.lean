import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_20 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 20 128 =
      height29DFTSumWitness 20 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_21 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 21 128 =
      height29DFTSumWitness 21 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_22 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 22 128 =
      height29DFTSumWitness 22 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_23 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 23 128 =
      height29DFTSumWitness 23 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_24 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 24 128 =
      height29DFTSumWitness 24 := by
  decide +kernel

/-- The coefficient block beginning at 20 in the exact Fourier table. -/
theorem height29_dft_sum_block_04 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (20 + k.val) 128 =
      height29DFTSumWitness (20 + k.val) := by
  fin_cases k
  · exact dot_20
  · exact dot_21
  · exact dot_22
  · exact dot_23
  · exact dot_24

#print axioms height29_dft_sum_block_04

end FieldTarget
