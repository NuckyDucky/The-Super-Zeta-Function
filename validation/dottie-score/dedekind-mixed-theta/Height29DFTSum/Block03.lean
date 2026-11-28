import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_15 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 15 128 =
      height29DFTSumWitness 15 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_16 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 16 128 =
      height29DFTSumWitness 16 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_17 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 17 128 =
      height29DFTSumWitness 17 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_18 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 18 128 =
      height29DFTSumWitness 18 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_19 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 19 128 =
      height29DFTSumWitness 19 := by
  decide +kernel

/-- The coefficient block beginning at 15 in the exact Fourier table. -/
theorem height29_dft_sum_block_03 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (15 + k.val) 128 =
      height29DFTSumWitness (15 + k.val) := by
  fin_cases k
  · exact dot_15
  · exact dot_16
  · exact dot_17
  · exact dot_18
  · exact dot_19

#print axioms height29_dft_sum_block_03

end FieldTarget
