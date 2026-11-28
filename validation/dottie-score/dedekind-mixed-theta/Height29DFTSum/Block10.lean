import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_50 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 50 128 =
      height29DFTSumWitness 50 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_51 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 51 128 =
      height29DFTSumWitness 51 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_52 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 52 128 =
      height29DFTSumWitness 52 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_53 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 53 128 =
      height29DFTSumWitness 53 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_54 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 54 128 =
      height29DFTSumWitness 54 := by
  decide +kernel

/-- The coefficient block beginning at 50 in the exact Fourier table. -/
theorem height29_dft_sum_block_10 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (50 + k.val) 128 =
      height29DFTSumWitness (50 + k.val) := by
  fin_cases k
  · exact dot_50
  · exact dot_51
  · exact dot_52
  · exact dot_53
  · exact dot_54

#print axioms height29_dft_sum_block_10

end FieldTarget
