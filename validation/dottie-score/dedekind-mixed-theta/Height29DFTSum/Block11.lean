import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_55 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 55 128 =
      height29DFTSumWitness 55 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_56 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 56 128 =
      height29DFTSumWitness 56 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_57 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 57 128 =
      height29DFTSumWitness 57 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_58 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 58 128 =
      height29DFTSumWitness 58 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_59 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 59 128 =
      height29DFTSumWitness 59 := by
  decide +kernel

/-- The coefficient block beginning at 55 in the exact Fourier table. -/
theorem height29_dft_sum_block_11 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (55 + k.val) 128 =
      height29DFTSumWitness (55 + k.val) := by
  fin_cases k
  · exact dot_55
  · exact dot_56
  · exact dot_57
  · exact dot_58
  · exact dot_59

#print axioms height29_dft_sum_block_11

end FieldTarget
