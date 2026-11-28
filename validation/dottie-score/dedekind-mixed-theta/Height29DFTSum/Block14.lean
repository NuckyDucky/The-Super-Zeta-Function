import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_70 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 70 128 =
      height29DFTSumWitness 70 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_71 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 71 128 =
      height29DFTSumWitness 71 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_72 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 72 128 =
      height29DFTSumWitness 72 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_73 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 73 128 =
      height29DFTSumWitness 73 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_74 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 74 128 =
      height29DFTSumWitness 74 := by
  decide +kernel

/-- The coefficient block beginning at 70 in the exact Fourier table. -/
theorem height29_dft_sum_block_14 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (70 + k.val) 128 =
      height29DFTSumWitness (70 + k.val) := by
  fin_cases k
  · exact dot_70
  · exact dot_71
  · exact dot_72
  · exact dot_73
  · exact dot_74

#print axioms height29_dft_sum_block_14

end FieldTarget
