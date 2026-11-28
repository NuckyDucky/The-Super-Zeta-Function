import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_25 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 25 128 =
      height29DFTSumWitness 25 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_26 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 26 128 =
      height29DFTSumWitness 26 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_27 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 27 128 =
      height29DFTSumWitness 27 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_28 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 28 128 =
      height29DFTSumWitness 28 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_29 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 29 128 =
      height29DFTSumWitness 29 := by
  decide +kernel

/-- The coefficient block beginning at 25 in the exact Fourier table. -/
theorem height29_dft_sum_block_05 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (25 + k.val) 128 =
      height29DFTSumWitness (25 + k.val) := by
  fin_cases k
  · exact dot_25
  · exact dot_26
  · exact dot_27
  · exact dot_28
  · exact dot_29

#print axioms height29_dft_sum_block_05

end FieldTarget
