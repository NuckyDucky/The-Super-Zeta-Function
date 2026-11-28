import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_30 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 30 128 =
      height29DFTSumWitness 30 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_31 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 31 128 =
      height29DFTSumWitness 31 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_32 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 32 128 =
      height29DFTSumWitness 32 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_33 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 33 128 =
      height29DFTSumWitness 33 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_34 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 34 128 =
      height29DFTSumWitness 34 := by
  decide +kernel

/-- The coefficient block beginning at 30 in the exact Fourier table. -/
theorem height29_dft_sum_block_06 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (30 + k.val) 128 =
      height29DFTSumWitness (30 + k.val) := by
  fin_cases k
  · exact dot_30
  · exact dot_31
  · exact dot_32
  · exact dot_33
  · exact dot_34

#print axioms height29_dft_sum_block_06

end FieldTarget
