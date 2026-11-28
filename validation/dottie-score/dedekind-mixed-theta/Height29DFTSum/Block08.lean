import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_40 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 40 128 =
      height29DFTSumWitness 40 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_41 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 41 128 =
      height29DFTSumWitness 41 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_42 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 42 128 =
      height29DFTSumWitness 42 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_43 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 43 128 =
      height29DFTSumWitness 43 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_44 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 44 128 =
      height29DFTSumWitness 44 := by
  decide +kernel

/-- The coefficient block beginning at 40 in the exact Fourier table. -/
theorem height29_dft_sum_block_08 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (40 + k.val) 128 =
      height29DFTSumWitness (40 + k.val) := by
  fin_cases k
  · exact dot_40
  · exact dot_41
  · exact dot_42
  · exact dot_43
  · exact dot_44

#print axioms height29_dft_sum_block_08

end FieldTarget
