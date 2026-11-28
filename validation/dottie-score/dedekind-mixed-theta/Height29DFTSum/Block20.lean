import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_100 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 100 128 =
      height29DFTSumWitness 100 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_101 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 101 128 =
      height29DFTSumWitness 101 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_102 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 102 128 =
      height29DFTSumWitness 102 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_103 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 103 128 =
      height29DFTSumWitness 103 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_104 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 104 128 =
      height29DFTSumWitness 104 := by
  decide +kernel

/-- The coefficient block beginning at 100 in the exact Fourier table. -/
theorem height29_dft_sum_block_20 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (100 + k.val) 128 =
      height29DFTSumWitness (100 + k.val) := by
  fin_cases k
  · exact dot_100
  · exact dot_101
  · exact dot_102
  · exact dot_103
  · exact dot_104

#print axioms height29_dft_sum_block_20

end FieldTarget
