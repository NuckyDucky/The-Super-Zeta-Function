import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_110 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 110 128 =
      height29DFTSumWitness 110 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_111 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 111 128 =
      height29DFTSumWitness 111 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_112 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 112 128 =
      height29DFTSumWitness 112 := by
  decide +kernel

/-- The coefficient block beginning at 110 in the exact Fourier table. -/
theorem height29_dft_sum_block_22 (k : Fin 3) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (110 + k.val) 128 =
      height29DFTSumWitness (110 + k.val) := by
  fin_cases k
  · exact dot_110
  · exact dot_111
  · exact dot_112

#print axioms height29_dft_sum_block_22

end FieldTarget
