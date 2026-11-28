import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_105 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 105 128 =
      height29DFTSumWitness 105 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_106 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 106 128 =
      height29DFTSumWitness 106 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_107 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 107 128 =
      height29DFTSumWitness 107 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_108 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 108 128 =
      height29DFTSumWitness 108 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_109 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 109 128 =
      height29DFTSumWitness 109 := by
  decide +kernel

/-- The coefficient block beginning at 105 in the exact Fourier table. -/
theorem height29_dft_sum_block_21 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (105 + k.val) 128 =
      height29DFTSumWitness (105 + k.val) := by
  fin_cases k
  · exact dot_105
  · exact dot_106
  · exact dot_107
  · exact dot_108
  · exact dot_109

#print axioms height29_dft_sum_block_21

end FieldTarget
