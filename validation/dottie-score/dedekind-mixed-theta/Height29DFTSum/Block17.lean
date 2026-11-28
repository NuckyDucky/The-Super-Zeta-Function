import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_85 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 85 128 =
      height29DFTSumWitness 85 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_86 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 86 128 =
      height29DFTSumWitness 86 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_87 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 87 128 =
      height29DFTSumWitness 87 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_88 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 88 128 =
      height29DFTSumWitness 88 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_89 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 89 128 =
      height29DFTSumWitness 89 := by
  decide +kernel

/-- The coefficient block beginning at 85 in the exact Fourier table. -/
theorem height29_dft_sum_block_17 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (85 + k.val) 128 =
      height29DFTSumWitness (85 + k.val) := by
  fin_cases k
  · exact dot_85
  · exact dot_86
  · exact dot_87
  · exact dot_88
  · exact dot_89

#print axioms height29_dft_sum_block_17

end FieldTarget
