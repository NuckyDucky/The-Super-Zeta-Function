import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_90 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 90 128 =
      height29DFTSumWitness 90 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_91 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 91 128 =
      height29DFTSumWitness 91 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_92 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 92 128 =
      height29DFTSumWitness 92 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_93 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 93 128 =
      height29DFTSumWitness 93 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_94 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 94 128 =
      height29DFTSumWitness 94 := by
  decide +kernel

/-- The coefficient block beginning at 90 in the exact Fourier table. -/
theorem height29_dft_sum_block_18 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (90 + k.val) 128 =
      height29DFTSumWitness (90 + k.val) := by
  fin_cases k
  · exact dot_90
  · exact dot_91
  · exact dot_92
  · exact dot_93
  · exact dot_94

#print axioms height29_dft_sum_block_18

end FieldTarget
