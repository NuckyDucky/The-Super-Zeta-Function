import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_95 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 95 128 =
      height29DFTSumWitness 95 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_96 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 96 128 =
      height29DFTSumWitness 96 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_97 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 97 128 =
      height29DFTSumWitness 97 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_98 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 98 128 =
      height29DFTSumWitness 98 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_99 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 99 128 =
      height29DFTSumWitness 99 := by
  decide +kernel

/-- The coefficient block beginning at 95 in the exact Fourier table. -/
theorem height29_dft_sum_block_19 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (95 + k.val) 128 =
      height29DFTSumWitness (95 + k.val) := by
  fin_cases k
  · exact dot_95
  · exact dot_96
  · exact dot_97
  · exact dot_98
  · exact dot_99

#print axioms height29_dft_sum_block_19

end FieldTarget
