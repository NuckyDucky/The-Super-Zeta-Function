import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_35 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 35 128 =
      height29DFTSumWitness 35 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_36 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 36 128 =
      height29DFTSumWitness 36 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_37 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 37 128 =
      height29DFTSumWitness 37 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_38 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 38 128 =
      height29DFTSumWitness 38 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_39 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 39 128 =
      height29DFTSumWitness 39 := by
  decide +kernel

/-- The coefficient block beginning at 35 in the exact Fourier table. -/
theorem height29_dft_sum_block_07 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (35 + k.val) 128 =
      height29DFTSumWitness (35 + k.val) := by
  fin_cases k
  · exact dot_35
  · exact dot_36
  · exact dot_37
  · exact dot_38
  · exact dot_39

#print axioms height29_dft_sum_block_07

end FieldTarget
