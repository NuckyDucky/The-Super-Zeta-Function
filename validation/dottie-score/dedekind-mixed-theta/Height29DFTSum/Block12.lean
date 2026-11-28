import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_60 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 60 128 =
      height29DFTSumWitness 60 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_61 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 61 128 =
      height29DFTSumWitness 61 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_62 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 62 128 =
      height29DFTSumWitness 62 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_63 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 63 128 =
      height29DFTSumWitness 63 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_64 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 64 128 =
      height29DFTSumWitness 64 := by
  decide +kernel

/-- The coefficient block beginning at 60 in the exact Fourier table. -/
theorem height29_dft_sum_block_12 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (60 + k.val) 128 =
      height29DFTSumWitness (60 + k.val) := by
  fin_cases k
  · exact dot_60
  · exact dot_61
  · exact dot_62
  · exact dot_63
  · exact dot_64

#print axioms height29_dft_sum_block_12

end FieldTarget
