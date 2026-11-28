import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_75 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 75 128 =
      height29DFTSumWitness 75 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_76 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 76 128 =
      height29DFTSumWitness 76 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_77 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 77 128 =
      height29DFTSumWitness 77 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_78 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 78 128 =
      height29DFTSumWitness 78 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_79 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 79 128 =
      height29DFTSumWitness 79 := by
  decide +kernel

/-- The coefficient block beginning at 75 in the exact Fourier table. -/
theorem height29_dft_sum_block_15 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (75 + k.val) 128 =
      height29DFTSumWitness (75 + k.val) := by
  fin_cases k
  · exact dot_75
  · exact dot_76
  · exact dot_77
  · exact dot_78
  · exact dot_79

#print axioms height29_dft_sum_block_15

end FieldTarget
