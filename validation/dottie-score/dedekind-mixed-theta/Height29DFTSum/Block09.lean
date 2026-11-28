import DedekindDiscriminant23Height29Samples

namespace FieldTarget

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_45 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 45 128 =
      height29DFTSumWitness 45 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_46 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 46 128 =
      height29DFTSumWitness 46 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_47 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 47 128 =
      height29DFTSumWitness 47 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_48 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 48 128 =
      height29DFTSumWitness 48 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem dot_49 :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 49 128 =
      height29DFTSumWitness 49 := by
  decide +kernel

/-- The coefficient block beginning at 45 in the exact Fourier table. -/
theorem height29_dft_sum_block_09 (k : Fin 5) :
    gaussianDFTSum height29SampleNumerator contourRoot128PhaseNumerator 128 (45 + k.val) 128 =
      height29DFTSumWitness (45 + k.val) := by
  fin_cases k
  · exact dot_45
  · exact dot_46
  · exact dot_47
  · exact dot_48
  · exact dot_49

#print axioms height29_dft_sum_block_09

end FieldTarget
