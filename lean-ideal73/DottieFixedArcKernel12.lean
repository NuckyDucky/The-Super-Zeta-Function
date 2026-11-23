import DottieFixedArcInputs
namespace QuarticModel.DottieFixedIntervals
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
theorem fixedArcBlock12_kernel :
    fixedArcBlock12.all (fixedArcPass fixedSharpInput fixedReferenceTicks) = true := by decide +kernel
#print axioms fixedArcBlock12_kernel
end QuarticModel.DottieFixedIntervals
