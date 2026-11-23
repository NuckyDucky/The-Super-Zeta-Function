import DottieFixedArcInputs
namespace QuarticModel.DottieFixedIntervals
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
theorem fixedArcBlock30_kernel :
    fixedArcBlock30.all (fixedArcPass fixedSharpInput fixedReferenceTicks) = true := by decide +kernel
#print axioms fixedArcBlock30_kernel
end QuarticModel.DottieFixedIntervals
