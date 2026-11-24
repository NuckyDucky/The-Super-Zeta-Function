import DottiePairedRows

namespace QuarticModel

set_option maxHeartbeats 30000000 in
theorem dottieFirstPairedRows :
    dottiePairedRowSpan 276824064 dottieQuickWeightTicks 0 32 = (-1520366087337219369947611529556332136023237808650385154240569320916415792 : ℤ) := by
  decide +kernel

#print axioms dottieFirstPairedRows

end QuarticModel
