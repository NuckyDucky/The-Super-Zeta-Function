import DottieDirectReferenceScore

namespace QuarticModel

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

/-- The complete final row of the reference lattice, including its axis. -/
theorem dottieDirectReference_last_row :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 16637 1 =
      -21976255580371586449635392316596758318086840067326213982989601079864746992 := by
  decide +kernel

/-- The first 128 pairs of the interior row used in the earlier moment replay. -/
theorem dottieDirectReference_interior_block :
    dottiePairRowBlock dottieDirectReferenceWeight 11763 0 128 =
      298265635049017771890086833825406738163614632986830822845271502626417478784 := by
  decide +kernel

#print axioms dottieDirectReference_last_row
#print axioms dottieDirectReference_interior_block

end QuarticModel
