import DottieCachedReferenceCosine
import DottieStructuralPairBlocks

namespace QuarticModel

set_option maxRecDepth 18000
set_option maxHeartbeats 30000000
set_option profiler.threshold 100

set_option profiler true in
theorem reference_block_original_0 :
    dottiePairRowBlockWithSign dottieLookupRowSign dottieFastReferenceWeight 11763 0 128 =
      (298265635049017771890086833825406738163614632986830822845271502626417478784 : ℤ) := by
  decide +kernel

set_option profiler true in
theorem reference_block_cached_0 :
    dottiePairRowBlockWithSign dottieLookupRowSign dottieCachedReferenceWeight 11763 0 128 =
      (298265635049017771890086833825406738163614632986830822845271502626417478784 : ℤ) := by
  decide +kernel

set_option profiler true in
theorem reference_block_cached_1 :
    dottiePairRowBlockWithSign dottieLookupRowSign dottieCachedReferenceWeight 11763 128 128 =
      (-51301641997961729036743448083280029256358071143501420667511586234477378072 : ℤ) := by
  decide +kernel

set_option profiler true in
theorem reference_block_original_1 :
    dottiePairRowBlockWithSign dottieLookupRowSign dottieFastReferenceWeight 11763 128 128 =
      (-51301641997961729036743448083280029256358071143501420667511586234477378072 : ℤ) := by
  decide +kernel

set_option profiler true in
theorem reference_block_original_2 :
    dottiePairRowBlockWithSign dottieLookupRowSign dottieFastReferenceWeight 11763 256 128 =
      (-102066721941807364031852956758151027570398282596529105804992049445550010712 : ℤ) := by
  decide +kernel

set_option profiler true in
theorem reference_block_cached_2 :
    dottiePairRowBlockWithSign dottieLookupRowSign dottieCachedReferenceWeight 11763 256 128 =
      (-102066721941807364031852956758151027570398282596529105804992049445550010712 : ℤ) := by
  decide +kernel

set_option profiler true in
theorem reference_block_cached_3 :
    dottiePairRowBlockWithSign dottieLookupRowSign dottieCachedReferenceWeight 11763 384 128 =
      (140911919336333244138489564150261108157480100125920239465624330416876439288 : ℤ) := by
  decide +kernel

set_option profiler true in
theorem reference_block_original_3 :
    dottiePairRowBlockWithSign dottieLookupRowSign dottieFastReferenceWeight 11763 384 128 =
      (140911919336333244138489564150261108157480100125920239465624330416876439288 : ℤ) := by
  decide +kernel

#print axioms reference_block_original_0
#print axioms reference_block_cached_0

end QuarticModel
