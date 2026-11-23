import QuarticCheckedShellKernel

namespace QuarticKernel

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

theorem actual_bin_count : binCount actualBins = 33554431 := by decide

theorem actual_checked_shells :
    (∀ j : ℕ, 0 < j → j ≤ 33554432 → 1 ≤ prefixSum j) ∧
      BinsCorrect 0 actualBins ∧ prefixSum 33554432 = 17505 :=
  actual_checked_shells_kernel

#print axioms actual_bin_count
#print axioms actual_checked_shells

end QuarticKernel
