import DottieFixedArcKernel0
import DottieFixedArcKernel1
import DottieFixedArcKernel2
import DottieFixedArcKernel3
import DottieFixedArcKernel4
import DottieFixedArcKernel5
import DottieFixedArcKernel6
import DottieFixedArcKernel7
import DottieFixedArcKernel8
import DottieFixedArcKernel9
import DottieFixedArcKernel10
import DottieFixedArcKernel11
import DottieFixedArcKernel12
import DottieFixedArcKernel13
import DottieFixedArcKernel14
import DottieFixedArcKernel15
import DottieFixedArcKernel16
import DottieFixedArcKernel17
import DottieFixedArcKernel18
import DottieFixedArcKernel19
import DottieFixedArcKernel20
import DottieFixedArcKernel21
import DottieFixedArcKernel22
import DottieFixedArcKernel23
import DottieFixedArcKernel24
import DottieFixedArcKernel25
import DottieFixedArcKernel26
import DottieFixedArcKernel27
import DottieFixedArcKernel28
import DottieFixedArcKernel29
import DottieFixedArcKernel30
import DottieFixedArcKernel31
import DottieFixedArcKernel32
import DottieFixedArcKernel33
namespace QuarticModel.DottieFixedIntervals
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
theorem fixedReferenceTicks_eq : fixedReferenceUpper fixedReferenceInput = fixedReferenceTicks := by decide +kernel
theorem fixedCheckedArcs_cover : dottieSharpFactoredArcCover fixedCheckedArcs = true := by decide +kernel
theorem fixedCheckedArcs_scalar : fixedCheckedArcs.all dottieSharpFactoredArcPass = true := by decide +kernel
theorem fixedCheckedArcs_count : fixedCheckedArcs.length = 398 := by decide +kernel
private theorem append_pass {α : Type} (f : α → Bool) (xs ys : List α)
    (hx : xs.all f = true) (hy : ys.all f = true) : (xs ++ ys).all f = true := by
  rw [List.all_append, hx, hy]
  rfl
theorem fixedCheckedArcs_pass :
    fixedCheckedArcs.all (fixedArcPass fixedSharpInput (fixedReferenceUpper fixedReferenceInput)) = true := by
  let f := fixedArcPass fixedSharpInput fixedReferenceTicks
  have h0 : fixedArcGroup0.all f = true :=
    (append_pass f fixedArcBlock0 _ fixedArcBlock0_kernel (append_pass f fixedArcBlock1 _ fixedArcBlock1_kernel (append_pass f fixedArcBlock2 _ fixedArcBlock2_kernel (append_pass f fixedArcBlock3 _ fixedArcBlock3_kernel (append_pass f fixedArcBlock4 _ fixedArcBlock4_kernel (append_pass f fixedArcBlock5 _ fixedArcBlock5_kernel (append_pass f fixedArcBlock6 _ fixedArcBlock6_kernel (append_pass f fixedArcBlock7 _ fixedArcBlock7_kernel fixedArcBlock8_kernel))))))))
  have h1 : fixedArcGroup1.all f = true :=
    (append_pass f fixedArcBlock9 _ fixedArcBlock9_kernel (append_pass f fixedArcBlock10 _ fixedArcBlock10_kernel (append_pass f fixedArcBlock11 _ fixedArcBlock11_kernel (append_pass f fixedArcBlock12 _ fixedArcBlock12_kernel (append_pass f fixedArcBlock13 _ fixedArcBlock13_kernel (append_pass f fixedArcBlock14 _ fixedArcBlock14_kernel (append_pass f fixedArcBlock15 _ fixedArcBlock15_kernel fixedArcBlock16_kernel)))))))
  have h2 : fixedArcGroup2.all f = true :=
    (append_pass f fixedArcBlock17 _ fixedArcBlock17_kernel (append_pass f fixedArcBlock18 _ fixedArcBlock18_kernel (append_pass f fixedArcBlock19 _ fixedArcBlock19_kernel (append_pass f fixedArcBlock20 _ fixedArcBlock20_kernel (append_pass f fixedArcBlock21 _ fixedArcBlock21_kernel (append_pass f fixedArcBlock22 _ fixedArcBlock22_kernel (append_pass f fixedArcBlock23 _ fixedArcBlock23_kernel fixedArcBlock24_kernel)))))))
  have h3 : fixedArcGroup3.all f = true :=
    (append_pass f fixedArcBlock25 _ fixedArcBlock25_kernel (append_pass f fixedArcBlock26 _ fixedArcBlock26_kernel (append_pass f fixedArcBlock27 _ fixedArcBlock27_kernel (append_pass f fixedArcBlock28 _ fixedArcBlock28_kernel (append_pass f fixedArcBlock29 _ fixedArcBlock29_kernel (append_pass f fixedArcBlock30 _ fixedArcBlock30_kernel (append_pass f fixedArcBlock31 _ fixedArcBlock31_kernel (append_pass f fixedArcBlock32 _ fixedArcBlock32_kernel fixedArcBlock33_kernel))))))))
  have hAll : fixedCheckedArcs.all f = true :=
    append_pass f fixedArcGroup0 _ h0 (append_pass f fixedArcGroup1 _ h1
      (append_pass f fixedArcGroup2 fixedArcGroup3 h2 h3))
  exact (congrArg (fun r => fixedCheckedArcs.all (fixedArcPass fixedSharpInput r) = true)
    fixedReferenceTicks_eq.symm).mp hAll
#print axioms fixedReferenceTicks_eq
#print axioms fixedCheckedArcs_cover
#print axioms fixedCheckedArcs_scalar
#print axioms fixedCheckedArcs_count
#print axioms fixedCheckedArcs_pass
end QuarticModel.DottieFixedIntervals
