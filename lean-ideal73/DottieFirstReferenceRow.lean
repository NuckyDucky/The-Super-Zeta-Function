import DottieReferenceRowOneBlock0
import DottieReferenceRowOneBlock1
import DottieReferenceRowOneBlock2
import DottieReferenceRowOneBlock3
import DottieReferenceRowOneBlock4
import DottieReferenceRowOneBlock5
import DottieReferenceRowOneBlock6
import DottieReferenceRowOneBlock7
import DottieReferenceRowOneBlock8
import DottieReferenceRowOneBlock9
import DottieReferenceRowOneBlock10
import DottieReferenceRowOneBlock11
import DottieReferenceRowOneBlock12
import DottieReferenceRowOneBlock13
import DottieReferenceRowOneBlock14
import DottieReferenceRowOneBlock15
import DottieReferenceRowOneBlock16

open Finset

namespace QuarticModel

theorem dottieFirstReferenceRow :
    dottieRowChunk dottieWeightTicks 1 0 (dottieReferenceRowSize 1) = (-577613653815523960696086815005161638050104779213201110268069679423323008 : ℤ) := by
  rw [dottieRowChunk_eq_blocks dottieWeightTicks 1 (dottieReferenceRowSize 1) 1024]
  have hdiv : dottieReferenceRowSize 1 / 1024 = 16 := by decide +kernel
  have hmod : dottieReferenceRowSize 1 % 1024 = 255 := by decide +kernel
  rw [hdiv, hmod, show 16*1024 = (16384 : ℕ) by decide +kernel]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.zero_mul,
    dottieRowOneBlock0, dottieRowOneBlock1, dottieRowOneBlock2, dottieRowOneBlock3, dottieRowOneBlock4,
    dottieRowOneBlock5, dottieRowOneBlock6, dottieRowOneBlock7, dottieRowOneBlock8, dottieRowOneBlock9,
    dottieRowOneBlock10, dottieRowOneBlock11, dottieRowOneBlock12, dottieRowOneBlock13, dottieRowOneBlock14,
    dottieRowOneBlock15, dottieRowOneBlock16]
  decide +kernel

#print axioms dottieFirstReferenceRow

end QuarticModel
