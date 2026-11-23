import DottiePairedRows

open Finset

namespace QuarticModel

set_option maxHeartbeats 30000000

private theorem firstTerms : dottiePairRowHead 276824064 dottieQuickWeightTicks 10999 =
    (72711979060153648615389982126456771976846733676325442335859322997552 : ℤ) := by decide +kernel

private theorem block0 : dottiePairRowBlock dottieQuickWeightTicks 10999 0 1024 =
    (-1315725651614355347465823804489022081578602230619563911725231394854320 : ℤ) := by decide +kernel

private theorem block1 : dottiePairRowBlock dottieQuickWeightTicks 10999 1024 1024 =
    (6234776852304458190711588737115723923783465924895645485113216793170904 : ℤ) := by decide +kernel

private theorem block2 : dottiePairRowBlock dottieQuickWeightTicks 10999 2048 1024 =
    (-4941860922039228945781306714310374067244409842942955850393044860540408 : ℤ) := by decide +kernel

private theorem block3 : dottiePairRowBlock dottieQuickWeightTicks 10999 3072 1024 =
    (-683761204520213189592348148773055415857198194138629490876214576312640 : ℤ) := by decide +kernel

private theorem block4 : dottiePairRowBlock dottieQuickWeightTicks 10999 4096 1024 =
    (3752973651530175288222354054607734221936465692216374412185426137907256 : ℤ) := by decide +kernel

private theorem block5 : dottiePairRowBlock dottieQuickWeightTicks 10999 5120 1024 =
    (6627103019506329027399945995559642608899675954744904432342946725974440 : ℤ) := by decide +kernel

private theorem block6 : dottiePairRowBlock dottieQuickWeightTicks 10999 6144 1024 =
    (6828255472748379108302586232038263729588537558851940496212617448583832 : ℤ) := by decide +kernel

private theorem block7 : dottiePairRowBlock dottieQuickWeightTicks 10999 7168 1024 =
    (-1477020150750650219457464690291677094926096592088626016356596747637056 : ℤ) := by decide +kernel

private theorem block8 : dottiePairRowBlock dottieQuickWeightTicks 10999 8192 1024 =
    (676273877907153864960773565072191390448668105631976465574333744410656 : ℤ) := by decide +kernel

private theorem block9 : dottiePairRowBlock dottieQuickWeightTicks 10999 9216 1024 =
    (-385945316473567079762132708800912259441713586969053465629390811926640 : ℤ) := by decide +kernel

private theorem lastTerms : dottiePairRowBlock dottieQuickWeightTicks 10999 10240 759 =
    (-3997468349405973451535953807484875145667417080308203104716764309190032 : ℤ) := by decide +kernel

theorem dottiePairedRow11000 : dottiePairedRowSpan 276824064 dottieQuickWeightTicks 10999 1 = (11390313258252660894617608692370096581918222442950134894067157472583544 : ℤ) := by
  rw [dottiePairedRowSpan_one, firstTerms, dottiePairRowBlock_eq_blocks]
  have hdiv : dottiePairRowSize 276824064 10999 / 1024 = 10 := by decide +kernel
  have hmod : dottiePairRowSize 276824064 10999 % 1024 = 759 := by decide +kernel
  rw [hdiv, hmod]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceMul, Nat.zero_mul,
    block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, lastTerms]
  decide +kernel

#print axioms dottiePairedRow11000

end QuarticModel
