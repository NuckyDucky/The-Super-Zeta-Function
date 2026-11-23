import DottieNormalizedMomentScore
namespace QuarticModel.DottieFixedIntervals
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000

private def realWeight (n : ℕ) : ℤ := momentWeightRealTicks n 0
private def imagWeight (n : ℕ) : ℤ := momentWeightImagTicks n 0

private theorem joinScore (f : ℕ → ℤ) (a lo m n : ℕ) {x y : ℤ}
    (hm : dottiePairRowBlock f a lo m = x) (hn : dottiePairRowBlock f a (lo+m) n = y) :
    dottiePairRowBlock f a lo (m+n) = x+y := by
  rw [dottiePairRowBlock_add,hm,hn]

private theorem part0 :
    dottiePairRowBlock realWeight 11763 0 128 = -43481151690513308 ∧
    dottiePairRowBlock imagWeight 11763 0 128 = 24374937816273338 := by
  constructor <;> decide +kernel

private theorem part1 :
    dottiePairRowBlock realWeight 11763 128 128 = 17797224436609321 ∧
    dottiePairRowBlock imagWeight 11763 128 128 = 5475261584382894 := by
  constructor <;> decide +kernel

private theorem part2 :
    dottiePairRowBlock realWeight 11763 256 128 = 26331637186511839 ∧
    dottiePairRowBlock imagWeight 11763 256 128 = 2388982974633002 := by
  constructor <;> decide +kernel

private theorem part3 :
    dottiePairRowBlock realWeight 11763 384 128 = -33748888760916685 ∧
    dottiePairRowBlock imagWeight 11763 384 128 = -858170533315048 := by
  constructor <;> decide +kernel

private theorem part4 :
    dottiePairRowBlock realWeight 11763 512 128 = 27376588529373263 ∧
    dottiePairRowBlock imagWeight 11763 512 128 = 13356753326244974 := by
  constructor <;> decide +kernel

private theorem part5 :
    dottiePairRowBlock realWeight 11763 640 128 = -40533074678313878 ∧
    dottiePairRowBlock imagWeight 11763 640 128 = -6850179754989683 := by
  constructor <;> decide +kernel

private theorem part6 :
    dottiePairRowBlock realWeight 11763 768 128 = -9623807619822612 ∧
    dottiePairRowBlock imagWeight 11763 768 128 = 5514323696223614 := by
  constructor <;> decide +kernel

private theorem part7 :
    dottiePairRowBlock realWeight 11763 896 128 = 1527723516986627 ∧
    dottiePairRowBlock imagWeight 11763 896 128 = -3913559598499528 := by
  constructor <;> decide +kernel

theorem momentInteriorBlock_276824064_zero :
    dottiePairRowBlock (fun n => momentWeightRealTicks n 0) 11763 0 1024 = -54353749080085433 ∧
    dottiePairRowBlock (fun n => momentWeightImagTicks n 0) 11763 0 1024 = 39488349510953563 := by
  constructor
  · refine (joinScore realWeight 11763 0 512 512 (joinScore realWeight 11763 0 256 256 (joinScore realWeight 11763 0 128 128 part0.1 part1.1) (joinScore realWeight 11763 256 128 128 part2.1 part3.1)) (joinScore realWeight 11763 512 256 256 (joinScore realWeight 11763 512 128 128 part4.1 part5.1) (joinScore realWeight 11763 768 128 128 part6.1 part7.1))).trans ?_
    decide +kernel
  · refine (joinScore imagWeight 11763 0 512 512 (joinScore imagWeight 11763 0 256 256 (joinScore imagWeight 11763 0 128 128 part0.2 part1.2) (joinScore imagWeight 11763 256 128 128 part2.2 part3.2)) (joinScore imagWeight 11763 512 256 256 (joinScore imagWeight 11763 512 128 128 part4.2 part5.2) (joinScore imagWeight 11763 768 128 128 part6.2 part7.2))).trans ?_
    decide +kernel

#print axioms momentInteriorBlock_276824064_zero

end QuarticModel.DottieFixedIntervals
