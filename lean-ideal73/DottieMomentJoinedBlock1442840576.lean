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
    dottiePairRowBlock realWeight 26858 0 128 = -3786644030633588 ∧
    dottiePairRowBlock imagWeight 26858 0 128 = 2658336350141900 := by
  constructor <;> decide +kernel

private theorem part1 :
    dottiePairRowBlock realWeight 26858 128 128 = -7052340753072074 ∧
    dottiePairRowBlock imagWeight 26858 128 128 = 514009669904071 := by
  constructor <;> decide +kernel

private theorem part2 :
    dottiePairRowBlock realWeight 26858 256 128 = -13814702622646622 ∧
    dottiePairRowBlock imagWeight 26858 256 128 = -3543713156019162 := by
  constructor <;> decide +kernel

private theorem part3 :
    dottiePairRowBlock realWeight 26858 384 128 = 9652360234616097 ∧
    dottiePairRowBlock imagWeight 26858 384 128 = 5818677274251463 := by
  constructor <;> decide +kernel

private theorem part4 :
    dottiePairRowBlock realWeight 26858 512 128 = 1633838070580822 ∧
    dottiePairRowBlock imagWeight 26858 512 128 = 10146947145250574 := by
  constructor <;> decide +kernel

private theorem part5 :
    dottiePairRowBlock realWeight 26858 640 128 = 6591994814741089 ∧
    dottiePairRowBlock imagWeight 26858 640 128 = -12412786565422890 := by
  constructor <;> decide +kernel

private theorem part6 :
    dottiePairRowBlock realWeight 26858 768 128 = 13585243681774733 ∧
    dottiePairRowBlock imagWeight 26858 768 128 = -9144024856645026 := by
  constructor <;> decide +kernel

private theorem part7 :
    dottiePairRowBlock realWeight 26858 896 128 = 3825547919396543 ∧
    dottiePairRowBlock imagWeight 26858 896 128 = 2580577728362158 := by
  constructor <;> decide +kernel

theorem momentInteriorBlock_1442840576_zero :
    dottiePairRowBlock (fun n => momentWeightRealTicks n 0) 26858 0 1024 = 10635297314757000 ∧
    dottiePairRowBlock (fun n => momentWeightImagTicks n 0) 26858 0 1024 = -3381976410176912 := by
  constructor
  · refine (joinScore realWeight 26858 0 512 512 (joinScore realWeight 26858 0 256 256 (joinScore realWeight 26858 0 128 128 part0.1 part1.1) (joinScore realWeight 26858 256 128 128 part2.1 part3.1)) (joinScore realWeight 26858 512 256 256 (joinScore realWeight 26858 512 128 128 part4.1 part5.1) (joinScore realWeight 26858 768 128 128 part6.1 part7.1))).trans ?_
    decide +kernel
  · refine (joinScore imagWeight 26858 0 512 512 (joinScore imagWeight 26858 0 256 256 (joinScore imagWeight 26858 0 128 128 part0.2 part1.2) (joinScore imagWeight 26858 256 128 128 part2.2 part3.2)) (joinScore imagWeight 26858 512 256 256 (joinScore imagWeight 26858 512 128 128 part4.2 part5.2) (joinScore imagWeight 26858 768 128 128 part6.2 part7.2))).trans ?_
    decide +kernel

#print axioms momentInteriorBlock_1442840576_zero

end QuarticModel.DottieFixedIntervals
