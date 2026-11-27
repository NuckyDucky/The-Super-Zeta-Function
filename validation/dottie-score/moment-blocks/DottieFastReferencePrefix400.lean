import DottieFastReferencePrefix384
import DottieFastReferenceRows384To392
import DottieFastReferenceRows392To400

namespace QuarticModel

private theorem dottieDirectReferenceSpan384To400 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 384 16 = (-48247701198934050125727116618113201438811314631584538887236291341923215960680 : ℤ) := by
  have h : dottiePairedRowSpan 276824064 dottieFastReferenceWeight 384 16 = (-48247701198934050125727116618113201438811314631584538887236291341923215960680 : ℤ) := by
    calc
      _ = (-30835442912786753948582762718588048544029733872320921703158279162863065561960 : ℤ) + (-17412258286147296177144353899525152894781580759263617184078012179060150398720 : ℤ) := by
        simpa only [Nat.reduceAdd, dottieFastReferenceRows384To392, dottieFastReferenceRows392To400] using
          dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 384 8 8
      _ = _ := by decide +kernel
  simpa only [funext dottie_fast_reference_weight_eq] using h

theorem dottieDirectReferencePrefix400 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 400 = (-111923991880396129975553603001717030490358214776436661809996998425664418843024 : ℤ) := by
  calc
    _ = (-63676290681462079849826486383603829051546900144852122922760707083741202882344 : ℤ) + (-48247701198934050125727116618113201438811314631584538887236291341923215960680 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieDirectReferencePrefix384, dottieDirectReferenceSpan384To400] using
        dottiePairedRowSpan_add 276824064 dottieDirectReferenceWeight 0 384 16
    _ = _ := by decide +kernel

#print axioms dottieDirectReferencePrefix400

end QuarticModel
