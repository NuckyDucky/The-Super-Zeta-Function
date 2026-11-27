import DottieFastReferencePrefix400
import DottieFastReferenceRows400To408
import DottieFastReferenceRows408To416

namespace QuarticModel

private theorem dottieDirectReferenceSpan400To416 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 400 16 = (1566806622702638160947067196275123709918930003693108020551015938569186134664 : ℤ) := by
  have h : dottiePairedRowSpan 276824064 dottieFastReferenceWeight 400 16 = (1566806622702638160947067196275123709918930003693108020551015938569186134664 : ℤ) := by
    calc
      _ = (12287615789142141834633181368687144074119659079023842261533137260980437773144 : ℤ) + (-10720809166439503673686114172412020364200729075330734240982121322411251638480 : ℤ) := by
        simpa only [Nat.reduceAdd, dottieFastReferenceRows400To408, dottieFastReferenceRows408To416] using
          dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 400 8 8
      _ = _ := by decide +kernel
  simpa only [funext dottie_fast_reference_weight_eq] using h

theorem dottieDirectReferencePrefix416 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 416 = (-110357185257693491814606535805441906780439284772743553789445982487095232708360 : ℤ) := by
  calc
    _ = (-111923991880396129975553603001717030490358214776436661809996998425664418843024 : ℤ) + (1566806622702638160947067196275123709918930003693108020551015938569186134664 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieDirectReferencePrefix400, dottieDirectReferenceSpan400To416] using
        dottiePairedRowSpan_add 276824064 dottieDirectReferenceWeight 0 400 16
    _ = _ := by decide +kernel

#print axioms dottieDirectReferencePrefix416

end QuarticModel
