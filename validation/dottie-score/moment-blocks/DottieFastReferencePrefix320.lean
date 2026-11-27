import DottieFastReferencePrefix288
import DottieFastReferenceRows288To304
import DottieFastReferenceSpan304To320

namespace QuarticModel

theorem dottieDirectReferencePrefix320 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 320 = (67181794722702150158571329193635924464419105250296752182285353959097885094056 : ℤ) := by
  have hleft := dottieFastReferenceRows288To304
  rw [funext dottie_fast_reference_weight_eq] at hleft
  have hnew :
      dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 288 32 =
        (-31026810230893685428625835253260022480198048141853356262289729107491086286912 : ℤ) +
        (-55895457804941021895095617842523174775829487644877345153037535512400730433792 : ℤ) := by
    simpa only [Nat.reduceAdd, hleft, dottieDirectReferenceSpan304To320] using
      dottiePairedRowSpan_add 276824064 dottieDirectReferenceWeight 288 16 16
  calc
    _ = (154104062758536857482292782289419121720446641037027453597612618578989701814760 : ℤ) +
        ((-31026810230893685428625835253260022480198048141853356262289729107491086286912 : ℤ) +
         (-55895457804941021895095617842523174775829487644877345153037535512400730433792 : ℤ)) := by
      simpa only [Nat.reduceAdd, dottieDirectReferencePrefix288, hnew] using
        dottiePairedRowSpan_add 276824064 dottieDirectReferenceWeight 0 288 32
    _ = _ := by decide +kernel

#print axioms dottieDirectReferencePrefix320

end QuarticModel
