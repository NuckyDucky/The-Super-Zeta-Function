import DottieFastReferenceRows304To312
import DottieFastReferenceRows312To320

namespace QuarticModel

private theorem span304_320 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 304 16 = (-55895457804941021895095617842523174775829487644877345153037535512400730433792 : ℤ) := by
  calc
    _ = (-39164254548257089143577706454178846810796967477947263495946093315168825292912 : ℤ) + (-16731203256683932751517911388344327965032520166930081657091442197231905140880 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows304To312, dottieFastReferenceRows312To320] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 304 8 8
    _ = _ := by decide +kernel

theorem dottieDirectReferenceSpan304To320 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 304 16 = (-55895457804941021895095617842523174775829487644877345153037535512400730433792 : ℤ) := by
  simpa only [funext dottie_fast_reference_weight_eq] using span304_320

#print axioms dottieDirectReferenceSpan304To320

end QuarticModel
