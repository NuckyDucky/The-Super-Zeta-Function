import DottieFastReferencePrefix320
import DottieFastReferenceSpan320To352

namespace QuarticModel

theorem dottieDirectReferencePrefix352 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 352 = (-5469890926530716200864597129627420341251731645711743847751937076137155303288 : ℤ) := by
  calc
    _ = (67181794722702150158571329193635924464419105250296752182285353959097885094056 : ℤ) + (-72651685649232866359435926323263344805670836896008496030037291035235040397344 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieDirectReferencePrefix320, dottieDirectReferenceSpan320To352] using
        dottiePairedRowSpan_add 276824064 dottieDirectReferenceWeight 0 320 32
    _ = _ := by decide +kernel

#print axioms dottieDirectReferencePrefix352

end QuarticModel
