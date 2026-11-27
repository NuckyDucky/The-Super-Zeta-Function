import DottieFastReferencePrefix352
import DottieFastReferenceSpan352To384

namespace QuarticModel

theorem dottieDirectReferencePrefix384 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 384 = (-63676290681462079849826486383603829051546900144852122922760707083741202882344 : ℤ) := by
  calc
    _ = (-5469890926530716200864597129627420341251731645711743847751937076137155303288 : ℤ) + (-58206399754931363648961889253976408710295168499140379075008770007604047579056 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieDirectReferencePrefix352, dottieDirectReferenceSpan352To384] using
        dottiePairedRowSpan_add 276824064 dottieDirectReferenceWeight 0 352 32
    _ = _ := by decide +kernel

#print axioms dottieDirectReferencePrefix384

end QuarticModel
