import DottieFastReferenceRows352To360
import DottieFastReferenceRows360To368
import DottieFastReferenceRows368To376
import DottieFastReferenceRows376To384

namespace QuarticModel

private theorem span352_368 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 352 16 = (-33550828414507972371354914398589271042339155825896583987930075524514005739376 : ℤ) := by
  calc
    _ = (-22836787918091921365678916247207565454688164059139724076831570203859009255328 : ℤ) + (-10714040496416051005675998151381705587650991766756859911098505320654996484048 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows352To360, dottieFastReferenceRows360To368] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 352 8 8
    _ = _ := by decide +kernel

private theorem span368_384 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 368 16 = (-24655571340423391277606974855387137667956012673243795087078694483090041839680 : ℤ) := by
  calc
    _ = (-2789795914050247712205910085106128267860859754247116974901460232466408813528 : ℤ) + (-21865775426373143565401064770281009400095152918996678112177234250623633026152 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows368To376, dottieFastReferenceRows376To384] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 368 8 8
    _ = _ := by decide +kernel

private theorem span352_384 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 352 32 = (-58206399754931363648961889253976408710295168499140379075008770007604047579056 : ℤ) := by
  calc
    _ = (-33550828414507972371354914398589271042339155825896583987930075524514005739376 : ℤ) + (-24655571340423391277606974855387137667956012673243795087078694483090041839680 : ℤ) := by
      simpa only [Nat.reduceAdd, span352_368, span368_384] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 352 16 16
    _ = _ := by decide +kernel

theorem dottieDirectReferenceSpan352To384 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 352 32 = (-58206399754931363648961889253976408710295168499140379075008770007604047579056 : ℤ) := by
  simpa only [funext dottie_fast_reference_weight_eq] using span352_384

#print axioms dottieDirectReferenceSpan352To384

end QuarticModel
