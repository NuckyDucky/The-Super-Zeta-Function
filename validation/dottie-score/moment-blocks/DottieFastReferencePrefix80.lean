import DottieFastReferenceRows0To32
import DottieFastReferenceRows32To56
import DottieFastReferenceRows56To80

namespace QuarticModel

private theorem rows32To80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 32 48 = (210055985157196564901714489323882946615572236369864513864981470402764765401328 : ℤ) := by
  calc
    _ = (2844303315207303955938745588343629537079563137215149335699091771436876842512 : ℤ) + (207211681841989260945775743735539317078492673232649364529282378631327888558816 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows32To56, dottieFastReferenceRows56To80] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 32 24 24
    _ = _ := by decide +kernel

/-- The certified subtotal of the first 80 rows of the original reference score. -/
theorem dottieDirectReferencePrefix80 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 80 = (110417291909170196939781320748055514653463741168429282878316999971902615462840 : ℤ) := by
  rw [← funext dottie_fast_reference_weight_eq]
  calc
    _ = (-99638693248026367961933168575827431962108495201435230986664470430862149938488 : ℤ) + (210055985157196564901714489323882946615572236369864513864981470402764765401328 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows0To32, rows32To80] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 32 48
    _ = _ := by decide +kernel

#print axioms dottieDirectReferencePrefix80

end QuarticModel
