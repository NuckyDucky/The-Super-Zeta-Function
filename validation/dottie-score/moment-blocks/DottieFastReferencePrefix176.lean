import DottieFastReferenceRows0To32
import DottieFastReferenceRows32To56
import DottieFastReferenceRows56To80
import DottieFastReferenceRows80To96
import DottieFastReferenceRows96To112
import DottieFastReferenceRows112To128
import DottieFastReferenceRows128To144
import DottieFastReferenceRows144To160
import DottieFastReferenceRows160To176

namespace QuarticModel

private theorem span0_56 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 56 = (-96794389932819064005994422987483802425028932064220081650965378659425273095976 : ℤ) := by
  calc
    _ = (-99638693248026367961933168575827431962108495201435230986664470430862149938488 : ℤ) + (2844303315207303955938745588343629537079563137215149335699091771436876842512 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows0To32, dottieFastReferenceRows32To56] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 32 24
    _ = _ := by decide +kernel

private theorem span56_96 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 56 40 = (131113166889100767300004698485697548933776425697216605448547886870015243323968 : ℤ) := by
  calc
    _ = (207211681841989260945775743735539317078492673232649364529282378631327888558816 : ℤ) + (-76098514952888493645771045249841768144716247535432759080734491761312645234848 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows56To80, dottieFastReferenceRows80To96] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 56 24 16
    _ = _ := by decide +kernel

private theorem span0_96 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 96 = (34318776956281703294010275498213746508747493632996523797582508210589970227992 : ℤ) := by
  calc
    _ = (-96794389932819064005994422987483802425028932064220081650965378659425273095976 : ℤ) + (131113166889100767300004698485697548933776425697216605448547886870015243323968 : ℤ) := by
      simpa only [Nat.reduceAdd, span0_56, span56_96] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 56 40
    _ = _ := by decide +kernel

private theorem span96_128 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 96 32 = (-185550616563015065837809700472365613924500003680515211386323602994993486067408 : ℤ) := by
  calc
    _ = (-85739878283340398725863200334437522522646269822395081075853344365344551226080 : ℤ) + (-99810738279674667111946500137928091401853733858120130310470258629648934841328 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows96To112, dottieFastReferenceRows112To128] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 96 16 16
    _ = _ := by decide +kernel

private theorem span144_176 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 144 32 = (81384151104512440554272604797647380728889123108536223467626790743302101831136 : ℤ) := by
  calc
    _ = (54214441528445158267695437590539671021614053088452099596732370440358809078224 : ℤ) + (27169709576067282286577167207107709707275070020084123870894420302943292752912 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows144To160, dottieFastReferenceRows160To176] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 144 16 16
    _ = _ := by decide +kernel

private theorem span128_176 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 128 48 = (46754464545589916972906374909761899754277145914446344872973424877616694577512 : ℤ) := by
  calc
    _ = (-34629686558922523581366229887885480974611977194089878594653365865685407253624 : ℤ) + (81384151104512440554272604797647380728889123108536223467626790743302101831136 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows128To144, span144_176] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 128 16 32
    _ = _ := by decide +kernel

private theorem span96_176 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 96 80 = (-138796152017425148864903325562603714170222857766068866513350178117376791489896 : ℤ) := by
  calc
    _ = (-185550616563015065837809700472365613924500003680515211386323602994993486067408 : ℤ) + (46754464545589916972906374909761899754277145914446344872973424877616694577512 : ℤ) := by
      simpa only [Nat.reduceAdd, span96_128, span128_176] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 96 32 48
    _ = _ := by decide +kernel

private theorem span0_176 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 176 = (-104477375061143445570893050064389967661475364133072342715767669906786821261904 : ℤ) := by
  calc
    _ = (34318776956281703294010275498213746508747493632996523797582508210589970227992 : ℤ) + (-138796152017425148864903325562603714170222857766068866513350178117376791489896 : ℤ) := by
      simpa only [Nat.reduceAdd, span0_96, span96_176] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 96 80
    _ = _ := by decide +kernel

theorem dottieDirectReferencePrefix176 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 176 = (-104477375061143445570893050064389967661475364133072342715767669906786821261904 : ℤ) := by
  simpa only [funext dottie_fast_reference_weight_eq] using span0_176

#print axioms dottieDirectReferencePrefix176

end QuarticModel
