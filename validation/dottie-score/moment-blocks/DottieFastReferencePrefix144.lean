import DottieFastReferenceRows0To32
import DottieFastReferenceRows32To56
import DottieFastReferenceRows56To80
import DottieFastReferenceRows80To96
import DottieFastReferenceRows96To112
import DottieFastReferenceRows112To128
import DottieFastReferenceRows128To144

namespace QuarticModel

private theorem span32_80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 32 48 = (210055985157196564901714489323882946615572236369864513864981470402764765401328 : ℤ) := by
  calc
    _ = (2844303315207303955938745588343629537079563137215149335699091771436876842512 : ℤ) + (207211681841989260945775743735539317078492673232649364529282378631327888558816 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows32To56, dottieFastReferenceRows56To80] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 32 24 24
    _ = _ := by decide +kernel

private theorem span0_80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 80 = (110417291909170196939781320748055514653463741168429282878316999971902615462840 : ℤ) := by
  calc
    _ = (-99638693248026367961933168575827431962108495201435230986664470430862149938488 : ℤ) + (210055985157196564901714489323882946615572236369864513864981470402764765401328 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows0To32, span32_80] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 32 48
    _ = _ := by decide +kernel

private theorem span80_112 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 80 32 = (-161838393236228892371634245584279290667362517357827840156587836126657196460928 : ℤ) := by
  calc
    _ = (-76098514952888493645771045249841768144716247535432759080734491761312645234848 : ℤ) + (-85739878283340398725863200334437522522646269822395081075853344365344551226080 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows80To96, dottieFastReferenceRows96To112] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 80 16 16
    _ = _ := by decide +kernel

private theorem span112_144 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 112 32 = (-134440424838597190693312730025813572376465711052210008905123624495334342094952 : ℤ) := by
  calc
    _ = (-99810738279674667111946500137928091401853733858120130310470258629648934841328 : ℤ) + (-34629686558922523581366229887885480974611977194089878594653365865685407253624 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows112To128, dottieFastReferenceRows128To144] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 112 16 16
    _ = _ := by decide +kernel

private theorem span80_144 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 80 64 = (-296278818074826083064946975610092863043828228410037849061711460621991538555880 : ℤ) := by
  calc
    _ = (-161838393236228892371634245584279290667362517357827840156587836126657196460928 : ℤ) + (-134440424838597190693312730025813572376465711052210008905123624495334342094952 : ℤ) := by
      simpa only [Nat.reduceAdd, span80_112, span112_144] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 80 32 32
    _ = _ := by decide +kernel

private theorem span0_144 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 144 = (-185861526165655886125165654862037348390364487241608566183394460650088923093040 : ℤ) := by
  calc
    _ = (110417291909170196939781320748055514653463741168429282878316999971902615462840 : ℤ) + (-296278818074826083064946975610092863043828228410037849061711460621991538555880 : ℤ) := by
      simpa only [Nat.reduceAdd, span0_80, span80_144] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 80 64
    _ = _ := by decide +kernel

theorem dottieDirectReferencePrefix144 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 144 = (-185861526165655886125165654862037348390364487241608566183394460650088923093040 : ℤ) := by
  simpa only [funext dottie_fast_reference_weight_eq] using span0_144

#print axioms dottieDirectReferencePrefix144

end QuarticModel
