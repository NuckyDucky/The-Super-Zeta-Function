import DottieFastReferenceRows0To32
import DottieFastReferenceRows32To56
import DottieFastReferenceRows56To80
import DottieFastReferenceRows80To96
import DottieFastReferenceRows96To112
import DottieFastReferenceRows112To128
import DottieFastReferenceRows128To144
import DottieFastReferenceRows144To160
import DottieFastReferenceRows160To176
import DottieFastReferenceRows176To192
import DottieFastReferenceRows192To208

namespace QuarticModel

private theorem span0_56 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 56 = (-96794389932819064005994422987483802425028932064220081650965378659425273095976 : ℤ) := by
  calc
    _ = (-99638693248026367961933168575827431962108495201435230986664470430862149938488 : ℤ) + (2844303315207303955938745588343629537079563137215149335699091771436876842512 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows0To32, dottieFastReferenceRows32To56] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 32 24
    _ = _ := by decide +kernel

private theorem span80_112 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 80 32 = (-161838393236228892371634245584279290667362517357827840156587836126657196460928 : ℤ) := by
  calc
    _ = (-76098514952888493645771045249841768144716247535432759080734491761312645234848 : ℤ) + (-85739878283340398725863200334437522522646269822395081075853344365344551226080 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows80To96, dottieFastReferenceRows96To112] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 80 16 16
    _ = _ := by decide +kernel

private theorem span56_112 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 56 56 = (45373288605760368574141498151260026411130155874821524372694542504670692097888 : ℤ) := by
  calc
    _ = (207211681841989260945775743735539317078492673232649364529282378631327888558816 : ℤ) + (-161838393236228892371634245584279290667362517357827840156587836126657196460928 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows56To80, span80_112] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 56 24 32
    _ = _ := by decide +kernel

private theorem span0_112 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 112 = (-51421101327058695431852924836223776013898776189398557278270836154754580998088 : ℤ) := by
  calc
    _ = (-96794389932819064005994422987483802425028932064220081650965378659425273095976 : ℤ) + (45373288605760368574141498151260026411130155874821524372694542504670692097888 : ℤ) := by
      simpa only [Nat.reduceAdd, span0_56, span56_112] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 56 56
    _ = _ := by decide +kernel

private theorem span128_160 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 128 32 = (19584754969522634686329207702654190047002075894362221002079004574673401824600 : ℤ) := by
  calc
    _ = (-34629686558922523581366229887885480974611977194089878594653365865685407253624 : ℤ) + (54214441528445158267695437590539671021614053088452099596732370440358809078224 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows128To144, dottieFastReferenceRows144To160] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 128 16 16
    _ = _ := by decide +kernel

private theorem span112_160 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 112 48 = (-80225983310152032425617292435273901354851657963757909308391254054975533016728 : ℤ) := by
  calc
    _ = (-99810738279674667111946500137928091401853733858120130310470258629648934841328 : ℤ) + (19584754969522634686329207702654190047002075894362221002079004574673401824600 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows112To128, span128_160] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 112 16 32
    _ = _ := by decide +kernel

private theorem span176_208 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 176 32 = (138165623913036169794391433409295475703385624597376135098007632074941621099808 : ℤ) := by
  calc
    _ = (75578201049228708187373869286369698975942481729413410269286453738964201143696 : ℤ) + (62587422863807461607017564122925776727443142867962724828721178335977419956112 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows176To192, dottieFastReferenceRows192To208] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 176 16 16
    _ = _ := by decide +kernel

private theorem span160_208 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 160 48 = (165335333489103452080968600616403185410660694617460258968902052377884913852720 : ℤ) := by
  calc
    _ = (27169709576067282286577167207107709707275070020084123870894420302943292752912 : ℤ) + (138165623913036169794391433409295475703385624597376135098007632074941621099808 : ℤ) := by
      simpa only [Nat.reduceAdd, dottieFastReferenceRows160To176, span176_208] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 160 16 32
    _ = _ := by decide +kernel

private theorem span112_208 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 112 96 = (85109350178951419655351308181129284055809036653702349660510798322909380835992 : ℤ) := by
  calc
    _ = (-80225983310152032425617292435273901354851657963757909308391254054975533016728 : ℤ) + (165335333489103452080968600616403185410660694617460258968902052377884913852720 : ℤ) := by
      simpa only [Nat.reduceAdd, span112_160, span160_208] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 112 48 48
    _ = _ := by decide +kernel

private theorem span0_208 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 208 = (33688248851892724223498383344905508041910260464303792382239962168154799837904 : ℤ) := by
  calc
    _ = (-51421101327058695431852924836223776013898776189398557278270836154754580998088 : ℤ) + (85109350178951419655351308181129284055809036653702349660510798322909380835992 : ℤ) := by
      simpa only [Nat.reduceAdd, span0_112, span112_208] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 112 96
    _ = _ := by decide +kernel

theorem dottieDirectReferencePrefix208 :
    dottiePairedRowSpan 276824064 dottieDirectReferenceWeight 0 208 = (33688248851892724223498383344905508041910260464303792382239962168154799837904 : ℤ) := by
  simpa only [funext dottie_fast_reference_weight_eq] using span0_208

#print axioms dottieDirectReferencePrefix208

end QuarticModel
