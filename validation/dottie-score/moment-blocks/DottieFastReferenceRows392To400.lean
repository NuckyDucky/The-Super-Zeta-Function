import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row392_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 392 =
    (307917493294110891046278730312064082510632839742857738293678275156998463312 : ℤ) := by decide +kernel

private theorem row392_block0 : dottiePairRowBlock dottieFastReferenceWeight 392 0 392 =
    (2382382823604666721775673782177168281196530844024367510514662556889076840112 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 392 0 392).symm.trans (by decide +kernel)

private theorem row392 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 392 1 = (2690300316898777612821952512489232363707163683767225248808340832046075303424 : ℤ) := by
  rw [dottiePairedRowSpan_one, row392_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 392 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 392 % 1024 = 392 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row392_block0]
  decide +kernel

private theorem row393_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 393 =
    (-210041342103322490626943160985351927629664607724943558171845536616368746496 : ℤ) := by decide +kernel

private theorem row393_block0 : dottiePairRowBlock dottieFastReferenceWeight 393 0 393 =
    (-4123139226992395659741959695386463905713920670768921398199468437919605010280 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 393 0 393).symm.trans (by decide +kernel)

private theorem row393 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 393 1 = (-4333180569095718150368902856371815833343585278493864956371313974535973756776 : ℤ) := by
  rw [dottiePairedRowSpan_one, row393_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 393 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 393 % 1024 = 393 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row393_block0]
  decide +kernel

private theorem row394_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 394 =
    (-143469042464205659661868669950568631626479704161117339107281691938755776072 : ℤ) := by decide +kernel

private theorem row394_block0 : dottiePairRowBlock dottieFastReferenceWeight 394 0 394 =
    (-767553097293066716758012593961385923824431436826931607780005287827770485848 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 394 0 394).symm.trans (by decide +kernel)

private theorem row394 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 394 1 = (-911022139757272376419881263911954555450911140988048946887286979766526261920 : ℤ) := by
  rw [dottiePairedRowSpan_one, row394_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 394 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 394 % 1024 = 394 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row394_block0]
  decide +kernel

private theorem row395_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 395 =
    (216201593228468134570147138904998687913323048897759341322365942732857985360 : ℤ) := by decide +kernel

private theorem row395_block0 : dottiePairRowBlock dottieFastReferenceWeight 395 0 395 =
    (2975613112874819271138858653530410546198055046502664569798626162967353994920 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 395 0 395).symm.trans (by decide +kernel)

private theorem row395 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 395 1 = (3191814706103287405709005792435409234111378095400423911120992105700211980280 : ℤ) := by
  rw [dottiePairedRowSpan_one, row395_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 395 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 395 % 1024 = 395 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row395_block0]
  decide +kernel

private theorem row396_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 396 =
    (320075781275369610717805187378923420942327208708790330805693358407185364224 : ℤ) := by decide +kernel

private theorem row396_block0 : dottiePairRowBlock dottieFastReferenceWeight 396 0 396 =
    (-1466995288119291977478283217249109778145958993779704868746198881438296331272 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 396 0 396).symm.trans (by decide +kernel)

private theorem row396 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 396 1 = (-1146919506843922366760478029870186357203631785070914537940505523031110967048 : ℤ) := by
  rw [dottiePairedRowSpan_one, row396_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 396 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 396 % 1024 = 396 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row396_block0]
  decide +kernel

private theorem row397_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 397 =
    (-98113300593235495916015386716588817685608255296627813250296493585135228624 : ℤ) := by decide +kernel

private theorem row397_block0 : dottiePairRowBlock dottieFastReferenceWeight 397 0 397 =
    (-6256575821240489327702342164783195011134220679142504965817196675767565570840 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 397 0 397).symm.trans (by decide +kernel)

private theorem row397 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 397 1 = (-6354689121833724823618357551499783828819828934439132779067493169352700799464 : ℤ) := by
  rw [dottiePairedRowSpan_one, row397_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 397 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 397 % 1024 = 397 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row397_block0]
  decide +kernel

private theorem row398_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 398 =
    (310905596471404884277259880029746625635554905168512270909964909732639499536 : ℤ) := by decide +kernel

private theorem row398_block0 : dottiePairRowBlock dottieFastReferenceWeight 398 0 398 =
    (1158163868652238975483587460709232230640795048050004978098566817480707135600 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 398 0 398).symm.trans (by decide +kernel)

private theorem row398 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 398 1 = (1469069465123643859760847340738978856276349953218517249008531727213346635136 : ℤ) := by
  rw [dottiePairedRowSpan_one, row398_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 398 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 398 % 1024 = 398 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row398_block0]
  decide +kernel

private theorem row399_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 399 =
    (-228413682478074516732305623614323738998961859485654341678497851310884683496 : ℤ) := by decide +kernel

private theorem row399_block0 : dottiePairRowBlock dottieFastReferenceWeight 399 0 399 =
    (-11789217754264292821536234219920709035059553493172168031070779346022587848856 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 399 0 399).symm.trans (by decide +kernel)

private theorem row399 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 399 1 = (-12017631436742367338268539843535032774058515352657822372749277197333472532352 : ℤ) := by
  rw [dottiePairedRowSpan_one, row399_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 399 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 399 % 1024 = 399 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row399_block0]
  decide +kernel

private theorem span392_394 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 392 2 = (-1642880252196940537546950343882583469636421594726639707562973142489898453352 : ℤ) := by
  calc
    _ = (2690300316898777612821952512489232363707163683767225248808340832046075303424 : ℤ) + (-4333180569095718150368902856371815833343585278493864956371313974535973756776 : ℤ) := by
      simpa only [Nat.reduceAdd, row392, row393] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 392 1 1
    _ = _ := by decide +kernel

private theorem span394_396 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 394 2 = (2280792566346015029289124528523454678660466954412374964233705125933685718360 : ℤ) := by
  calc
    _ = (-911022139757272376419881263911954555450911140988048946887286979766526261920 : ℤ) + (3191814706103287405709005792435409234111378095400423911120992105700211980280 : ℤ) := by
      simpa only [Nat.reduceAdd, row394, row395] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 394 1 1
    _ = _ := by decide +kernel

private theorem span392_396 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 392 4 = (637912314149074491742174184640871209024045359685735256670731983443787265008 : ℤ) := by
  calc
    _ = (-1642880252196940537546950343882583469636421594726639707562973142489898453352 : ℤ) + (2280792566346015029289124528523454678660466954412374964233705125933685718360 : ℤ) := by
      simpa only [Nat.reduceAdd, span392_394, span394_396] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 392 2 2
    _ = _ := by decide +kernel

private theorem span396_398 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 396 2 = (-7501608628677647190378835581369970186023460719510047317007998692383811766512 : ℤ) := by
  calc
    _ = (-1146919506843922366760478029870186357203631785070914537940505523031110967048 : ℤ) + (-6354689121833724823618357551499783828819828934439132779067493169352700799464 : ℤ) := by
      simpa only [Nat.reduceAdd, row396, row397] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 396 1 1
    _ = _ := by decide +kernel

private theorem span398_400 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 398 2 = (-10548561971618723478507692502796053917782165399439305123740745470120125897216 : ℤ) := by
  calc
    _ = (1469069465123643859760847340738978856276349953218517249008531727213346635136 : ℤ) + (-12017631436742367338268539843535032774058515352657822372749277197333472532352 : ℤ) := by
      simpa only [Nat.reduceAdd, row398, row399] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 398 1 1
    _ = _ := by decide +kernel

private theorem span396_400 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 396 4 = (-18050170600296370668886528084166024103805626118949352440748744162503937663728 : ℤ) := by
  calc
    _ = (-7501608628677647190378835581369970186023460719510047317007998692383811766512 : ℤ) + (-10548561971618723478507692502796053917782165399439305123740745470120125897216 : ℤ) := by
      simpa only [Nat.reduceAdd, span396_398, span398_400] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 396 2 2
    _ = _ := by decide +kernel

private theorem span392_400 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 392 8 = (-17412258286147296177144353899525152894781580759263617184078012179060150398720 : ℤ) := by
  calc
    _ = (637912314149074491742174184640871209024045359685735256670731983443787265008 : ℤ) + (-18050170600296370668886528084166024103805626118949352440748744162503937663728 : ℤ) := by
      simpa only [Nat.reduceAdd, span392_396, span396_400] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 392 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows392To400 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 392 8 = (-17412258286147296177144353899525152894781580759263617184078012179060150398720 : ℤ) :=
  span392_400

#print axioms dottieFastReferenceRows392To400

end QuarticModel
