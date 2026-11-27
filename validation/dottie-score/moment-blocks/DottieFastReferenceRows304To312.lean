import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row304_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 304 =
    (-213813171221525652167026876011880731158386793565474144970270674675454041440 : ℤ) := by decide +kernel

private theorem row304_block0 : dottiePairRowBlock dottieFastReferenceWeight 304 0 304 =
    (-521999206528586132712925371984615928008263660989512745352970884551588679272 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 304 0 304).symm.trans (by decide +kernel)

private theorem row304 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 304 1 = (-735812377750111784879952247996496659166650454554986890323241559227042720712 : ℤ) := by
  rw [dottiePairedRowSpan_one, row304_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 304 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 304 % 1024 = 304 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row304_block0]
  decide +kernel

private theorem row305_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 305 =
    (414842930652444028759340943916881949960893701847754369311875097803522329656 : ℤ) := by decide +kernel

private theorem row305_block0 : dottiePairRowBlock dottieFastReferenceWeight 305 0 305 =
    (-11068302038900527211226046659975323045877243489630755529906674555122182912448 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 305 0 305).symm.trans (by decide +kernel)

private theorem row305 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 305 1 = (-10653459108248083182466705716058441095916349787783001160594799457318660582792 : ℤ) := by
  rw [dottiePairedRowSpan_one, row305_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 305 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 305 % 1024 = 305 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row305_block0]
  decide +kernel

private theorem row306_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 306 =
    (211777512406150779790950229740627418909631870515447928735047544649085897440 : ℤ) := by decide +kernel

private theorem row306_block0 : dottiePairRowBlock dottieFastReferenceWeight 306 0 306 =
    (-2342037748847551957345542457436167188754232571457940688190097256601997598368 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 306 0 306).symm.trans (by decide +kernel)

private theorem row306 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 306 1 = (-2130260236441401177554592227695539769844600700942492759455049711952911700928 : ℤ) := by
  rw [dottiePairedRowSpan_one, row306_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 306 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 306 % 1024 = 306 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row306_block0]
  decide +kernel

private theorem row307_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 307 =
    (-391098567860940918357803749130527747934967702329552194725056043598854970240 : ℤ) := by decide +kernel

private theorem row307_block0 : dottiePairRowBlock dottieFastReferenceWeight 307 0 307 =
    (-8827844750357912200061408231293572110118759097941209871948312278680620621432 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 307 0 307).symm.trans (by decide +kernel)

private theorem row307 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 307 1 = (-9218943318218853118419211980424099858053726800270762066673368322279475591672 : ℤ) := by
  rw [dottiePairedRowSpan_one, row307_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 307 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 307 % 1024 = 307 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row307_block0]
  decide +kernel

private theorem row308_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 308 =
    (-1682327764150805603186891689722046771380261143478743234747848313773458088 : ℤ) := by decide +kernel

private theorem row308_block0 : dottiePairRowBlock dottieFastReferenceWeight 308 0 308 =
    (-4110592786358599379404533679773739959297941434065519324798732068142162867880 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 308 0 308).symm.trans (by decide +kernel)

private theorem row308 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 308 1 = (-4112275114122750185007720571463462006069321695208998068033479916455936325968 : ℤ) := by
  rw [dottiePairedRowSpan_one, row308_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 308 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 308 % 1024 = 308 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row308_block0]
  decide +kernel

private theorem row309_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 309 =
    (313031820636691526530015366263889406973642384330324957671378299072526181808 : ℤ) := by decide +kernel

private theorem row309_block0 : dottiePairRowBlock dottieFastReferenceWeight 309 0 309 =
    (-7986619673856598138932834253840577092233710758768566925557917354423163244136 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 309 0 309).symm.trans (by decide +kernel)

private theorem row309 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 309 1 = (-7673587853219906612402818887576687685260068374438241967886539055350637062328 : ℤ) := by
  rw [dottiePairedRowSpan_one, row309_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 309 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 309 % 1024 = 309 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row309_block0]
  decide +kernel

private theorem row310_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 310 =
    (-398184190526577071422871640423912351360880514932066061366883987942457538720 : ℤ) := by decide +kernel

private theorem row310_block0 : dottiePairRowBlock dottieFastReferenceWeight 310 0 310 =
    (2267735676966993629077278504476112808104923208811204344427970904203673473136 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 310 0 310).symm.trans (by decide +kernel)

private theorem row310 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 310 1 = (1869551486440416557654406864052200456744042693879138283061086916261215934416 : ℤ) := by
  rw [dottiePairedRowSpan_one, row310_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 310 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 310 % 1024 = 310 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row310_block0]
  decide +kernel

private theorem row311_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 311 =
    (-400422002234399486986916729891027958347156735782171631731597312458101591088 : ℤ) := by decide +kernel

private theorem row311_block0 : dottiePairRowBlock dottieFastReferenceWeight 311 0 311 =
    (-6109046024462000153514194957125292234883135622845747234309104896387275651840 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 311 0 311).symm.trans (by decide +kernel)

private theorem row311 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 311 1 = (-6509468026696399640501111687016320193230292358627918866040702208845377242928 : ℤ) := by
  rw [dottiePairedRowSpan_one, row311_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 311 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 311 % 1024 = 311 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row311_block0]
  decide +kernel

private theorem span304_306 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 304 2 = (-11389271485998194967346657964054937755083000242337988050918041016545703303504 : ℤ) := by
  calc
    _ = (-735812377750111784879952247996496659166650454554986890323241559227042720712 : ℤ) + (-10653459108248083182466705716058441095916349787783001160594799457318660582792 : ℤ) := by
      simpa only [Nat.reduceAdd, row304, row305] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 304 1 1
    _ = _ := by decide +kernel

private theorem span306_308 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 306 2 = (-11349203554660254295973804208119639627898327501213254826128418034232387292600 : ℤ) := by
  calc
    _ = (-2130260236441401177554592227695539769844600700942492759455049711952911700928 : ℤ) + (-9218943318218853118419211980424099858053726800270762066673368322279475591672 : ℤ) := by
      simpa only [Nat.reduceAdd, row306, row307] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 306 1 1
    _ = _ := by decide +kernel

private theorem span304_308 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 304 4 = (-22738475040658449263320462172174577382981327743551242877046459050778090596104 : ℤ) := by
  calc
    _ = (-11389271485998194967346657964054937755083000242337988050918041016545703303504 : ℤ) + (-11349203554660254295973804208119639627898327501213254826128418034232387292600 : ℤ) := by
      simpa only [Nat.reduceAdd, span304_306, span306_308] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 304 2 2
    _ = _ := by decide +kernel

private theorem span308_310 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 308 2 = (-11785862967342656797410539459040149691329390069647240035920018971806573388296 : ℤ) := by
  calc
    _ = (-4112275114122750185007720571463462006069321695208998068033479916455936325968 : ℤ) + (-7673587853219906612402818887576687685260068374438241967886539055350637062328 : ℤ) := by
      simpa only [Nat.reduceAdd, row308, row309] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 308 1 1
    _ = _ := by decide +kernel

private theorem span310_312 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 310 2 = (-4639916540255983082846704822964119736486249664748780582979615292584161308512 : ℤ) := by
  calc
    _ = (1869551486440416557654406864052200456744042693879138283061086916261215934416 : ℤ) + (-6509468026696399640501111687016320193230292358627918866040702208845377242928 : ℤ) := by
      simpa only [Nat.reduceAdd, row310, row311] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 310 1 1
    _ = _ := by decide +kernel

private theorem span308_312 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 308 4 = (-16425779507598639880257244282004269427815639734396020618899634264390734696808 : ℤ) := by
  calc
    _ = (-11785862967342656797410539459040149691329390069647240035920018971806573388296 : ℤ) + (-4639916540255983082846704822964119736486249664748780582979615292584161308512 : ℤ) := by
      simpa only [Nat.reduceAdd, span308_310, span310_312] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 308 2 2
    _ = _ := by decide +kernel

private theorem span304_312 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 304 8 = (-39164254548257089143577706454178846810796967477947263495946093315168825292912 : ℤ) := by
  calc
    _ = (-22738475040658449263320462172174577382981327743551242877046459050778090596104 : ℤ) + (-16425779507598639880257244282004269427815639734396020618899634264390734696808 : ℤ) := by
      simpa only [Nat.reduceAdd, span304_308, span308_312] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 304 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows304To312 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 304 8 = (-39164254548257089143577706454178846810796967477947263495946093315168825292912 : ℤ) :=
  span304_312

#print axioms dottieFastReferenceRows304To312

end QuarticModel
