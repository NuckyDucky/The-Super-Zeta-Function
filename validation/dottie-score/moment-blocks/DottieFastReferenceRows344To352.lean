import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row344_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 344 =
    (-345527464848134530221989269174377126543340619490807414433958250252059457408 : ℤ) := by decide +kernel

private theorem row344_block0 : dottiePairRowBlock dottieFastReferenceWeight 344 0 344 =
    (2749928436664380179442104097254260469948920154604203043679682340318921795288 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 344 0 344).symm.trans (by decide +kernel)

private theorem row344 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 344 1 = (2404400971816245649220114828079883343405579535113395629245724090066862337880 : ℤ) := by
  rw [dottiePairedRowSpan_one, row344_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 344 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 344 % 1024 = 344 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row344_block0]
  decide +kernel

private theorem row345_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 345 =
    (-355171248148353704813745207854262773602006487632743437187949969988700827648 : ℤ) := by decide +kernel

private theorem row345_block0 : dottiePairRowBlock dottieFastReferenceWeight 345 0 345 =
    (-7480527058824695425702823694944267953525437715424041741816717907726353307200 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 345 0 345).symm.trans (by decide +kernel)

private theorem row345 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 345 1 = (-7835698306973049130516568902798530727127444203056785179004667877715054134848 : ℤ) := by
  rw [dottiePairedRowSpan_one, row345_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 345 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 345 % 1024 = 345 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row345_block0]
  decide +kernel

private theorem row346_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 346 =
    (344629870923749646939903121889084364820064795231233188108826703919168087864 : ℤ) := by decide +kernel

private theorem row346_block0 : dottiePairRowBlock dottieFastReferenceWeight 346 0 346 =
    (7803939860256560491057342141060315329625309608096302128109061578309368031576 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 346 0 346).symm.trans (by decide +kernel)

private theorem row346 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 346 1 = (8148569731180310137997245262949399694445374403327535316217888282228536119440 : ℤ) := by
  rw [dottiePairedRowSpan_one, row346_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 346 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 346 % 1024 = 346 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row346_block0]
  decide +kernel

private theorem row347_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 347 =
    (-364512404033784161657388467379398063456414658079557648669211916359235767680 : ℤ) := by decide +kernel

private theorem row347_block0 : dottiePairRowBlock dottieFastReferenceWeight 347 0 347 =
    (-7048497742487732909557436728734379833756964365713489347711815595853897910200 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 347 0 347).symm.trans (by decide +kernel)

private theorem row347 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 347 1 = (-7413010146521517071214825196113777897213379023793046996381027512213133677880 : ℤ) := by
  rw [dottiePairedRowSpan_one, row347_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 347 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 347 % 1024 = 347 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row347_block0]
  decide +kernel

private theorem row348_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 348 =
    (-330099674588832242955804254616609812896051533470450829652890294859575003208 : ℤ) := by decide +kernel

private theorem row348_block0 : dottiePairRowBlock dottieFastReferenceWeight 348 0 348 =
    (-4402955996436015397082491647189724477071450580924193308099176076949932955448 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 348 0 348).symm.trans (by decide +kernel)

private theorem row348 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 348 1 = (-4733055671024847640038295901806334289967502114394644137752066371809507958656 : ℤ) := by
  rw [dottiePairedRowSpan_one, row348_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 348 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 348 % 1024 = 348 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row348_block0]
  decide +kernel

private theorem row349_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 349 =
    (108382643816377872908339703667080921201992068161473986991883423352324158480 : ℤ) := by decide +kernel

private theorem row349_block0 : dottiePairRowBlock dottieFastReferenceWeight 349 0 349 =
    (-10530008054782824225243511070687516363867050958734151867064485238646567843640 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 349 0 349).symm.trans (by decide +kernel)

private theorem row349 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 349 1 = (-10421625410966446352335171367020435442665058890572677880072601815294243685160 : ℤ) := by
  rw [dottiePairedRowSpan_one, row349_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 349 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 349 % 1024 = 349 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row349_block0]
  decide +kernel

private theorem row350_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 350 =
    (351259536317884580425564274843405084660157222093071462271303270104410931760 : ℤ) := by decide +kernel

private theorem row350_block0 : dottiePairRowBlock dottieFastReferenceWeight 350 0 350 =
    (328550601800843710921730831210895069528522536800701433343820636094478126336 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 350 0 350).symm.trans (by decide +kernel)

private theorem row350 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 350 1 = (679810138118728291347295106054300154188679758893772895615123906198889058096 : ℤ) := by
  rw [dottiePairedRowSpan_one, row350_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 350 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 350 % 1024 = 350 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row350_block0]
  decide +kernel

private theorem row351_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 351 =
    (-258476680038413200043883758993643742910262150536885707170190742851452451624 : ℤ) := by decide +kernel

private theorem row351_block0 : dottiePairRowBlock dottieFastReferenceWeight 351 0 351 =
    (644816246094938627959950180474418467743358153566570079334132022815352767888 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 351 0 351).symm.trans (by decide +kernel)

private theorem row351 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 351 1 = (386339566056525427916066421480774724833096003029684372163941279963900316264 : ℤ) := by
  rw [dottiePairedRowSpan_one, row351_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 351 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 351 % 1024 = 351 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row351_block0]
  decide +kernel

private theorem span344_346 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 344 2 = (-5431297335156803481296454074718647383721864667943389549758943787648191796968 : ℤ) := by
  calc
    _ = (2404400971816245649220114828079883343405579535113395629245724090066862337880 : ℤ) + (-7835698306973049130516568902798530727127444203056785179004667877715054134848 : ℤ) := by
      simpa only [Nat.reduceAdd, row344, row345] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 344 1 1
    _ = _ := by decide +kernel

private theorem span346_348 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 346 2 = (735559584658793066782420066835621797231995379534488319836860770015402441560 : ℤ) := by
  calc
    _ = (8148569731180310137997245262949399694445374403327535316217888282228536119440 : ℤ) + (-7413010146521517071214825196113777897213379023793046996381027512213133677880 : ℤ) := by
      simpa only [Nat.reduceAdd, row346, row347] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 346 1 1
    _ = _ := by decide +kernel

private theorem span344_348 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 344 4 = (-4695737750498010414514034007883025586489869288408901229922083017632789355408 : ℤ) := by
  calc
    _ = (-5431297335156803481296454074718647383721864667943389549758943787648191796968 : ℤ) + (735559584658793066782420066835621797231995379534488319836860770015402441560 : ℤ) := by
      simpa only [Nat.reduceAdd, span344_346, span346_348] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 344 2 2
    _ = _ := by decide +kernel

private theorem span348_350 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 348 2 = (-15154681081991293992373467268826769732632561004967322017824668187103751643816 : ℤ) := by
  calc
    _ = (-4733055671024847640038295901806334289967502114394644137752066371809507958656 : ℤ) + (-10421625410966446352335171367020435442665058890572677880072601815294243685160 : ℤ) := by
      simpa only [Nat.reduceAdd, row348, row349] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 348 1 1
    _ = _ := by decide +kernel

private theorem span350_352 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 350 2 = (1066149704175253719263361527535074879021775761923457267779065186162789374360 : ℤ) := by
  calc
    _ = (679810138118728291347295106054300154188679758893772895615123906198889058096 : ℤ) + (386339566056525427916066421480774724833096003029684372163941279963900316264 : ℤ) := by
      simpa only [Nat.reduceAdd, row350, row351] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 350 1 1
    _ = _ := by decide +kernel

private theorem span348_352 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 348 4 = (-14088531377816040273110105741291694853610785243043864750045603000940962269456 : ℤ) := by
  calc
    _ = (-15154681081991293992373467268826769732632561004967322017824668187103751643816 : ℤ) + (1066149704175253719263361527535074879021775761923457267779065186162789374360 : ℤ) := by
      simpa only [Nat.reduceAdd, span348_350, span350_352] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 348 2 2
    _ = _ := by decide +kernel

private theorem span344_352 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 344 8 = (-18784269128314050687624139749174720440100654531452765979967686018573751624864 : ℤ) := by
  calc
    _ = (-4695737750498010414514034007883025586489869288408901229922083017632789355408 : ℤ) + (-14088531377816040273110105741291694853610785243043864750045603000940962269456 : ℤ) := by
      simpa only [Nat.reduceAdd, span344_348, span348_352] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 344 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows344To352 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 344 8 = (-18784269128314050687624139749174720440100654531452765979967686018573751624864 : ℤ) :=
  span344_352

#print axioms dottieFastReferenceRows344To352

end QuarticModel
