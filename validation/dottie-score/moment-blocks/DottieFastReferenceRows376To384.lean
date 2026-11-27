import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row376_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 376 =
    (42331894222969104077436732217000067304315566444095727872624776254221795184 : ℤ) := by decide +kernel

private theorem row376_block0 : dottiePairRowBlock dottieFastReferenceWeight 376 0 376 =
    (-3558084288530742441916264433784681962364606291485037796259381104343216616648 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 376 0 376).symm.trans (by decide +kernel)

private theorem row376 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 376 1 = (-3515752394307773337838827701567681895060290725040942068386756328088994821464 : ℤ) := by
  rw [dottiePairedRowSpan_one, row376_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 376 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 376 % 1024 = 376 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row376_block0]
  decide +kernel

private theorem row377_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 377 =
    (-324208831136214085570413292651720132926773508878789157372356218689085926200 : ℤ) := by decide +kernel

private theorem row377_block0 : dottiePairRowBlock dottieFastReferenceWeight 377 0 377 =
    (1808606808170074359045899739203164698827715710084615898772317124910003087992 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 377 0 377).symm.trans (by decide +kernel)

private theorem row377 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 377 1 = (1484397977033860273475486446551444565900942201205826741399960906220917161792 : ℤ) := by
  rw [dottiePairedRowSpan_one, row377_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 377 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 377 % 1024 = 377 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row377_block0]
  decide +kernel

private theorem row378_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 378 =
    (327316426568997783832553004393999103183085464641937068320078121810273148984 : ℤ) := by decide +kernel

private theorem row378_block0 : dottiePairRowBlock dottieFastReferenceWeight 378 0 378 =
    (-1990936607402688261317797135339727117157407790815775865961142998352772056248 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 378 0 378).symm.trans (by decide +kernel)

private theorem row378 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 378 1 = (-1663620180833690477485244130945728013974322326173838797641064876542498907264 : ℤ) := by
  rw [dottiePairedRowSpan_one, row378_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 378 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 378 % 1024 = 378 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row378_block0]
  decide +kernel

private theorem row379_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 379 =
    (-333947467819333389993241968186757790883146874460723176206783776853202844528 : ℤ) := by decide +kernel

private theorem row379_block0 : dottiePairRowBlock dottieFastReferenceWeight 379 0 379 =
    (6219096689125738563909565701690382573542070897158254378568269560967918777944 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 379 0 379).symm.trans (by decide +kernel)

private theorem row379 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 379 1 = (5885149221306405173916323733503624782658924022697531202361485784114715933416 : ℤ) := by
  rw [dottiePairedRowSpan_one, row379_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 379 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 379 % 1024 = 379 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row379_block0]
  decide +kernel

private theorem row380_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 380 =
    (-267040758458527161671902144145219009342429729337524773266695884422793200952 : ℤ) := by decide +kernel

private theorem row380_block0 : dottiePairRowBlock dottieFastReferenceWeight 380 0 380 =
    (-10657582881025778074927281324792448610880071561902571114404132556669500782296 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 380 0 380).symm.trans (by decide +kernel)

private theorem row380 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 380 1 = (-10924623639484305236599183468937667620222501291240095887670828441092293983248 : ℤ) := by
  rw [dottiePairedRowSpan_one, row380_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 380 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 380 % 1024 = 380 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row380_block0]
  decide +kernel

private theorem row381_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 381 =
    (-58119509368209543493227051230248939212175856510208127263431842901548505088 : ℤ) := by decide +kernel

private theorem row381_block0 : dottiePairRowBlock dottieFastReferenceWeight 381 0 381 =
    (1327436118444702483372175774423582162927173491780735681708730499148467082456 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 381 0 381).symm.trans (by decide +kernel)

private theorem row381 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 381 1 = (1269316609076492939878948723193333223714997635270527554445298656246918577368 : ℤ) := by
  rw [dottiePairedRowSpan_one, row381_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 381 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 381 % 1024 = 381 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row381_block0]
  decide +kernel

private theorem row382_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 382 =
    (-329686550254826177527411609384963093523066339992088243406473161452238798848 : ℤ) := by decide +kernel

private theorem row382_block0 : dottiePairRowBlock dottieFastReferenceWeight 382 0 382 =
    (-8157521215589012919608931549284570495916546972469049493606117184025852049904 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 382 0 382).symm.trans (by decide +kernel)

private theorem row382 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 382 1 = (-8487207765843839097136343158669533589439613312461137737012590345478090848752 : ℤ) := by
  rw [dottiePairedRowSpan_one, row382_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 382 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 382 % 1024 = 382 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row382_block0]
  decide +kernel

private theorem row383_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 383 =
    (82843091859809085494025631472275769285534979602418776660935405850140884800 : ℤ) := by decide +kernel

private theorem row383_block0 : dottiePairRowBlock dottieFastReferenceWeight 383 0 383 =
    (-5996278345180102889106250844881076622958824102856967896333675011854447022800 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 383 0 383).symm.trans (by decide +kernel)

private theorem row383 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 383 1 = (-5913435253320293803612225213408800853673289123254549119672739606004306138000 : ℤ) := by
  rw [dottiePairedRowSpan_one, row383_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 383 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 383 % 1024 = 383 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row383_block0]
  decide +kernel

private theorem span376_378 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 376 2 = (-2031354417273913064363341255016237329159348523835115326986795421868077659672 : ℤ) := by
  calc
    _ = (-3515752394307773337838827701567681895060290725040942068386756328088994821464 : ℤ) + (1484397977033860273475486446551444565900942201205826741399960906220917161792 : ℤ) := by
      simpa only [Nat.reduceAdd, row376, row377] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 376 1 1
    _ = _ := by decide +kernel

private theorem span378_380 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 378 2 = (4221529040472714696431079602557896768684601696523692404720420907572217026152 : ℤ) := by
  calc
    _ = (-1663620180833690477485244130945728013974322326173838797641064876542498907264 : ℤ) + (5885149221306405173916323733503624782658924022697531202361485784114715933416 : ℤ) := by
      simpa only [Nat.reduceAdd, row378, row379] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 378 1 1
    _ = _ := by decide +kernel

private theorem span376_380 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 376 4 = (2190174623198801632067738347541659439525253172688577077733625485704139366480 : ℤ) := by
  calc
    _ = (-2031354417273913064363341255016237329159348523835115326986795421868077659672 : ℤ) + (4221529040472714696431079602557896768684601696523692404720420907572217026152 : ℤ) := by
      simpa only [Nat.reduceAdd, span376_378, span378_380] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 376 2 2
    _ = _ := by decide +kernel

private theorem span380_382 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 380 2 = (-9655307030407812296720234745744334396507503655969568333225529784845375405880 : ℤ) := by
  calc
    _ = (-10924623639484305236599183468937667620222501291240095887670828441092293983248 : ℤ) + (1269316609076492939878948723193333223714997635270527554445298656246918577368 : ℤ) := by
      simpa only [Nat.reduceAdd, row380, row381] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 380 1 1
    _ = _ := by decide +kernel

private theorem span382_384 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 382 2 = (-14400643019164132900748568372078334443112902435715686856685329951482396986752 : ℤ) := by
  calc
    _ = (-8487207765843839097136343158669533589439613312461137737012590345478090848752 : ℤ) + (-5913435253320293803612225213408800853673289123254549119672739606004306138000 : ℤ) := by
      simpa only [Nat.reduceAdd, row382, row383] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 382 1 1
    _ = _ := by decide +kernel

private theorem span380_384 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 380 4 = (-24055950049571945197468803117822668839620406091685255189910859736327772392632 : ℤ) := by
  calc
    _ = (-9655307030407812296720234745744334396507503655969568333225529784845375405880 : ℤ) + (-14400643019164132900748568372078334443112902435715686856685329951482396986752 : ℤ) := by
      simpa only [Nat.reduceAdd, span380_382, span382_384] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 380 2 2
    _ = _ := by decide +kernel

private theorem span376_384 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 376 8 = (-21865775426373143565401064770281009400095152918996678112177234250623633026152 : ℤ) := by
  calc
    _ = (2190174623198801632067738347541659439525253172688577077733625485704139366480 : ℤ) + (-24055950049571945197468803117822668839620406091685255189910859736327772392632 : ℤ) := by
      simpa only [Nat.reduceAdd, span376_380, span380_384] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 376 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows376To384 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 376 8 = (-21865775426373143565401064770281009400095152918996678112177234250623633026152 : ℤ) :=
  span376_384

#print axioms dottieFastReferenceRows376To384

end QuarticModel
