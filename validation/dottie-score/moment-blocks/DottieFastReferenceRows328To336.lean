import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row328_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 328 =
    (-322726032439471157161585074324335696285364679322419789481625840355854128704 : ℤ) := by decide +kernel

private theorem row328_block0 : dottiePairRowBlock dottieFastReferenceWeight 328 0 328 =
    (1902579531143531668811118148503924407501467572227732548874683961549767702120 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 328 0 328).symm.trans (by decide +kernel)

private theorem row328 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 328 1 = (1579853498704060511649533074179588711216102892905312759393058121193913573416 : ℤ) := by
  rw [dottiePairedRowSpan_one, row328_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 328 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 328 % 1024 = 328 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row328_block0]
  decide +kernel

private theorem row329_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 329 =
    (-382836078100991100447735910800124749951973366219652758198154125038961508544 : ℤ) := by decide +kernel

private theorem row329_block0 : dottiePairRowBlock dottieFastReferenceWeight 329 0 329 =
    (-3550324629267626417061326938021287181757040325485652308493699966610520876360 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 329 0 329).symm.trans (by decide +kernel)

private theorem row329 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 329 1 = (-3933160707368617517509062848821411931709013691705305066691854091649482384904 : ℤ) := by
  rw [dottiePairedRowSpan_one, row329_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 329 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 329 % 1024 = 329 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row329_block0]
  decide +kernel

private theorem row330_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 330 =
    (335419906017618137095709184918772084812208502208781582657479576232512305368 : ℤ) := by decide +kernel

private theorem row330_block0 : dottiePairRowBlock dottieFastReferenceWeight 330 0 330 =
    (3929677954528427783689482472056329377893839517216195743504285749001674185040 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 330 0 330).symm.trans (by decide +kernel)

private theorem row330 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 330 1 = (4265097860546045920785191656975101462706048019424977326161765325234186490408 : ℤ) := by
  rw [dottiePairedRowSpan_one, row330_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 330 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 330 % 1024 = 330 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row330_block0]
  decide +kernel

private theorem row331_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 331 =
    (182272371887464102668244299526787565671433587904855774298155949571366274432 : ℤ) := by decide +kernel

private theorem row331_block0 : dottiePairRowBlock dottieFastReferenceWeight 331 0 331 =
    (-6477504225073790635731322382189973816311887277089490350752059797805802525736 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 331 0 331).symm.trans (by decide +kernel)

private theorem row331 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 331 1 = (-6295231853186326533063078082663186250640453689184634576453903848234436251304 : ℤ) := by
  rw [dottiePairedRowSpan_one, row331_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 331 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 331 % 1024 = 331 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row331_block0]
  decide +kernel

private theorem row332_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 332 =
    (376900023612039474344710936821633984160198372092999459939045938575887494784 : ℤ) := by decide +kernel

private theorem row332_block0 : dottiePairRowBlock dottieFastReferenceWeight 332 0 332 =
    (-9388160520411713398008784296922748957577724298834359753934699537335245431272 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 332 0 332).symm.trans (by decide +kernel)

private theorem row332 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 332 1 = (-9011260496799673923664073360101114973417525926741360293995653598759357936488 : ℤ) := by
  rw [dottiePairedRowSpan_one, row332_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 332 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 332 % 1024 = 332 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row332_block0]
  decide +kernel

private theorem row333_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 333 =
    (318031174760488985059381174176583943200252193694771014796247103952044465208 : ℤ) := by decide +kernel

private theorem row333_block0 : dottiePairRowBlock dottieFastReferenceWeight 333 0 333 =
    (-2356496626423274496790250711638584474281300868181114743865937460343403794120 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 333 0 333).symm.trans (by decide +kernel)

private theorem row333 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 333 1 = (-2038465451662785511730869537462000531081048674486343729069690356391359328912 : ℤ) := by
  rw [dottiePairedRowSpan_one, row333_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 333 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 333 % 1024 = 333 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row333_block0]
  decide +kernel

private theorem row334_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 334 =
    (326462195474579328608099539920564946331908217799918998330966735878820527576 : ℤ) := by decide +kernel

private theorem row334_block0 : dottiePairRowBlock dottieFastReferenceWeight 334 0 334 =
    (-57423202620756317743851092753023995823542716749623456003898704434764245288 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 334 0 334).symm.trans (by decide +kernel)

private theorem row334 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 334 1 = (269038992853823010864248447167540950508365501050295542327068031444056282288 : ℤ) := by
  rw [dottiePairedRowSpan_one, row334_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 334 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 334 % 1024 = 334 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row334_block0]
  decide +kernel

private theorem row335_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 335 =
    (370099595449244463779187178026564737583753039194344549723368892949470343512 : ℤ) := by decide +kernel

private theorem row335_block0 : dottiePairRowBlock dottieFastReferenceWeight 335 0 335 =
    (-3221474996635799990982108375201470012376456907810894649361905528175911485712 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 335 0 335).symm.trans (by decide +kernel)

private theorem row335 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 335 1 = (-2851375401186555527202921197174905274792703868616550099638536635226441142200 : ℤ) := by
  rw [dottiePairedRowSpan_one, row335_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 335 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 335 % 1024 = 335 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row335_block0]
  decide +kernel

private theorem span328_330 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 328 2 = (-2353307208664557005859529774641823220492910798799992307298795970455568811488 : ℤ) := by
  calc
    _ = (1579853498704060511649533074179588711216102892905312759393058121193913573416 : ℤ) + (-3933160707368617517509062848821411931709013691705305066691854091649482384904 : ℤ) := by
      simpa only [Nat.reduceAdd, row328, row329] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 328 1 1
    _ = _ := by decide +kernel

private theorem span330_332 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 330 2 = (-2030133992640280612277886425688084787934405669759657250292138523000249760896 : ℤ) := by
  calc
    _ = (4265097860546045920785191656975101462706048019424977326161765325234186490408 : ℤ) + (-6295231853186326533063078082663186250640453689184634576453903848234436251304 : ℤ) := by
      simpa only [Nat.reduceAdd, row330, row331] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 330 1 1
    _ = _ := by decide +kernel

private theorem span328_332 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 328 4 = (-4383441201304837618137416200329908008427316468559649557590934493455818572384 : ℤ) := by
  calc
    _ = (-2353307208664557005859529774641823220492910798799992307298795970455568811488 : ℤ) + (-2030133992640280612277886425688084787934405669759657250292138523000249760896 : ℤ) := by
      simpa only [Nat.reduceAdd, span328_330, span330_332] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 328 2 2
    _ = _ := by decide +kernel

private theorem span332_334 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 332 2 = (-11049725948462459435394942897563115504498574601227704023065343955150717265400 : ℤ) := by
  calc
    _ = (-9011260496799673923664073360101114973417525926741360293995653598759357936488 : ℤ) + (-2038465451662785511730869537462000531081048674486343729069690356391359328912 : ℤ) := by
      simpa only [Nat.reduceAdd, row332, row333] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 332 1 1
    _ = _ := by decide +kernel

private theorem span334_336 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 334 2 = (-2582336408332732516338672750007364324284338367566254557311468603782384859912 : ℤ) := by
  calc
    _ = (269038992853823010864248447167540950508365501050295542327068031444056282288 : ℤ) + (-2851375401186555527202921197174905274792703868616550099638536635226441142200 : ℤ) := by
      simpa only [Nat.reduceAdd, row334, row335] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 334 1 1
    _ = _ := by decide +kernel

private theorem span332_336 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 332 4 = (-13632062356795191951733615647570479828782912968793958580376812558933102125312 : ℤ) := by
  calc
    _ = (-11049725948462459435394942897563115504498574601227704023065343955150717265400 : ℤ) + (-2582336408332732516338672750007364324284338367566254557311468603782384859912 : ℤ) := by
      simpa only [Nat.reduceAdd, span332_334, span334_336] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 332 2 2
    _ = _ := by decide +kernel

private theorem span328_336 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 328 8 = (-18015503558100029569871031847900387837210229437353608137967747052388920697696 : ℤ) := by
  calc
    _ = (-4383441201304837618137416200329908008427316468559649557590934493455818572384 : ℤ) + (-13632062356795191951733615647570479828782912968793958580376812558933102125312 : ℤ) := by
      simpa only [Nat.reduceAdd, span328_332, span332_336] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 328 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows328To336 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 328 8 = (-18015503558100029569871031847900387837210229437353608137967747052388920697696 : ℤ) :=
  span328_336

#print axioms dottieFastReferenceRows328To336

end QuarticModel
