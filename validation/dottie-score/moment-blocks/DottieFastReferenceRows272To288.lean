import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row272_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 272 =
    (-285815556080006528217735608008572358653386603307607502397807913654572925104 : ℤ) := by decide +kernel

private theorem row272_block0 : dottiePairRowBlock dottieFastReferenceWeight 272 0 272 =
    (-5545951644443806707757053743991629003110387874044063390417187764057944859864 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 272 0 272).symm.trans (by decide +kernel)

private theorem row272 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 272 1 = (-5831767200523813235974789352000201361763774477351670892814995677712517784968 : ℤ) := by
  rw [dottiePairedRowSpan_one, row272_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 272 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 272 % 1024 = 272 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row272_block0]
  decide +kernel

private theorem row273_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 273 =
    (196918155478261749578894010696204839060576940049897677112087045210185314304 : ℤ) := by decide +kernel

private theorem row273_block0 : dottiePairRowBlock dottieFastReferenceWeight 273 0 273 =
    (14939956309913770013344869295580454327636132098409478558488555524500991209808 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 273 0 273).symm.trans (by decide +kernel)

private theorem row273 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 273 1 = (15136874465392031762923763306276659166696709038459376235600642569711176524112 : ℤ) := by
  rw [dottiePairedRowSpan_one, row273_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 273 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 273 % 1024 = 273 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row273_block0]
  decide +kernel

private theorem row274_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 274 =
    (219445710158938642964828458101478654930027236732188256061094235524559351288 : ℤ) := by decide +kernel

private theorem row274_block0 : dottiePairRowBlock dottieFastReferenceWeight 274 0 274 =
    (13463220894820458986283395971329703515480826368844959173025829516842111176544 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 274 0 274).symm.trans (by decide +kernel)

private theorem row274 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 274 1 = (13682666604979397629248224429431182170410853605577147429086923752366670527832 : ℤ) := by
  rw [dottiePairedRowSpan_one, row274_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 274 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 274 % 1024 = 274 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row274_block0]
  decide +kernel

private theorem row275_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 275 =
    (-329365502215279755059339337508184175895903410078593342969238513617128589312 : ℤ) := by decide +kernel

private theorem row275_block0 : dottiePairRowBlock dottieFastReferenceWeight 275 0 275 =
    (-1381723950615088576600770939092261552221427578259662111913043132253747296952 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 275 0 275).symm.trans (by decide +kernel)

private theorem row275 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 275 1 = (-1711089452830368331660110276600445728117330988338255454882281645870875886264 : ℤ) := by
  rw [dottiePairedRowSpan_one, row275_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 275 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 275 % 1024 = 275 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row275_block0]
  decide +kernel

private theorem row276_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 276 =
    (-401394144229211144832494578800408400061730993315077473374723292507297430800 : ℤ) := by decide +kernel

private theorem row276_block0 : dottiePairRowBlock dottieFastReferenceWeight 276 0 276 =
    (7098391368323892611964239487099301457383425623174575000563078418552124840496 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 276 0 276).symm.trans (by decide +kernel)

private theorem row276 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 276 1 = (6696997224094681467131744908298893057321694629859497527188355126044827409696 : ℤ) := by
  rw [dottiePairedRowSpan_one, row276_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 276 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 276 % 1024 = 276 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row276_block0]
  decide +kernel

private theorem row277_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 277 =
    (-162418518499499661538855289604763382408112046427650797802907565061195812608 : ℤ) := by decide +kernel

private theorem row277_block0 : dottiePairRowBlock dottieFastReferenceWeight 277 0 277 =
    (-936428570182535766413988723936371517379529873128546334781089013600930667800 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 277 0 277).symm.trans (by decide +kernel)

private theorem row277 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 277 1 = (-1098847088682035427952844013541134899787641919556197132583996578662126480408 : ℤ) := by
  rw [dottiePairedRowSpan_one, row277_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 277 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 277 % 1024 = 277 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row277_block0]
  decide +kernel

private theorem row278_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 278 =
    (-402905896394341384737069821297994433231683893628780717572948148430779659904 : ℤ) := by decide +kernel

private theorem row278_block0 : dottiePairRowBlock dottieFastReferenceWeight 278 0 278 =
    (10602162365040753732495733967414786834782133288343689449230293629988936800 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 278 0 278).symm.trans (by decide +kernel)

private theorem row278 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 278 1 = (-392303734029300631004574087330579646396901760340437028123717854800790723104 : ℤ) := by
  rw [dottiePairedRowSpan_one, row278_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 278 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 278 % 1024 = 278 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row278_block0]
  decide +kernel

private theorem row279_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 279 =
    (-335676303486452756682732968713691776031486799541960917054894629602424882152 : ℤ) := by decide +kernel

private theorem row279_block0 : dottiePairRowBlock dottieFastReferenceWeight 279 0 279 =
    (-5108316606199473735804016319520349076047576544942688113942467751928160791848 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 279 0 279).symm.trans (by decide +kernel)

private theorem row279 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 279 1 = (-5443992909685926492486749288234040852079063344484649030997362381530585674000 : ℤ) := by
  rw [dottiePairedRowSpan_one, row279_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 279 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 279 % 1024 = 279 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row279_block0]
  decide +kernel

private theorem row280_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 280 =
    (73089831811138725954627905757903246840505886534861973070631210616161789952 : ℤ) := by decide +kernel

private theorem row280_block0 : dottiePairRowBlock dottieFastReferenceWeight 280 0 280 =
    (-1520270866166289259634215021448465420335672255874248234357271150013800731248 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 280 0 280).symm.trans (by decide +kernel)

private theorem row280 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 280 1 = (-1447181034355150533679587115690562173495166369339386261286639939397638941296 : ℤ) := by
  rw [dottiePairedRowSpan_one, row280_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 280 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 280 % 1024 = 280 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row280_block0]
  decide +kernel

private theorem row281_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 281 =
    (156335643863636782748986283198526079537171722652496128683397743816011791104 : ℤ) := by decide +kernel

private theorem row281_block0 : dottiePairRowBlock dottieFastReferenceWeight 281 0 281 =
    (1326195168616985070221528004279877616860549791504714484455989580484791074264 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 281 0 281).symm.trans (by decide +kernel)

private theorem row281 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 281 1 = (1482530812480621852970514287478403696397721514157210613139387324300802865368 : ℤ) := by
  rw [dottiePairedRowSpan_one, row281_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 281 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 281 % 1024 = 281 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row281_block0]
  decide +kernel

private theorem row282_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 282 =
    (-215026557123877294326679617010222651196168087696194581455123529397213478912 : ℤ) := by decide +kernel

private theorem row282_block0 : dottiePairRowBlock dottieFastReferenceWeight 282 0 282 =
    (2528946828598568867296915121201071537467065330657103424611597472021481904112 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 282 0 282).symm.trans (by decide +kernel)

private theorem row282 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 282 1 = (2313920271474691572970235504190848886270897242960908843156473942624268425200 : ℤ) := by
  rw [dottiePairedRowSpan_one, row282_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 282 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 282 % 1024 = 282 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row282_block0]
  decide +kernel

private theorem row283_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 283 =
    (421534782728318310373406037562058525304482169028838131984565518864414453632 : ℤ) := by decide +kernel

private theorem row283_block0 : dottiePairRowBlock dottieFastReferenceWeight 283 0 283 =
    (1498866805060928662022735839311210610190201323438837624982294016347889320856 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 283 0 283).symm.trans (by decide +kernel)

private theorem row283 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 283 1 = (1920401587789246972396141876873269135494683492467675756966859535212303774488 : ℤ) := by
  rw [dottiePairedRowSpan_one, row283_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 283 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 283 % 1024 = 283 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row283_block0]
  decide +kernel

private theorem row284_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 284 =
    (-440913525828943000132381706660662542197375799830038411920434100619190075504 : ℤ) := by decide +kernel

private theorem row284_block0 : dottiePairRowBlock dottieFastReferenceWeight 284 0 284 =
    (-5719353195073609708397098141423024221900794286226410313468823679140540522432 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 284 0 284).symm.trans (by decide +kernel)

private theorem row284 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 284 1 = (-6160266720902552708529479848083686764098170086056448725389257779759730597936 : ℤ) := by
  rw [dottiePairedRowSpan_one, row284_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 284 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 284 % 1024 = 284 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row284_block0]
  decide +kernel

private theorem row285_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 285 =
    (417848198197533131380548952688991090859034638170161276819857862805584743832 : ℤ) := by decide +kernel

private theorem row285_block0 : dottiePairRowBlock dottieFastReferenceWeight 285 0 285 =
    (-7684885962855200551696719510382730443514228466731877663268100250047232002008 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 285 0 285).symm.trans (by decide +kernel)

private theorem row285 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 285 1 = (-7267037764657667420316170557693739352655193828561716386448242387241647258176 : ℤ) := by
  rw [dottiePairedRowSpan_one, row285_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 285 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 285 % 1024 = 285 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row285_block0]
  decide +kernel

private theorem row286_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 286 =
    (0 : ℤ) := by decide +kernel

private theorem row286_block0 : dottiePairRowBlock dottieFastReferenceWeight 286 0 286 =
    (2412326063908279876184413381896968335631813497642968614526994330480586687480 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 286 0 286).symm.trans (by decide +kernel)

private theorem row286 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 286 1 = (2412326063908279876184413381896968335631813497642968614526994330480586687480 : ℤ) := by
  rw [dottiePairedRowSpan_one, row286_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 286 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 286 % 1024 = 286 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row286_block0]
  decide +kernel

private theorem row287_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 287 =
    (6870210724811209738560025486613439964287292451670230485477152980154972544 : ℤ) := by decide +kernel

private theorem row287_block0 : dottiePairRowBlock dottieFastReferenceWeight 287 0 287 =
    (-7106307507720603337016453427401320013435462124530518318831925593521109901568 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 287 0 287).symm.trans (by decide +kernel)

private theorem row287 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 287 1 = (-7099437296995792127277893401914706573471174832078848088346448440540954929024 : ℤ) := by
  rw [dottiePairedRowSpan_one, row287_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 287 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 287 % 1024 = 287 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row287_block0]
  decide +kernel

private theorem span272_274 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 272 2 = (9305107264868218526948973954276457804932934561107705342785646891998658739144 : ℤ) := by
  calc
    _ = (-5831767200523813235974789352000201361763774477351670892814995677712517784968 : ℤ) + (15136874465392031762923763306276659166696709038459376235600642569711176524112 : ℤ) := by
      simpa only [Nat.reduceAdd, row272, row273] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 272 1 1
    _ = _ := by decide +kernel

private theorem span274_276 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 274 2 = (11971577152149029297588114152830736442293522617238891974204642106495794641568 : ℤ) := by
  calc
    _ = (13682666604979397629248224429431182170410853605577147429086923752366670527832 : ℤ) + (-1711089452830368331660110276600445728117330988338255454882281645870875886264 : ℤ) := by
      simpa only [Nat.reduceAdd, row274, row275] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 274 1 1
    _ = _ := by decide +kernel

private theorem span272_276 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 272 4 = (21276684417017247824537088107107194247226457178346597316990288998494453380712 : ℤ) := by
  calc
    _ = (9305107264868218526948973954276457804932934561107705342785646891998658739144 : ℤ) + (11971577152149029297588114152830736442293522617238891974204642106495794641568 : ℤ) := by
      simpa only [Nat.reduceAdd, span272_274, span274_276] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 272 2 2
    _ = _ := by decide +kernel

private theorem span276_278 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 276 2 = (5598150135412646039178900894757758157534052710303300394604358547382700929288 : ℤ) := by
  calc
    _ = (6696997224094681467131744908298893057321694629859497527188355126044827409696 : ℤ) + (-1098847088682035427952844013541134899787641919556197132583996578662126480408 : ℤ) := by
      simpa only [Nat.reduceAdd, row276, row277] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 276 1 1
    _ = _ := by decide +kernel

private theorem span278_280 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 278 2 = (-5836296643715227123491323375564620498475965104825086059121080236331376397104 : ℤ) := by
  calc
    _ = (-392303734029300631004574087330579646396901760340437028123717854800790723104 : ℤ) + (-5443992909685926492486749288234040852079063344484649030997362381530585674000 : ℤ) := by
      simpa only [Nat.reduceAdd, row278, row279] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 278 1 1
    _ = _ := by decide +kernel

private theorem span276_280 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 276 4 = (-238146508302581084312422480806862340941912394521785664516721688948675467816 : ℤ) := by
  calc
    _ = (5598150135412646039178900894757758157534052710303300394604358547382700929288 : ℤ) + (-5836296643715227123491323375564620498475965104825086059121080236331376397104 : ℤ) := by
      simpa only [Nat.reduceAdd, span276_278, span278_280] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 276 2 2
    _ = _ := by decide +kernel

private theorem span272_280 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 272 8 = (21038537908714666740224665626300331906284544783824811652473567309545777912896 : ℤ) := by
  calc
    _ = (21276684417017247824537088107107194247226457178346597316990288998494453380712 : ℤ) + (-238146508302581084312422480806862340941912394521785664516721688948675467816 : ℤ) := by
      simpa only [Nat.reduceAdd, span272_276, span276_280] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 272 4 4
    _ = _ := by decide +kernel

private theorem span280_282 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 280 2 = (35349778125471319290927171787841522902555144817824351852747384903163924072 : ℤ) := by
  calc
    _ = (-1447181034355150533679587115690562173495166369339386261286639939397638941296 : ℤ) + (1482530812480621852970514287478403696397721514157210613139387324300802865368 : ℤ) := by
      simpa only [Nat.reduceAdd, row280, row281] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 280 1 1
    _ = _ := by decide +kernel

private theorem span282_284 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 282 2 = (4234321859263938545366377381064118021765580735428584600123333477836572199688 : ℤ) := by
  calc
    _ = (2313920271474691572970235504190848886270897242960908843156473942624268425200 : ℤ) + (1920401587789246972396141876873269135494683492467675756966859535212303774488 : ℤ) := by
      simpa only [Nat.reduceAdd, row282, row283] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 282 1 1
    _ = _ := by decide +kernel

private theorem span280_284 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 280 4 = (4269671637389409864657304552851959544668135880246408951976080862739736123760 : ℤ) := by
  calc
    _ = (35349778125471319290927171787841522902555144817824351852747384903163924072 : ℤ) + (4234321859263938545366377381064118021765580735428584600123333477836572199688 : ℤ) := by
      simpa only [Nat.reduceAdd, span280_282, span282_284] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 280 2 2
    _ = _ := by decide +kernel

private theorem span284_286 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 284 2 = (-13427304485560220128845650405777426116753363914618165111837500167001377856112 : ℤ) := by
  calc
    _ = (-6160266720902552708529479848083686764098170086056448725389257779759730597936 : ℤ) + (-7267037764657667420316170557693739352655193828561716386448242387241647258176 : ℤ) := by
      simpa only [Nat.reduceAdd, row284, row285] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 284 1 1
    _ = _ := by decide +kernel

private theorem span286_288 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 286 2 = (-4687111233087512251093480020017738237839361334435879473819454110060368241544 : ℤ) := by
  calc
    _ = (2412326063908279876184413381896968335631813497642968614526994330480586687480 : ℤ) + (-7099437296995792127277893401914706573471174832078848088346448440540954929024 : ℤ) := by
      simpa only [Nat.reduceAdd, row286, row287] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 286 1 1
    _ = _ := by decide +kernel

private theorem span284_288 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 284 4 = (-18114415718647732379939130425795164354592725249054044585656954277061746097656 : ℤ) := by
  calc
    _ = (-13427304485560220128845650405777426116753363914618165111837500167001377856112 : ℤ) + (-4687111233087512251093480020017738237839361334435879473819454110060368241544 : ℤ) := by
      simpa only [Nat.reduceAdd, span284_286, span286_288] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 284 2 2
    _ = _ := by decide +kernel

private theorem span280_288 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 280 8 = (-13844744081258322515281825872943204809924589368807635633680873414322009973896 : ℤ) := by
  calc
    _ = (4269671637389409864657304552851959544668135880246408951976080862739736123760 : ℤ) + (-18114415718647732379939130425795164354592725249054044585656954277061746097656 : ℤ) := by
      simpa only [Nat.reduceAdd, span280_284, span284_288] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 280 4 4
    _ = _ := by decide +kernel

private theorem span272_288 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 272 16 = (7193793827456344224942839753357127096359955415017176018792693895223767939000 : ℤ) := by
  calc
    _ = (21038537908714666740224665626300331906284544783824811652473567309545777912896 : ℤ) + (-13844744081258322515281825872943204809924589368807635633680873414322009973896 : ℤ) := by
      simpa only [Nat.reduceAdd, span272_280, span280_288] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 272 8 8
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows272To288 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 272 16 = (7193793827456344224942839753357127096359955415017176018792693895223767939000 : ℤ) :=
  span272_288

#print axioms dottieFastReferenceRows272To288

end QuarticModel
