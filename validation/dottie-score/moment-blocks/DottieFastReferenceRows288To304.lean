import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row288_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 288 =
    (82724540652697559767307744492130897760059619514577370582281685292140130968 : ℤ) := by decide +kernel

private theorem row288_block0 : dottiePairRowBlock dottieFastReferenceWeight 288 0 288 =
    (-12675058883385219647929433201300152998845783847576238339338570235316773477072 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 288 0 288).symm.trans (by decide +kernel)

private theorem row288 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 288 1 = (-12592334342732522088162125456808022101085724228061660968756288550024633346104 : ℤ) := by
  rw [dottiePairedRowSpan_one, row288_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 288 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 288 % 1024 = 288 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row288_block0]
  decide +kernel

private theorem row289_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 289 =
    (223255360070513214343565188571462703455048660655485666726601550822297925136 : ℤ) := by decide +kernel

private theorem row289_block0 : dottiePairRowBlock dottieFastReferenceWeight 289 0 289 =
    (2908883714185365397786460528083392888935930685919697900426403530291196339520 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 289 0 289).symm.trans (by decide +kernel)

private theorem row289 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 289 1 = (3132139074255878612130025716654855592390979346575183567153005081113494264656 : ℤ) := by
  rw [dottiePairedRowSpan_one, row289_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 289 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 289 % 1024 = 289 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row289_block0]
  decide +kernel

private theorem row290_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 290 =
    (419136688589319124149886341879697680986020514672076679355559350515640178752 : ℤ) := by decide +kernel

private theorem row290_block0 : dottiePairRowBlock dottieFastReferenceWeight 290 0 290 =
    (-5447111010379031976100346316964489925325441386017075036969646940310548472848 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 290 0 290).symm.trans (by decide +kernel)

private theorem row290 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 290 1 = (-5027974321789712851950459975084792244339420871344998357614087589794908294096 : ℤ) := by
  rw [dottiePairedRowSpan_one, row290_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 290 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 290 % 1024 = 290 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row290_block0]
  decide +kernel

private theorem row291_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 291 =
    (384432958663085836684216234519963279792756477265829483637256435020723690984 : ℤ) := by decide +kernel

private theorem row291_block0 : dottiePairRowBlock dottieFastReferenceWeight 291 0 291 =
    (1975236287645952248104356249006988247145755581182156098934393595589361143456 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 291 0 291).symm.trans (by decide +kernel)

private theorem row291 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 291 1 = (2359669246309038084788572483526951526938512058447985582571650030610084834440 : ℤ) := by
  rw [dottiePairedRowSpan_one, row291_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 291 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 291 % 1024 = 291 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row291_block0]
  decide +kernel

private theorem row292_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 292 =
    (275424026142617602824894522117629115555829414839489878850899647615349939656 : ℤ) := by decide +kernel

private theorem row292_block0 : dottiePairRowBlock dottieFastReferenceWeight 292 0 292 =
    (4016865292243016684647941283099620490967681558955269344746729782329490051880 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 292 0 292).symm.trans (by decide +kernel)

private theorem row292 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 292 1 = (4292289318385634287472835805217249606523510973794759223597629429944839991536 : ℤ) := by
  rw [dottiePairedRowSpan_one, row292_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 292 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 292 % 1024 = 292 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row292_block0]
  decide +kernel

private theorem row293_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 293 =
    (273015600945843172836030326283452765730327309499880339387977024766070147072 : ℤ) := by decide +kernel

private theorem row293_block0 : dottiePairRowBlock dottieFastReferenceWeight 293 0 293 =
    (-5265415446263011432695037164036176541783149656022990543870807440272407174216 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 293 0 293).symm.trans (by decide +kernel)

private theorem row293 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 293 1 = (-4992399845317168259859006837752723776052822346523110204482830415506337027144 : ℤ) := by
  rw [dottiePairedRowSpan_one, row293_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 293 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 293 % 1024 = 293 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row293_block0]
  decide +kernel

private theorem row294_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 294 =
    (-380715930428154026493786887438779429681734391397828122063805625331100489288 : ℤ) := by decide +kernel

private theorem row294_block0 : dottiePairRowBlock dottieFastReferenceWeight 294 0 294 =
    (-9253637473014854929472956117998030634180345073876071397286531846443932868120 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 294 0 294).symm.trans (by decide +kernel)

private theorem row294 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 294 1 = (-9634353403443008955966743005436810063862079465273899519350337471775033357408 : ℤ) := by
  rw [dottiePairedRowSpan_one, row294_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 294 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 294 % 1024 = 294 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row294_block0]
  decide +kernel

private theorem row295_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 295 =
    (-419097207445081733442815554923812780945977340174612902401825337747182634528 : ℤ) := by decide +kernel

private theorem row295_block0 : dottiePairRowBlock dottieFastReferenceWeight 295 0 295 =
    (-7091026081161252893783152330181451428304868775280193894260975796227647760056 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 295 0 295).symm.trans (by decide +kernel)

private theorem row295 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 295 1 = (-7510123288606334627225967885105264209250846115454806796662801133974830394584 : ℤ) := by
  rw [dottiePairedRowSpan_one, row295_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 295 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 295 % 1024 = 295 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row295_block0]
  decide +kernel

private theorem row296_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 296 =
    (205732036812673053122835297390136085862535855793337241413459177860495462960 : ℤ) := by decide +kernel

private theorem row296_block0 : dottiePairRowBlock dottieFastReferenceWeight 296 0 296 =
    (-201761765026717171100305030823267327045419333375998101435699805089476468680 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 296 0 296).symm.trans (by decide +kernel)

private theorem row296 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 296 1 = (3970271785955882022530266566868758817116522417339139977759372771018994280 : ℤ) := by
  rw [dottiePairedRowSpan_one, row296_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 296 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 296 % 1024 = 296 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row296_block0]
  decide +kernel

private theorem row297_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 297 =
    (300063004023216142805160814246793856919063834247011004165033793375538050888 : ℤ) := by decide +kernel

private theorem row297_block0 : dottiePairRowBlock dottieFastReferenceWeight 297 0 297 =
    (-1559818934254015991972217957653454265833147607628728643601026343497651967712 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 297 0 297).symm.trans (by decide +kernel)

private theorem row297 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 297 1 = (-1259755930230799849167057143406660408914083773381717639435992550122113916824 : ℤ) := by
  rw [dottiePairedRowSpan_one, row297_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 297 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 297 % 1024 = 297 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row297_block0]
  decide +kernel

private theorem row298_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 298 =
    (354303577674463581533232099663244222990556783092452125534341949861026007624 : ℤ) := by decide +kernel

private theorem row298_block0 : dottiePairRowBlock dottieFastReferenceWeight 298 0 298 =
    (11155027164824596925891570190654975275954182174017771494296811679280686530352 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 298 0 298).symm.trans (by decide +kernel)

private theorem row298 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 298 1 = (11509330742499060507424802290318219498944738957110223619831153629141712537976 : ℤ) := by
  rw [dottiePairedRowSpan_one, row298_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 298 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 298 % 1024 = 298 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row298_block0]
  decide +kernel

private theorem row299_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 299 =
    (-365405246880445797624371940559033278227831367320786110532528203584929138336 : ℤ) := by decide +kernel

private theorem row299_block0 : dottiePairRowBlock dottieFastReferenceWeight 299 0 299 =
    (-4418256675572037349878557215970353199408877964302695696712489237471227467592 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 299 0 299).symm.trans (by decide +kernel)

private theorem row299 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 299 1 = (-4783661922452483147502929156529386477636709331623481807245017441056156605928 : ℤ) := by
  rw [dottiePairedRowSpan_one, row299_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 299 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 299 % 1024 = 299 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row299_block0]
  decide +kernel

private theorem row300_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 300 =
    (417686069623332054710120099713139547945863463039605657738146328331034115984 : ℤ) := by decide +kernel

private theorem row300_block0 : dottiePairRowBlock dottieFastReferenceWeight 300 0 300 =
    (-35459985381429298419650810803936493136419926859423526707766857001428185320 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 300 0 300).symm.trans (by decide +kernel)

private theorem row300 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 300 1 = (382226084241902756290469288909203054809443536180182131030379471329605930664 : ℤ) := by
  rw [dottiePairedRowSpan_one, row300_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 300 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 300 % 1024 = 300 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row300_block0]
  decide +kernel

private theorem row301_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 301 =
    (183610563016929356247045079018804388557904618865673027440055234416228846624 : ℤ) := by decide +kernel

private theorem row301_block0 : dottiePairRowBlock dottieFastReferenceWeight 301 0 301 =
    (-3399782755521652624745816989667319377929131816295973026513228582734226149608 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 301 0 301).symm.trans (by decide +kernel)

private theorem row301 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 301 1 = (-3216172192504723268498771910648514989371227197430299999073173348317997302984 : ℤ) := by
  rw [dottiePairedRowSpan_one, row301_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 301 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 301 % 1024 = 301 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row301_block0]
  decide +kernel

private theorem row302_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 302 =
    (420030848384384655758727942582746467579812970578489598953437998347616508728 : ℤ) := by decide +kernel

private theorem row302_block0 : dottiePairRowBlock dottieFastReferenceWeight 302 0 302 =
    (-945060109409583971404419371774777301368316504793550474292056930275670402168 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 302 0 302).symm.trans (by decide +kernel)

private theorem row302 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 302 1 = (-525029261025199315645691429192030833788503534215060875338618931928053893440 : ℤ) := by
  rw [dottiePairedRowSpan_one, row302_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 302 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 302 % 1024 = 302 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row302_block0]
  decide +kernel

private theorem row303_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 303 =
    (-206125019012894949639677635233020980524745418947167970066503662342234934296 : ℤ) := by decide +kernel

private theorem row303_block0 : dottiePairRowBlock dottieFastReferenceWeight 303 0 303 =
    (-2958505441256308245136640669256144433796187254122825388425655027559543767656 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 303 0 303).symm.trans (by decide +kernel)

private theorem row303 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 303 1 = (-3164630460269203194776318304489165414320932673069993358492158689901778701952 : ℤ) := by
  rw [dottiePairedRowSpan_one, row303_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 303 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 303 % 1024 = 303 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row303_block0]
  decide +kernel

private theorem span288_290 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 288 2 = (-9460195268476643476032099740153166508694744881486477401603283468911139081448 : ℤ) := by
  calc
    _ = (-12592334342732522088162125456808022101085724228061660968756288550024633346104 : ℤ) + (3132139074255878612130025716654855592390979346575183567153005081113494264656 : ℤ) := by
      simpa only [Nat.reduceAdd, row288, row289] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 288 1 1
    _ = _ := by decide +kernel

private theorem span290_292 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 290 2 = (-2668305075480674767161887491557840717400908812897012775042437559184823459656 : ℤ) := by
  calc
    _ = (-5027974321789712851950459975084792244339420871344998357614087589794908294096 : ℤ) + (2359669246309038084788572483526951526938512058447985582571650030610084834440 : ℤ) := by
      simpa only [Nat.reduceAdd, row290, row291] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 290 1 1
    _ = _ := by decide +kernel

private theorem span288_292 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 288 4 = (-12128500343957318243193987231711007226095653694383490176645721028095962541104 : ℤ) := by
  calc
    _ = (-9460195268476643476032099740153166508694744881486477401603283468911139081448 : ℤ) + (-2668305075480674767161887491557840717400908812897012775042437559184823459656 : ℤ) := by
      simpa only [Nat.reduceAdd, span288_290, span290_292] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 288 2 2
    _ = _ := by decide +kernel

private theorem span292_294 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 292 2 = (-700110526931533972386171032535474169529311372728350980885200985561497035608 : ℤ) := by
  calc
    _ = (4292289318385634287472835805217249606523510973794759223597629429944839991536 : ℤ) + (-4992399845317168259859006837752723776052822346523110204482830415506337027144 : ℤ) := by
      simpa only [Nat.reduceAdd, row292, row293] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 292 1 1
    _ = _ := by decide +kernel

private theorem span294_296 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 294 2 = (-17144476692049343583192710890542074273112925580728706316013138605749863751992 : ℤ) := by
  calc
    _ = (-9634353403443008955966743005436810063862079465273899519350337471775033357408 : ℤ) + (-7510123288606334627225967885105264209250846115454806796662801133974830394584 : ℤ) := by
      simpa only [Nat.reduceAdd, row294, row295] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 294 1 1
    _ = _ := by decide +kernel

private theorem span292_296 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 292 4 = (-17844587218980877555578881923077548442642236953457057296898339591311360787600 : ℤ) := by
  calc
    _ = (-700110526931533972386171032535474169529311372728350980885200985561497035608 : ℤ) + (-17144476692049343583192710890542074273112925580728706316013138605749863751992 : ℤ) := by
      simpa only [Nat.reduceAdd, span292_294, span294_296] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 292 2 2
    _ = _ := by decide +kernel

private theorem span288_296 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 288 8 = (-29973087562938195798772869154788555668737890647840547473544060619407323328704 : ℤ) := by
  calc
    _ = (-12128500343957318243193987231711007226095653694383490176645721028095962541104 : ℤ) + (-17844587218980877555578881923077548442642236953457057296898339591311360787600 : ℤ) := by
      simpa only [Nat.reduceAdd, span288_292, span292_296] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 288 4 4
    _ = _ := by decide +kernel

private theorem span296_298 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 296 2 = (-1255785658444843967144526876839791650096967250964378499458233177351094922544 : ℤ) := by
  calc
    _ = (3970271785955882022530266566868758817116522417339139977759372771018994280 : ℤ) + (-1259755930230799849167057143406660408914083773381717639435992550122113916824 : ℤ) := by
      simpa only [Nat.reduceAdd, row296, row297] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 296 1 1
    _ = _ := by decide +kernel

private theorem span298_300 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 298 2 = (6725668820046577359921873133788833021308029625486741812586136188085555932048 : ℤ) := by
  calc
    _ = (11509330742499060507424802290318219498944738957110223619831153629141712537976 : ℤ) + (-4783661922452483147502929156529386477636709331623481807245017441056156605928 : ℤ) := by
      simpa only [Nat.reduceAdd, row298, row299] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 298 1 1
    _ = _ := by decide +kernel

private theorem span296_300 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 296 4 = (5469883161601733392777346256949041371211062374522363313127903010734461009504 : ℤ) := by
  calc
    _ = (-1255785658444843967144526876839791650096967250964378499458233177351094922544 : ℤ) + (6725668820046577359921873133788833021308029625486741812586136188085555932048 : ℤ) := by
      simpa only [Nat.reduceAdd, span296_298, span298_300] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 296 2 2
    _ = _ := by decide +kernel

private theorem span300_302 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 300 2 = (-2833946108262820512208302621739311934561783661250117868042793876988391372320 : ℤ) := by
  calc
    _ = (382226084241902756290469288909203054809443536180182131030379471329605930664 : ℤ) + (-3216172192504723268498771910648514989371227197430299999073173348317997302984 : ℤ) := by
      simpa only [Nat.reduceAdd, row300, row301] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 300 1 1
    _ = _ := by decide +kernel

private theorem span302_304 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 302 2 = (-3689659721294402510422009733681196248109436207285054233830777621829832595392 : ℤ) := by
  calc
    _ = (-525029261025199315645691429192030833788503534215060875338618931928053893440 : ℤ) + (-3164630460269203194776318304489165414320932673069993358492158689901778701952 : ℤ) := by
      simpa only [Nat.reduceAdd, row302, row303] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 302 1 1
    _ = _ := by decide +kernel

private theorem span300_304 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 300 4 = (-6523605829557223022630312355420508182671219868535172101873571498818223967712 : ℤ) := by
  calc
    _ = (-2833946108262820512208302621739311934561783661250117868042793876988391372320 : ℤ) + (-3689659721294402510422009733681196248109436207285054233830777621829832595392 : ℤ) := by
      simpa only [Nat.reduceAdd, span300_302, span302_304] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 300 2 2
    _ = _ := by decide +kernel

private theorem span296_304 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 296 8 = (-1053722667955489629852966098471466811460157494012808788745668488083762958208 : ℤ) := by
  calc
    _ = (5469883161601733392777346256949041371211062374522363313127903010734461009504 : ℤ) + (-6523605829557223022630312355420508182671219868535172101873571498818223967712 : ℤ) := by
      simpa only [Nat.reduceAdd, span296_300, span300_304] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 296 4 4
    _ = _ := by decide +kernel

private theorem span288_304 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 288 16 = (-31026810230893685428625835253260022480198048141853356262289729107491086286912 : ℤ) := by
  calc
    _ = (-29973087562938195798772869154788555668737890647840547473544060619407323328704 : ℤ) + (-1053722667955489629852966098471466811460157494012808788745668488083762958208 : ℤ) := by
      simpa only [Nat.reduceAdd, span288_296, span296_304] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 288 8 8
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows288To304 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 288 16 = (-31026810230893685428625835253260022480198048141853356262289729107491086286912 : ℤ) :=
  span288_304

#print axioms dottieFastReferenceRows288To304

end QuarticModel
