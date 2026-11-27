import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row312_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 312 =
    (348068583006847139616132997649618783552411053050532011896059122720822895488 : ℤ) := by decide +kernel

private theorem row312_block0 : dottiePairRowBlock dottieFastReferenceWeight 312 0 312 =
    (11481130513026017108177426993150281162766990346380187170701484039461985095568 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 312 0 312).symm.trans (by decide +kernel)

private theorem row312 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 312 1 = (11829199096032864247793559990799899946319401399430719182597543162182807991056 : ℤ) := by
  rw [dottiePairedRowSpan_one, row312_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 312 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 312 % 1024 = 312 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row312_block0]
  decide +kernel

private theorem row313_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 313 =
    (-247942486023442423339894163535240994635361280858613698220167770339806865408 : ℤ) := by decide +kernel

private theorem row313_block0 : dottiePairRowBlock dottieFastReferenceWeight 313 0 313 =
    (-7116709216994355938174297920020400946579553945299724327814936919998617282536 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 313 0 313).symm.trans (by decide +kernel)

private theorem row313 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 313 1 = (-7364651703017798361514192083555641941214915226158338026035104690338424147944 : ℤ) := by
  rw [dottiePairedRowSpan_one, row313_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 313 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 313 % 1024 = 313 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row313_block0]
  decide +kernel

private theorem row314_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 314 =
    (313821407940882756722294458102968800595686177510431003921551919990454899192 : ℤ) := by decide +kernel

private theorem row314_block0 : dottiePairRowBlock dottieFastReferenceWeight 314 0 314 =
    (4899044877464801653425199025327515405425888660089068765198898128200218509368 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 314 0 314).symm.trans (by decide +kernel)

private theorem row314 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 314 1 = (5212866285405684410147493483430484206021574837599499769120450048190673408560 : ℤ) := by
  rw [dottiePairedRowSpan_one, row314_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 314 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 314 % 1024 = 314 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row314_block0]
  decide +kernel

private theorem row315_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 315 =
    (-402670103505123277713686029848343551049342749049625507457078911059618281920 : ℤ) := by decide +kernel

private theorem row315_block0 : dottiePairRowBlock dottieFastReferenceWeight 315 0 315 =
    (-2580916266134945140699088767232054447015290328634037353662450552435177266888 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 315 0 315).symm.trans (by decide +kernel)

private theorem row315 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 315 1 = (-2983586369640068418412774797080397998064633077683662861119529463494795548808 : ℤ) := by
  rw [dottiePairedRowSpan_one, row315_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 315 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 315 % 1024 = 315 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row315_block0]
  decide +kernel

private theorem row316_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 316 =
    (400369673718824225085314468097735883933002053897952671214164410182194470584 : ℤ) := by decide +kernel

private theorem row316_block0 : dottiePairRowBlock dottieFastReferenceWeight 316 0 316 =
    (2956419244197823425858683330013422496910744193706761225715429879457724380440 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 316 0 316).symm.trans (by decide +kernel)

private theorem row316 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 316 1 = (3356788917916647650943997798111158380843746247604713896929594289639918851024 : ℤ) := by
  rw [dottiePairedRowSpan_one, row316_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 316 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 316 % 1024 = 316 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row316_block0]
  decide +kernel

private theorem row317_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 317 =
    (-144132294356820498985153074439672937636565103100707803679429312408806235232 : ℤ) := by decide +kernel

private theorem row317_block0 : dottiePairRowBlock dottieFastReferenceWeight 317 0 317 =
    (-1588470416344067593778305059548168698333277515439242176122277574213794456960 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 317 0 317).symm.trans (by decide +kernel)

private theorem row317 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 317 1 = (-1732602710700888092763458133987841635969842618539949979801706886622600692192 : ℤ) := by
  rw [dottiePairedRowSpan_one, row317_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 317 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 317 % 1024 = 317 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row317_block0]
  decide +kernel

private theorem row318_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 318 =
    (323337402539666876061624413010703293587865334766542749611117000184298267280 : ℤ) := by decide +kernel

private theorem row318_block0 : dottiePairRowBlock dottieFastReferenceWeight 318 0 318 =
    (-6069083637389037898416327748916936271539626629936605367219812999548030408480 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 318 0 318).symm.trans (by decide +kernel)

private theorem row318 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 318 1 = (-5745746234849371022354703335906232977951761295170062617608695999363732141200 : ℤ) := by
  rw [dottiePairedRowSpan_one, row318_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 318 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 318 % 1024 = 318 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row318_block0]
  decide +kernel

private theorem row319_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 319 =
    (-371794139282420810313508846247871460118009266023809640284987632044743821728 : ℤ) := by decide +kernel

private theorem row319_block0 : dottiePairRowBlock dottieFastReferenceWeight 319 0 319 =
    (-18931676398548582355044325463907884484898081167989191380889005025381009039648 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 319 0 319).symm.trans (by decide +kernel)

private theorem row319 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 319 1 = (-19303470537831003165357834310155755945016090434013001021173992657425752861376 : ℤ) := by
  rw [dottiePairedRowSpan_one, row319_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 319 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 319 % 1024 = 319 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row319_block0]
  decide +kernel

private theorem span312_314 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 312 2 = (4464547393015065886279367907244258005104486173272381156562438471844383843112 : ℤ) := by
  calc
    _ = (11829199096032864247793559990799899946319401399430719182597543162182807991056 : ℤ) + (-7364651703017798361514192083555641941214915226158338026035104690338424147944 : ℤ) := by
      simpa only [Nat.reduceAdd, row312, row313] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 312 1 1
    _ = _ := by decide +kernel

private theorem span314_316 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 314 2 = (2229279915765615991734718686350086207956941759915836908000920584695877859752 : ℤ) := by
  calc
    _ = (5212866285405684410147493483430484206021574837599499769120450048190673408560 : ℤ) + (-2983586369640068418412774797080397998064633077683662861119529463494795548808 : ℤ) := by
      simpa only [Nat.reduceAdd, row314, row315] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 314 1 1
    _ = _ := by decide +kernel

private theorem span312_316 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 312 4 = (6693827308780681878014086593594344213061427933188218064563359056540261702864 : ℤ) := by
  calc
    _ = (4464547393015065886279367907244258005104486173272381156562438471844383843112 : ℤ) + (2229279915765615991734718686350086207956941759915836908000920584695877859752 : ℤ) := by
      simpa only [Nat.reduceAdd, span312_314, span314_316] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 312 2 2
    _ = _ := by decide +kernel

private theorem span316_318 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 316 2 = (1624186207215759558180539664123316744873903629064763917127887403017318158832 : ℤ) := by
  calc
    _ = (3356788917916647650943997798111158380843746247604713896929594289639918851024 : ℤ) + (-1732602710700888092763458133987841635969842618539949979801706886622600692192 : ℤ) := by
      simpa only [Nat.reduceAdd, row316, row317] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 316 1 1
    _ = _ := by decide +kernel

private theorem span318_320 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 318 2 = (-25049216772680374187712537646061988922967851729183063638782688656789485002576 : ℤ) := by
  calc
    _ = (-5745746234849371022354703335906232977951761295170062617608695999363732141200 : ℤ) + (-19303470537831003165357834310155755945016090434013001021173992657425752861376 : ℤ) := by
      simpa only [Nat.reduceAdd, row318, row319] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 318 1 1
    _ = _ := by decide +kernel

private theorem span316_320 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 316 4 = (-23425030565464614629531997981938672178093948100118299721654801253772166843744 : ℤ) := by
  calc
    _ = (1624186207215759558180539664123316744873903629064763917127887403017318158832 : ℤ) + (-25049216772680374187712537646061988922967851729183063638782688656789485002576 : ℤ) := by
      simpa only [Nat.reduceAdd, span316_318, span318_320] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 316 2 2
    _ = _ := by decide +kernel

private theorem span312_320 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 312 8 = (-16731203256683932751517911388344327965032520166930081657091442197231905140880 : ℤ) := by
  calc
    _ = (6693827308780681878014086593594344213061427933188218064563359056540261702864 : ℤ) + (-23425030565464614629531997981938672178093948100118299721654801253772166843744 : ℤ) := by
      simpa only [Nat.reduceAdd, span312_316, span316_320] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 312 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows312To320 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 312 8 = (-16731203256683932751517911388344327965032520166930081657091442197231905140880 : ℤ) :=
  span312_320

#print axioms dottieFastReferenceRows312To320

end QuarticModel
