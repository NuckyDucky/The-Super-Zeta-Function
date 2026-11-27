import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row0_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 0 =
    (-13798267819413870767508183097573753406751849294456313260475327754921935473632 : ℤ) := by decide +kernel

private theorem row0_block0 : dottiePairRowBlock dottieFastReferenceWeight 0 0 0 =
    (0 : ℤ) :=
  by decide +kernel

private theorem row0 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 1 = (-13798267819413870767508183097573753406751849294456313260475327754921935473632 : ℤ) := by
  rw [dottiePairedRowSpan_one, row0_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 0 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 0 % 1024 = 0 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row0_block0]
  decide +kernel

private theorem row1_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 1 =
    (-19227362680046444907992586878655659031931995805625150234995272298023537535216 : ℤ) := by decide +kernel

private theorem row1_block0 : dottiePairRowBlock dottieFastReferenceWeight 1 0 1 =
    (-19841789895115503737113643625251251165312892548050131417698935924319073450752 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 1 0 1).symm.trans (by decide +kernel)

private theorem row1 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 1 1 = (-39069152575161948645106230503906910197244888353675281652694208222342610985968 : ℤ) := by
  rw [dottiePairedRowSpan_one, row1_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 1 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 1 % 1024 = 1 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row1_block0]
  decide +kernel

private theorem row2_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 2 =
    (19794731100422852113253759776724326143751004960493397414145343188201683474432 : ℤ) := by decide +kernel

private theorem row2_block0 : dottiePairRowBlock dottieFastReferenceWeight 2 0 2 =
    (-120283923073473751432509134298657215686078660952688308350908953781784948347904 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 2 0 2).symm.trans (by decide +kernel)

private theorem row2 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 2 1 = (-100489191973050899319255374521932889542327655992194910936763610593583264873472 : ℤ) := by
  rw [dottiePairedRowSpan_one, row2_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 2 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 2 % 1024 = 2 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row2_block0]
  decide +kernel

private theorem row3_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 3 =
    (21040623120817012757565578069621853388286570607998908253754733460053174993672 : ℤ) := by decide +kernel

private theorem row3_block0 : dottiePairRowBlock dottieFastReferenceWeight 3 0 3 =
    (72330153448067411468656727962455944527188745843953268739041444414754721867312 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 3 0 3).symm.trans (by decide +kernel)

private theorem row3 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 3 1 = (93370776568884424226222306032077797915475316451952176992796177874807896860984 : ℤ) := by
  rw [dottiePairedRowSpan_one, row3_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 3 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 3 % 1024 = 3 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row3_block0]
  decide +kernel

private theorem row4_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 4 =
    (24428819677352728337430431727029180938999454090509746192546700827508526910440 : ℤ) := by decide +kernel

private theorem row4_block0 : dottiePairRowBlock dottieFastReferenceWeight 4 0 4 =
    (72877607171922795209474043106570321240333658915691059917210762770709850605824 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 4 0 4).symm.trans (by decide +kernel)

private theorem row4 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 4 1 = (97306426849275523546904474833599502179333113006200806109757463598218377516264 : ℤ) := by
  rw [dottiePairedRowSpan_one, row4_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 4 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 4 % 1024 = 4 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row4_block0]
  decide +kernel

private theorem row5_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 5 =
    (-16629468641296640917024072768365383881625572011605677541774451958963688001536 : ℤ) := by decide +kernel

private theorem row5_block0 : dottiePairRowBlock dottieFastReferenceWeight 5 0 5 =
    (61483912020197578829473827681447881708869153290091403742686472716677334756944 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 5 0 5).symm.trans (by decide +kernel)

private theorem row5 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 5 1 = (44854443378900937912449754913082497827243581278485726200912020757713646755408 : ℤ) := by
  rw [dottiePairedRowSpan_one, row5_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 5 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 5 % 1024 = 5 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row5_block0]
  decide +kernel

private theorem row6_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 6 =
    (-14246275123033580404566869369437010668368830692956094079879386299177176069888 : ℤ) := by decide +kernel

private theorem row6_block0 : dottiePairRowBlock dottieFastReferenceWeight 6 0 6 =
    (-8188314729471182597380671243248876927960697422017911855627774971090330621984 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 6 0 6).symm.trans (by decide +kernel)

private theorem row6 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 6 1 = (-22434589852504763001947540612685887596329528114974005935507161270267506691872 : ℤ) := by
  rw [dottiePairedRowSpan_one, row6_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 6 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 6 % 1024 = 6 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row6_block0]
  decide +kernel

private theorem row7_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 7 =
    (-14443162008191668960956126118732423719390205382004812992218220876095023185920 : ℤ) := by decide +kernel

private theorem row7_block0 : dottiePairRowBlock dottieFastReferenceWeight 7 0 7 =
    (-70220278258606357524010095466841952888180245054823131251051863142770021663616 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 7 0 7).symm.trans (by decide +kernel)

private theorem row7 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 7 1 = (-84663440266798026484966221585574376607570450436827944243270084018865044849536 : ℤ) := by
  rw [dottiePairedRowSpan_one, row7_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 7 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 7 % 1024 = 7 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row7_block0]
  decide +kernel

private theorem row8_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 8 =
    (12469027823818718378686885914135090151251102519156698442669765142410625915520 : ℤ) := by decide +kernel

private theorem row8_block0 : dottiePairRowBlock dottieFastReferenceWeight 8 0 8 =
    (-80619171567677677738979471628467181609598681951009867383984760884139710666792 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 8 0 8).symm.trans (by decide +kernel)

private theorem row8 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 8 1 = (-68150143743858959360292585714332091458347579431853168941314995741729084751272 : ℤ) := by
  rw [dottiePairedRowSpan_one, row8_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 8 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 8 % 1024 = 8 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row8_block0]
  decide +kernel

private theorem row9_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 9 =
    (-9730002785566504045708405559823669239842348066251881779546913567551803673552 : ℤ) := by decide +kernel

private theorem row9_block0 : dottiePairRowBlock dottieFastReferenceWeight 9 0 9 =
    (-48953128638191648827327744606669716964872508961939407335976998381547372912232 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 9 0 9).symm.trans (by decide +kernel)

private theorem row9 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 9 1 = (-58683131423758152873036150166493386204714857028191289115523911949099176585784 : ℤ) := by
  rw [dottiePairedRowSpan_one, row9_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 9 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 9 % 1024 = 9 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row9_block0]
  decide +kernel

private theorem row10_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 10 =
    (-11089591341621122572756687764574623730752225940432533611756029626210700646272 : ℤ) := by decide +kernel

private theorem row10_block0 : dottiePairRowBlock dottieFastReferenceWeight 10 0 10 =
    (-40528078399802694175796303536353367436203483140790821311340706076123722802960 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 10 0 10).symm.trans (by decide +kernel)

private theorem row10 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 10 1 = (-51617669741423816748552991300927991166955709081223354923096735702334423449232 : ℤ) := by
  rw [dottiePairedRowSpan_one, row10_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 10 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 10 % 1024 = 10 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row10_block0]
  decide +kernel

private theorem row11_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 11 =
    (10265567964707655945446547191872567136804588722173712177857188769523975174568 : ℤ) := by decide +kernel

private theorem row11_block0 : dottiePairRowBlock dottieFastReferenceWeight 11 0 11 =
    (-34453757738671765259660530889806390628002205338369861672282379631424050267696 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 11 0 11).symm.trans (by decide +kernel)

private theorem row11 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 11 1 = (-24188189773964109314213983697933823491197616616196149494425190861900075093128 : ℤ) := by
  rw [dottiePairedRowSpan_one, row11_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 11 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 11 % 1024 = 11 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row11_block0]
  decide +kernel

private theorem row12_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 12 =
    (-4366493955831551958458026550788433519359058358326482293445387954877622077184 : ℤ) := by decide +kernel

private theorem row12_block0 : dottiePairRowBlock dottieFastReferenceWeight 12 0 12 =
    (25601647769859096899769366800692117202141821883543981955076132683168716518800 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 12 0 12).symm.trans (by decide +kernel)

private theorem row12 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 12 1 = (21235153814027544941311340249903683682782763525217499661630744728291094441616 : ℤ) := by
  rw [dottiePairedRowSpan_one, row12_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 12 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 12 % 1024 = 12 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row12_block0]
  decide +kernel

private theorem row13_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 13 =
    (4236347914190156608083982248563130196187638332459961533176263568106532712648 : ℤ) := by decide +kernel

private theorem row13_block0 : dottiePairRowBlock dottieFastReferenceWeight 13 0 13 =
    (59040218578821781505357958850256999742970211532700589929267870061941090231904 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 13 0 13).symm.trans (by decide +kernel)

private theorem row13 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 13 1 = (63276566493011938113441941098820129939157849865160551462444133630047622944552 : ℤ) := by
  rw [dottiePairedRowSpan_one, row13_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 13 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 13 % 1024 = 13 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row13_block0]
  decide +kernel

private theorem row14_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 14 =
    (5412472163575927850537998544989483374433791193730832881436423355580807570104 : ℤ) := by decide +kernel

private theorem row14_block0 : dottiePairRowBlock dottieFastReferenceWeight 14 0 14 =
    (29656104560024459901702470105274292708454938761010130930284346775540630736848 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 14 0 14).symm.trans (by decide +kernel)

private theorem row14 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 14 1 = (35068576723600387752240468650263776082888729954740963811720770131121438306952 : ℤ) := by
  rw [dottiePairedRowSpan_one, row14_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 14 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 14 % 1024 = 14 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row14_block0]
  decide +kernel

private theorem row15_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 15 =
    (7953849610355466328113070483536312815383097468098941687584461773247146142272 : ℤ) := by decide +kernel

private theorem row15_block0 : dottiePairRowBlock dottieFastReferenceWeight 15 0 15 =
    (48889069469725996297111431365072370155823475932727713829736866573490570476704 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 15 0 15).symm.trans (by decide +kernel)

private theorem row15 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 15 1 = (56842919080081462625224501848608682971206573400826655517321328346737716618976 : ℤ) := by
  rw [dottiePairedRowSpan_one, row15_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 15 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 15 % 1024 = 15 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row15_block0]
  decide +kernel

private theorem row16_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 16 =
    (-300648928718601792839497153369073451384178909906447928098559220797343725784 : ℤ) := by decide +kernel

private theorem row16_block0 : dottiePairRowBlock dottieFastReferenceWeight 16 0 16 =
    (46783770717683207900013276816879776699491667948692687763361117940961054594960 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 16 0 16).symm.trans (by decide +kernel)

private theorem row16 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 16 1 = (46483121788964606107173779663510703248107489038786239835262558720163710869176 : ℤ) := by
  rw [dottiePairedRowSpan_one, row16_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 16 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 16 % 1024 = 16 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row16_block0]
  decide +kernel

private theorem row17_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 17 =
    (-7050818064513762652293245024771262629706987657133020582734106468197349326512 : ℤ) := by decide +kernel

private theorem row17_block0 : dottiePairRowBlock dottieFastReferenceWeight 17 0 17 =
    (36452273915793369539569341766698800405750440932662483018112047634086028703504 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 17 0 17).symm.trans (by decide +kernel)

private theorem row17 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 17 1 = (29401455851279606887276096741927537776043453275529462435377941165888679376992 : ℤ) := by
  rw [dottiePairedRowSpan_one, row17_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 17 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 17 % 1024 = 17 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row17_block0]
  decide +kernel

private theorem row18_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 18 =
    (6107524468653608201753399713923595108408640034999882772963553957332270003112 : ℤ) := by decide +kernel

private theorem row18_block0 : dottiePairRowBlock dottieFastReferenceWeight 18 0 18 =
    (41516374845784603364398694298003243495093199094096702620707476057104246247232 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 18 0 18).symm.trans (by decide +kernel)

private theorem row18 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 18 1 = (47623899314438211566152094011926838603501839129096585393671030014436516250344 : ℤ) := by
  rw [dottiePairedRowSpan_one, row18_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 18 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 18 % 1024 = 18 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row18_block0]
  decide +kernel

private theorem row19_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 19 =
    (2794745303591152355673142716725490367151873046735077286779069080829964560640 : ℤ) := by decide +kernel

private theorem row19_block0 : dottiePairRowBlock dottieFastReferenceWeight 19 0 19 =
    (23350879171750364051135235501801366905906476044930337848347333571624246031552 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 19 0 19).symm.trans (by decide +kernel)

private theorem row19 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 19 1 = (26145624475341516406808378218526857273058349091665415135126402652454210592192 : ℤ) := by
  rw [dottiePairedRowSpan_one, row19_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 19 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 19 % 1024 = 19 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row19_block0]
  decide +kernel

private theorem row20_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 20 =
    (-1827311969969296666976309545829607469679797331845951208561959671877876599168 : ℤ) := by decide +kernel

private theorem row20_block0 : dottiePairRowBlock dottieFastReferenceWeight 20 0 20 =
    (16535868967074189791471865176929182189892876104529957308924289559769801018176 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 20 0 20).symm.trans (by decide +kernel)

private theorem row20 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 20 1 = (14708556997104893124495555631099574720213078772684006100362329887891924419008 : ℤ) := by
  rw [dottiePairedRowSpan_one, row20_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 20 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 20 % 1024 = 20 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row20_block0]
  decide +kernel

private theorem row21_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 21 =
    (4406282819474566062902354726910954403579359964409497576639857852306197161592 : ℤ) := by decide +kernel

private theorem row21_block0 : dottiePairRowBlock dottieFastReferenceWeight 21 0 21 =
    (12580567425814032722232826730395679759581882021555906608031255744623931478032 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 21 0 21).symm.trans (by decide +kernel)

private theorem row21 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 21 1 = (16986850245288598785135181457306634163161241985965404184671113596930128639624 : ℤ) := by
  rw [dottiePairedRowSpan_one, row21_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 21 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 21 % 1024 = 21 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row21_block0]
  decide +kernel

private theorem row22_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 22 =
    (3258568034822565977060584030415514762523266763047588793257111621309871816368 : ℤ) := by decide +kernel

private theorem row22_block0 : dottiePairRowBlock dottieFastReferenceWeight 22 0 22 =
    (35482066964631883252091270321609452126531516004469861944511034286193166786304 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 22 0 22).symm.trans (by decide +kernel)

private theorem row22 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 22 1 = (38740634999454449229151854352024966889054782767517450737768145907503038602672 : ℤ) := by
  rw [dottiePairedRowSpan_one, row22_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 22 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 22 % 1024 = 22 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row22_block0]
  decide +kernel

private theorem row23_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 23 =
    (-5234570030844280586738333975449290817115252454343896086625566443242935353000 : ℤ) := by decide +kernel

private theorem row23_block0 : dottiePairRowBlock dottieFastReferenceWeight 23 0 23 =
    (-18682912482311326910081472658917809447589423625197263875850958795052405390216 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 23 0 23).symm.trans (by decide +kernel)

private theorem row23 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 23 1 = (-23917482513155607496819806634367100264704676079541159962476525238295340743216 : ℤ) := by
  rw [dottiePairedRowSpan_one, row23_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 23 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 23 % 1024 = 23 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row23_block0]
  decide +kernel

private theorem row24_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 24 =
    (-3196337105703831555019391317324555181273577113358696452214566019471080736768 : ℤ) := by decide +kernel

private theorem row24_block0 : dottiePairRowBlock dottieFastReferenceWeight 24 0 24 =
    (-816034504385376729672034490562618914009713720732065545462907703343187257504 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 24 0 24).symm.trans (by decide +kernel)

private theorem row24 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 24 1 = (-4012371610089208284691425807887174095283290834090761997677473722814267994272 : ℤ) := by
  rw [dottiePairedRowSpan_one, row24_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 24 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 24 % 1024 = 24 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row24_block0]
  decide +kernel

private theorem row25_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 25 =
    (228649484502011294735855912528415863343527957276806074691916059772814591304 : ℤ) := by decide +kernel

private theorem row25_block0 : dottiePairRowBlock dottieFastReferenceWeight 25 0 25 =
    (-40040839618182727785998305189344818057778655460331053708894297947432981242896 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 25 0 25).symm.trans (by decide +kernel)

private theorem row25 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 25 1 = (-39812190133680716491262449276816402194435127503054247634202381887660166651592 : ℤ) := by
  rw [dottiePairedRowSpan_one, row25_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 25 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 25 % 1024 = 25 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row25_block0]
  decide +kernel

private theorem row26_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 26 =
    (4689281118431941468489542438928442794060070553616213301060003098120191515128 : ℤ) := by decide +kernel

private theorem row26_block0 : dottiePairRowBlock dottieFastReferenceWeight 26 0 26 =
    (-18354782805263263289045255517326948566519030259392983125535316468352697439088 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 26 0 26).symm.trans (by decide +kernel)

private theorem row26 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 26 1 = (-13665501686831321820555713078398505772458959705776769824475313370232505923960 : ℤ) := by
  rw [dottiePairedRowSpan_one, row26_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 26 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 26 % 1024 = 26 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row26_block0]
  decide +kernel

private theorem row27_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 27 =
    (-314253157865253341069745881816193662546852455523361483895355595568040263168 : ℤ) := by decide +kernel

private theorem row27_block0 : dottiePairRowBlock dottieFastReferenceWeight 27 0 27 =
    (-20607204398697933253449727887073290369716666264422781585755923620851661362896 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 27 0 27).symm.trans (by decide +kernel)

private theorem row27 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 27 1 = (-20921457556563186594519473768889484032263518719946143069651279216419701626064 : ℤ) := by
  rw [dottiePairedRowSpan_one, row27_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 27 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 27 % 1024 = 27 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row27_block0]
  decide +kernel

private theorem row28_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 28 =
    (-991739291097200738115623993236482531506658390558755042094591931109580858928 : ℤ) := by decide +kernel

private theorem row28_block0 : dottiePairRowBlock dottieFastReferenceWeight 28 0 28 =
    (-43114530625244245867775853795121467129620700378349924985260352284646267306096 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 28 0 28).symm.trans (by decide +kernel)

private theorem row28 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 28 1 = (-44106269916341446605891477788357949661127358768908680027354944215755848165024 : ℤ) := by
  rw [dottiePairedRowSpan_one, row28_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 28 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 28 % 1024 = 28 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row28_block0]
  decide +kernel

private theorem row29_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 29 =
    (-1156872749501762578762897183312987755614304900048066402663506156726874766400 : ℤ) := by decide +kernel

private theorem row29_block0 : dottiePairRowBlock dottieFastReferenceWeight 29 0 29 =
    (-39636440306096127094933487495543452359871702892372473573960491174019089891816 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 29 0 29).symm.trans (by decide +kernel)

private theorem row29 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 29 1 = (-40793313055597889673696384678856440115486007792420539976623997330745964658216 : ℤ) := by
  rw [dottiePairedRowSpan_one, row29_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 29 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 29 % 1024 = 29 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row29_block0]
  decide +kernel

private theorem row30_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 30 =
    (432186237013843240165981200777771677870217005306541593069736499429485379712 : ℤ) := by decide +kernel

private theorem row30_block0 : dottiePairRowBlock dottieFastReferenceWeight 30 0 30 =
    (-46944302115924231878927585272843917046007978020457374813980999628172400589968 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 30 0 30).symm.trans (by decide +kernel)

private theorem row30 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 30 1 = (-46512115878910388638761604072066145368137761015150833220911263128742915210256 : ℤ) := by
  rw [dottiePairedRowSpan_one, row30_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 30 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 30 % 1024 = 30 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row30_block0]
  decide +kernel

private theorem row31_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 31 =
    (-3666162534093676427882766267745849665849973953275219915438229137204936748768 : ℤ) := by decide +kernel

private theorem row31_block0 : dottiePairRowBlock dottieFastReferenceWeight 31 0 31 =
    (-31183057772482480636960533703760454392149848023507400433603998080153381657984 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 31 0 31).symm.trans (by decide +kernel)

private theorem row31 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 31 1 = (-34849220306576157064843299971506304057999821976782620349042227217358318406752 : ℤ) := by
  rw [dottiePairedRowSpan_one, row31_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 31 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 31 % 1024 = 31 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row31_block0]
  decide +kernel

private theorem span0_2 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 2 = (-52867420394575819412614413601480663603996737648131594913169535977264546459600 : ℤ) := by
  calc
    _ = (-13798267819413870767508183097573753406751849294456313260475327754921935473632 : ℤ) + (-39069152575161948645106230503906910197244888353675281652694208222342610985968 : ℤ) := by
      simpa only [Nat.reduceAdd, row0, row1] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 1 1
    _ = _ := by decide +kernel

private theorem span2_4 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 2 2 = (-7118415404166475093033068489855091626852339540242733943967432718775368012488 : ℤ) := by
  calc
    _ = (-100489191973050899319255374521932889542327655992194910936763610593583264873472 : ℤ) + (93370776568884424226222306032077797915475316451952176992796177874807896860984 : ℤ) := by
      simpa only [Nat.reduceAdd, row2, row3] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 2 1 1
    _ = _ := by decide +kernel

private theorem span0_4 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 4 = (-59985835798742294505647482091335755230849077188374328857136968696039914472088 : ℤ) := by
  calc
    _ = (-52867420394575819412614413601480663603996737648131594913169535977264546459600 : ℤ) + (-7118415404166475093033068489855091626852339540242733943967432718775368012488 : ℤ) := by
      simpa only [Nat.reduceAdd, span0_2, span2_4] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 2 2
    _ = _ := by decide +kernel

private theorem span4_6 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 4 2 = (142160870228176461459354229746682000006576694284686532310669484355932024271672 : ℤ) := by
  calc
    _ = (97306426849275523546904474833599502179333113006200806109757463598218377516264 : ℤ) + (44854443378900937912449754913082497827243581278485726200912020757713646755408 : ℤ) := by
      simpa only [Nat.reduceAdd, row4, row5] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 4 1 1
    _ = _ := by decide +kernel

private theorem span6_8 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 6 2 = (-107098030119302789486913762198260264203899978551801950178777245289132551541408 : ℤ) := by
  calc
    _ = (-22434589852504763001947540612685887596329528114974005935507161270267506691872 : ℤ) + (-84663440266798026484966221585574376607570450436827944243270084018865044849536 : ℤ) := by
      simpa only [Nat.reduceAdd, row6, row7] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 6 1 1
    _ = _ := by decide +kernel

private theorem span4_8 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 4 4 = (35062840108873671972440467548421735802676715732884582131892239066799472730264 : ℤ) := by
  calc
    _ = (142160870228176461459354229746682000006576694284686532310669484355932024271672 : ℤ) + (-107098030119302789486913762198260264203899978551801950178777245289132551541408 : ℤ) := by
      simpa only [Nat.reduceAdd, span4_6, span6_8] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 4 2 2
    _ = _ := by decide +kernel

private theorem span0_8 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 8 = (-24922995689868622533207014542914019428172361455489746725244729629240441741824 : ℤ) := by
  calc
    _ = (-59985835798742294505647482091335755230849077188374328857136968696039914472088 : ℤ) + (35062840108873671972440467548421735802676715732884582131892239066799472730264 : ℤ) := by
      simpa only [Nat.reduceAdd, span0_4, span4_8] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 4 4
    _ = _ := by decide +kernel

private theorem span8_10 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 8 2 = (-126833275167617112233328735880825477663062436460044458056838907690828261337056 : ℤ) := by
  calc
    _ = (-68150143743858959360292585714332091458347579431853168941314995741729084751272 : ℤ) + (-58683131423758152873036150166493386204714857028191289115523911949099176585784 : ℤ) := by
      simpa only [Nat.reduceAdd, row8, row9] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 8 1 1
    _ = _ := by decide +kernel

private theorem span10_12 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 10 2 = (-75805859515387926062766974998861814658153325697419504417521926564234498542360 : ℤ) := by
  calc
    _ = (-51617669741423816748552991300927991166955709081223354923096735702334423449232 : ℤ) + (-24188189773964109314213983697933823491197616616196149494425190861900075093128 : ℤ) := by
      simpa only [Nat.reduceAdd, row10, row11] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 10 1 1
    _ = _ := by decide +kernel

private theorem span8_12 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 8 4 = (-202639134683005038296095710879687292321215762157463962474360834255062759879416 : ℤ) := by
  calc
    _ = (-126833275167617112233328735880825477663062436460044458056838907690828261337056 : ℤ) + (-75805859515387926062766974998861814658153325697419504417521926564234498542360 : ℤ) := by
      simpa only [Nat.reduceAdd, span8_10, span10_12] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 8 2 2
    _ = _ := by decide +kernel

private theorem span12_14 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 12 2 = (84511720307039483054753281348723813621940613390378051124074878358338717386168 : ℤ) := by
  calc
    _ = (21235153814027544941311340249903683682782763525217499661630744728291094441616 : ℤ) + (63276566493011938113441941098820129939157849865160551462444133630047622944552 : ℤ) := by
      simpa only [Nat.reduceAdd, row12, row13] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 12 1 1
    _ = _ := by decide +kernel

private theorem span14_16 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 14 2 = (91911495803681850377464970498872459054095303355567619329042098477859154925928 : ℤ) := by
  calc
    _ = (35068576723600387752240468650263776082888729954740963811720770131121438306952 : ℤ) + (56842919080081462625224501848608682971206573400826655517321328346737716618976 : ℤ) := by
      simpa only [Nat.reduceAdd, row14, row15] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 14 1 1
    _ = _ := by decide +kernel

private theorem span12_16 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 12 4 = (176423216110721333432218251847596272676035916745945670453116976836197872312096 : ℤ) := by
  calc
    _ = (84511720307039483054753281348723813621940613390378051124074878358338717386168 : ℤ) + (91911495803681850377464970498872459054095303355567619329042098477859154925928 : ℤ) := by
      simpa only [Nat.reduceAdd, span12_14, span14_16] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 12 2 2
    _ = _ := by decide +kernel

private theorem span8_16 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 8 8 = (-26215918572283704863877459032091019645179845411518292021243857418864887567320 : ℤ) := by
  calc
    _ = (-202639134683005038296095710879687292321215762157463962474360834255062759879416 : ℤ) + (176423216110721333432218251847596272676035916745945670453116976836197872312096 : ℤ) := by
      simpa only [Nat.reduceAdd, span8_12, span12_16] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 8 4 4
    _ = _ := by decide +kernel

private theorem span0_16 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 16 = (-51138914262152327397084473575005039073352206867008038746488587048105329309144 : ℤ) := by
  calc
    _ = (-24922995689868622533207014542914019428172361455489746725244729629240441741824 : ℤ) + (-26215918572283704863877459032091019645179845411518292021243857418864887567320 : ℤ) := by
      simpa only [Nat.reduceAdd, span0_8, span8_16] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 8 8
    _ = _ := by decide +kernel

private theorem span16_18 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 16 2 = (75884577640244212994449876405438241024150942314315702270640499886052390246168 : ℤ) := by
  calc
    _ = (46483121788964606107173779663510703248107489038786239835262558720163710869176 : ℤ) + (29401455851279606887276096741927537776043453275529462435377941165888679376992 : ℤ) := by
      simpa only [Nat.reduceAdd, row16, row17] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 16 1 1
    _ = _ := by decide +kernel

private theorem span18_20 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 18 2 = (73769523789779727972960472230453695876560188220762000528797432666890726842536 : ℤ) := by
  calc
    _ = (47623899314438211566152094011926838603501839129096585393671030014436516250344 : ℤ) + (26145624475341516406808378218526857273058349091665415135126402652454210592192 : ℤ) := by
      simpa only [Nat.reduceAdd, row18, row19] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 18 1 1
    _ = _ := by decide +kernel

private theorem span16_20 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 16 4 = (149654101430023940967410348635891936900711130535077702799437932552943117088704 : ℤ) := by
  calc
    _ = (75884577640244212994449876405438241024150942314315702270640499886052390246168 : ℤ) + (73769523789779727972960472230453695876560188220762000528797432666890726842536 : ℤ) := by
      simpa only [Nat.reduceAdd, span16_18, span18_20] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 16 2 2
    _ = _ := by decide +kernel

private theorem span20_22 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 20 2 = (31695407242393491909630737088406208883374320758649410285033443484822053058632 : ℤ) := by
  calc
    _ = (14708556997104893124495555631099574720213078772684006100362329887891924419008 : ℤ) + (16986850245288598785135181457306634163161241985965404184671113596930128639624 : ℤ) := by
      simpa only [Nat.reduceAdd, row20, row21] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 20 1 1
    _ = _ := by decide +kernel

private theorem span22_24 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 22 2 = (14823152486298841732332047717657866624350106687976290775291620669207697859456 : ℤ) := by
  calc
    _ = (38740634999454449229151854352024966889054782767517450737768145907503038602672 : ℤ) + (-23917482513155607496819806634367100264704676079541159962476525238295340743216 : ℤ) := by
      simpa only [Nat.reduceAdd, row22, row23] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 22 1 1
    _ = _ := by decide +kernel

private theorem span20_24 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 20 4 = (46518559728692333641962784806064075507724427446625701060325064154029750918088 : ℤ) := by
  calc
    _ = (31695407242393491909630737088406208883374320758649410285033443484822053058632 : ℤ) + (14823152486298841732332047717657866624350106687976290775291620669207697859456 : ℤ) := by
      simpa only [Nat.reduceAdd, span20_22, span22_24] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 20 2 2
    _ = _ := by decide +kernel

private theorem span16_24 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 16 8 = (196172661158716274609373133441956012408435557981703403859762996706972868006792 : ℤ) := by
  calc
    _ = (149654101430023940967410348635891936900711130535077702799437932552943117088704 : ℤ) + (46518559728692333641962784806064075507724427446625701060325064154029750918088 : ℤ) := by
      simpa only [Nat.reduceAdd, span16_20, span20_24] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 16 4 4
    _ = _ := by decide +kernel

private theorem span24_26 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 24 2 = (-43824561743769924775953875084703576289718418337145009631879855610474434645864 : ℤ) := by
  calc
    _ = (-4012371610089208284691425807887174095283290834090761997677473722814267994272 : ℤ) + (-39812190133680716491262449276816402194435127503054247634202381887660166651592 : ℤ) := by
      simpa only [Nat.reduceAdd, row24, row25] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 24 1 1
    _ = _ := by decide +kernel

private theorem span26_28 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 26 2 = (-34586959243394508415075186847287989804722478425722912894126592586652207550024 : ℤ) := by
  calc
    _ = (-13665501686831321820555713078398505772458959705776769824475313370232505923960 : ℤ) + (-20921457556563186594519473768889484032263518719946143069651279216419701626064 : ℤ) := by
      simpa only [Nat.reduceAdd, row26, row27] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 26 1 1
    _ = _ := by decide +kernel

private theorem span24_28 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 24 4 = (-78411520987164433191029061931991566094440896762867922526006448197126642195888 : ℤ) := by
  calc
    _ = (-43824561743769924775953875084703576289718418337145009631879855610474434645864 : ℤ) + (-34586959243394508415075186847287989804722478425722912894126592586652207550024 : ℤ) := by
      simpa only [Nat.reduceAdd, span24_26, span26_28] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 24 2 2
    _ = _ := by decide +kernel

private theorem span28_30 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 28 2 = (-84899582971939336279587862467214389776613366561329220003978941546501812823240 : ℤ) := by
  calc
    _ = (-44106269916341446605891477788357949661127358768908680027354944215755848165024 : ℤ) + (-40793313055597889673696384678856440115486007792420539976623997330745964658216 : ℤ) := by
      simpa only [Nat.reduceAdd, row28, row29] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 28 1 1
    _ = _ := by decide +kernel

private theorem span30_32 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 30 2 = (-81361336185486545703604904043572449426137582991933453569953490346101233617008 : ℤ) := by
  calc
    _ = (-46512115878910388638761604072066145368137761015150833220911263128742915210256 : ℤ) + (-34849220306576157064843299971506304057999821976782620349042227217358318406752 : ℤ) := by
      simpa only [Nat.reduceAdd, row30, row31] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 30 1 1
    _ = _ := by decide +kernel

private theorem span28_32 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 28 4 = (-166260919157425881983192766510786839202750949553262673573932431892603046440248 : ℤ) := by
  calc
    _ = (-84899582971939336279587862467214389776613366561329220003978941546501812823240 : ℤ) + (-81361336185486545703604904043572449426137582991933453569953490346101233617008 : ℤ) := by
      simpa only [Nat.reduceAdd, span28_30, span30_32] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 28 2 2
    _ = _ := by decide +kernel

private theorem span24_32 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 24 8 = (-244672440144590315174221828442778405297191846316130596099938880089729688636136 : ℤ) := by
  calc
    _ = (-78411520987164433191029061931991566094440896762867922526006448197126642195888 : ℤ) + (-166260919157425881983192766510786839202750949553262673573932431892603046440248 : ℤ) := by
      simpa only [Nat.reduceAdd, span24_28, span28_32] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 24 4 4
    _ = _ := by decide +kernel

private theorem span16_32 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 16 16 = (-48499778985874040564848695000822392888756288334427192240175883382756820629344 : ℤ) := by
  calc
    _ = (196172661158716274609373133441956012408435557981703403859762996706972868006792 : ℤ) + (-244672440144590315174221828442778405297191846316130596099938880089729688636136 : ℤ) := by
      simpa only [Nat.reduceAdd, span16_24, span24_32] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 16 8 8
    _ = _ := by decide +kernel

private theorem span0_32 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 32 = (-99638693248026367961933168575827431962108495201435230986664470430862149938488 : ℤ) := by
  calc
    _ = (-51138914262152327397084473575005039073352206867008038746488587048105329309144 : ℤ) + (-48499778985874040564848695000822392888756288334427192240175883382756820629344 : ℤ) := by
      simpa only [Nat.reduceAdd, span0_16, span16_32] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 0 16 16
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows0To32 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 0 32 = (-99638693248026367961933168575827431962108495201435230986664470430862149938488 : ℤ) :=
  span0_32

#print axioms dottieFastReferenceRows0To32

end QuarticModel
