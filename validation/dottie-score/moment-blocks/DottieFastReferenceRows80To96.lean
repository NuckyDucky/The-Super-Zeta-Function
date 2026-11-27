import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row80_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 80 =
    (1205213986584846153265331653551022619745779041079760873287328092934864157824 : ℤ) := by decide +kernel

private theorem row80_block0 : dottiePairRowBlock dottieFastReferenceWeight 80 0 80 =
    (8487386495283682855102925152516268188837796962623966452367850257138827803032 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 80 0 80).symm.trans (by decide +kernel)

private theorem row80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 80 1 = (9692600481868529008368256806067290808583576003703727325655178350073691960856 : ℤ) := by
  rw [dottiePairedRowSpan_one, row80_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 80 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 80 % 1024 = 80 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row80_block0]
  decide +kernel

private theorem row81_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 81 =
    (0 : ℤ) := by decide +kernel

private theorem row81_block0 : dottiePairRowBlock dottieFastReferenceWeight 81 0 81 =
    (-4286427075344578381466949299596444518342222316586576111161736222002546702160 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 81 0 81).symm.trans (by decide +kernel)

private theorem row81 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 81 1 = (-4286427075344578381466949299596444518342222316586576111161736222002546702160 : ℤ) := by
  rw [dottiePairedRowSpan_one, row81_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 81 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 81 % 1024 = 81 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row81_block0]
  decide +kernel

private theorem row82_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 82 =
    (1487986811724700628765991541741992970308875090588317870598085724748632941408 : ℤ) := by decide +kernel

private theorem row82_block0 : dottiePairRowBlock dottieFastReferenceWeight 82 0 82 =
    (13553484936120720114323183173370580592505029469095281054323300489896825703440 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 82 0 82).symm.trans (by decide +kernel)

private theorem row82 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 82 1 = (15041471747845420743089174715112573562813904559683598924921386214645458644848 : ℤ) := by
  rw [dottiePairedRowSpan_one, row82_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 82 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 82 % 1024 = 82 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row82_block0]
  decide +kernel

private theorem row83_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 83 =
    (759242993077079028685225173184269561331219985214923246213225665446628194992 : ℤ) := by decide +kernel

private theorem row83_block0 : dottiePairRowBlock dottieFastReferenceWeight 83 0 83 =
    (-16844057704427717342422597879353367792342135488517773607922393805804661384248 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 83 0 83).symm.trans (by decide +kernel)

private theorem row83 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 83 1 = (-16084814711350638313737372706169098231010915503302850361709168140358033189256 : ℤ) := by
  rw [dottiePairedRowSpan_one, row83_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 83 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 83 % 1024 = 83 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row83_block0]
  decide +kernel

private theorem row84_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 84 =
    (-1358689532589516855410265258009252816003399067234965209599540504099534800640 : ℤ) := by decide +kernel

private theorem row84_block0 : dottiePairRowBlock dottieFastReferenceWeight 84 0 84 =
    (7082123585813562723484702374678859085849657831708677030513562940444655959280 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 84 0 84).symm.trans (by decide +kernel)

private theorem row84 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 84 1 = (5723434053224045868074437116669606269846258764473711820914022436345121158640 : ℤ) := by
  rw [dottiePairedRowSpan_one, row84_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 84 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 84 % 1024 = 84 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row84_block0]
  decide +kernel

private theorem row85_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 85 =
    (-304214503172727552980301624403535554756476275801860095148802030490901625512 : ℤ) := by decide +kernel

private theorem row85_block0 : dottiePairRowBlock dottieFastReferenceWeight 85 0 85 =
    (-4009248383494554715100898900965872131802585815893726443273822000195203935992 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 85 0 85).symm.trans (by decide +kernel)

private theorem row85 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 85 1 = (-4313462886667282268081200525369407686559062091695586538422624030686105561504 : ℤ) := by
  rw [dottiePairedRowSpan_one, row85_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 85 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 85 % 1024 = 85 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row85_block0]
  decide +kernel

private theorem row86_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 86 =
    (-1071607065304550231011917595838887489319246151105898738478574937837532793616 : ℤ) := by decide +kernel

private theorem row86_block0 : dottiePairRowBlock dottieFastReferenceWeight 86 0 86 =
    (-8118998047654531313828501967215065420338758203791298435065996904748144564448 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 86 0 86).symm.trans (by decide +kernel)

private theorem row86 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 86 1 = (-9190605112959081544840419563053952909658004354897197173544571842585677358064 : ℤ) := by
  rw [dottiePairedRowSpan_one, row86_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 86 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 86 % 1024 = 86 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row86_block0]
  decide +kernel

private theorem row87_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 87 =
    (50190399034036562270663803534356363076041442403757818521474411687386447104 : ℤ) := by decide +kernel

private theorem row87_block0 : dottiePairRowBlock dottieFastReferenceWeight 87 0 87 =
    (-2996013503088045682190674737299518259029544074688184077691688462831926135880 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 87 0 87).symm.trans (by decide +kernel)

private theorem row87 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 87 1 = (-2945823104054009119920010933765161895953502632284426259170214051144539688776 : ℤ) := by
  rw [dottiePairedRowSpan_one, row87_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 87 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 87 % 1024 = 87 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row87_block0]
  decide +kernel

private theorem row88_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 88 =
    (-1391195154921570701267731713713902583812197995443557466728946503830437648384 : ℤ) := by decide +kernel

private theorem row88_block0 : dottiePairRowBlock dottieFastReferenceWeight 88 0 88 =
    (2222383378396487501047022941020653894733874476495215576205616203528689794384 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 88 0 88).symm.trans (by decide +kernel)

private theorem row88 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 88 1 = (831188223474916799779291227306751310921676481051658109476669699698252146000 : ℤ) := by
  rw [dottiePairedRowSpan_one, row88_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 88 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 88 % 1024 = 88 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row88_block0]
  decide +kernel

private theorem row89_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 89 =
    (441980252546418876382820099411426804200414645757435506027543731797469063536 : ℤ) := by decide +kernel

private theorem row89_block0 : dottiePairRowBlock dottieFastReferenceWeight 89 0 89 =
    (-21467784471059459266489841854756205131844309451068228322226990724834362198096 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 89 0 89).symm.trans (by decide +kernel)

private theorem row89 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 89 1 = (-21025804218513040390107021755344778327643894805310792816199446993036893134560 : ℤ) := by
  rw [dottiePairedRowSpan_one, row89_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 89 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 89 % 1024 = 89 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row89_block0]
  decide +kernel

private theorem row90_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 90 =
    (-1329051014900769765065118614002227414221069865825802587020148145426039731712 : ℤ) := by decide +kernel

private theorem row90_block0 : dottiePairRowBlock dottieFastReferenceWeight 90 0 90 =
    (-6095613341945852512633795189036105053046694045886416461962046729798631725040 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 90 0 90).symm.trans (by decide +kernel)

private theorem row90 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 90 1 = (-7424664356846622277698913803038332467267763911712219048982194875224671456752 : ℤ) := by
  rw [dottiePairedRowSpan_one, row90_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 90 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 90 % 1024 = 90 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row90_block0]
  decide +kernel

private theorem row91_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 91 =
    (-276851621218876078890597080306531881533253433098701378781461026716988862640 : ℤ) := by decide +kernel

private theorem row91_block0 : dottiePairRowBlock dottieFastReferenceWeight 91 0 91 =
    (5235641988094895667863729412751519338215113739745804014557065170299203785264 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 91 0 91).symm.trans (by decide +kernel)

private theorem row91 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 91 1 = (4958790366876019588973132332444987456681860306647102635775604143582214922624 : ℤ) := by
  rw [dottiePairedRowSpan_one, row91_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 91 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 91 % 1024 = 91 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row91_block0]
  decide +kernel

private theorem row92_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 92 =
    (-642367391102375366297903839870168880458568364528221653188764361629174480328 : ℤ) := by decide +kernel

private theorem row92_block0 : dottiePairRowBlock dottieFastReferenceWeight 92 0 92 =
    (-16596363263523976569751834685902627018162958840802330315572467614116666714080 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 92 0 92).symm.trans (by decide +kernel)

private theorem row92 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 92 1 = (-17238730654626351936049738525772795898621527205330551968761231975745841194408 : ℤ) := by
  rw [dottiePairedRowSpan_one, row92_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 92 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 92 % 1024 = 92 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row92_block0]
  decide +kernel

private theorem row93_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 93 =
    (1099608210439510669296330079307558394038837661132609952968507664632698704384 : ℤ) := by decide +kernel

private theorem row93_block0 : dottiePairRowBlock dottieFastReferenceWeight 93 0 93 =
    (5569974945572785060429466541641993396011475756440962250603192717706252445024 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 93 0 93).symm.trans (by decide +kernel)

private theorem row93 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 93 1 = (6669583156012295729725796620949551790050313417573572203571700382338951149408 : ℤ) := by
  rw [dottiePairedRowSpan_one, row93_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 93 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 93 % 1024 = 93 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row93_block0]
  decide +kernel

private theorem row94_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 94 =
    (-976884362441024463197000394349124009316120443805237596353581805188272369152 : ℤ) := by decide +kernel

private theorem row94_block0 : dottiePairRowBlock dottieFastReferenceWeight 94 0 94 =
    (-6153211599513495107350863461867288186705308908588060197624677553594457888840 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 94 0 94).symm.trans (by decide +kernel)

private theorem row94 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 94 1 = (-7130095961954519570547863856216412196021429352393297793978259358782730257992 : ℤ) := by
  rw [dottiePairedRowSpan_one, row94_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 94 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 94 % 1024 = 94 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row94_block0]
  decide +kernel

private theorem row95_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 95 =
    (-724899346540356318859545598404995173631959648380617250853320341773097229568 : ℤ) := by decide +kernel

private theorem row95_block0 : dottiePairRowBlock dottieFastReferenceWeight 95 0 95 =
    (-28650255553333241262472097501661150038903555246672014778266285156656199444184 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 95 0 95).symm.trans (by decide +kernel)

private theorem row95 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 95 1 = (-29375154899873597581331643100066145212535514895052632029119605498429296673752 : ℤ) := by
  rw [dottiePairedRowSpan_one, row95_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 95 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 95 % 1024 = 95 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row95_block0]
  decide +kernel

private theorem span80_82 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 80 2 = (5406173406523950626901307506470846290241353687117151214493442128071145258696 : ℤ) := by
  calc
    _ = (9692600481868529008368256806067290808583576003703727325655178350073691960856 : ℤ) + (-4286427075344578381466949299596444518342222316586576111161736222002546702160 : ℤ) := by
      simpa only [Nat.reduceAdd, row80, row81] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 80 1 1
    _ = _ := by decide +kernel

private theorem span82_84 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 82 2 = (-1043342963505217570648197991056524668197010943619251436787781925712574544408 : ℤ) := by
  calc
    _ = (15041471747845420743089174715112573562813904559683598924921386214645458644848 : ℤ) + (-16084814711350638313737372706169098231010915503302850361709168140358033189256 : ℤ) := by
      simpa only [Nat.reduceAdd, row82, row83] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 82 1 1
    _ = _ := by decide +kernel

private theorem span80_84 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 80 4 = (4362830443018733056253109515414321622044342743497899777705660202358570714288 : ℤ) := by
  calc
    _ = (5406173406523950626901307506470846290241353687117151214493442128071145258696 : ℤ) + (-1043342963505217570648197991056524668197010943619251436787781925712574544408 : ℤ) := by
      simpa only [Nat.reduceAdd, span80_82, span82_84] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 80 2 2
    _ = _ := by decide +kernel

private theorem span84_86 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 84 2 = (1409971166556763599993236591300198583287196672778125282491398405659015597136 : ℤ) := by
  calc
    _ = (5723434053224045868074437116669606269846258764473711820914022436345121158640 : ℤ) + (-4313462886667282268081200525369407686559062091695586538422624030686105561504 : ℤ) := by
      simpa only [Nat.reduceAdd, row84, row85] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 84 1 1
    _ = _ := by decide +kernel

private theorem span86_88 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 86 2 = (-12136428217013090664760430496819114805611506987181623432714785893730217046840 : ℤ) := by
  calc
    _ = (-9190605112959081544840419563053952909658004354897197173544571842585677358064 : ℤ) + (-2945823104054009119920010933765161895953502632284426259170214051144539688776 : ℤ) := by
      simpa only [Nat.reduceAdd, row86, row87] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 86 1 1
    _ = _ := by decide +kernel

private theorem span84_88 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 84 4 = (-10726457050456327064767193905518916222324310314403498150223387488071201449704 : ℤ) := by
  calc
    _ = (1409971166556763599993236591300198583287196672778125282491398405659015597136 : ℤ) + (-12136428217013090664760430496819114805611506987181623432714785893730217046840 : ℤ) := by
      simpa only [Nat.reduceAdd, span84_86, span86_88] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 84 2 2
    _ = _ := by decide +kernel

private theorem span80_88 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 80 8 = (-6363626607437594008514084390104594600279967570905598372517727285712630735416 : ℤ) := by
  calc
    _ = (4362830443018733056253109515414321622044342743497899777705660202358570714288 : ℤ) + (-10726457050456327064767193905518916222324310314403498150223387488071201449704 : ℤ) := by
      simpa only [Nat.reduceAdd, span80_84, span84_88] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 80 4 4
    _ = _ := by decide +kernel

private theorem span88_90 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 88 2 = (-20194615995038123590327730528038027016722218324259134706722777293338640988560 : ℤ) := by
  calc
    _ = (831188223474916799779291227306751310921676481051658109476669699698252146000 : ℤ) + (-21025804218513040390107021755344778327643894805310792816199446993036893134560 : ℤ) := by
      simpa only [Nat.reduceAdd, row88, row89] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 88 1 1
    _ = _ := by decide +kernel

private theorem span90_92 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 90 2 = (-2465873989970602688725781470593345010585903605065116413206590731642456534128 : ℤ) := by
  calc
    _ = (-7424664356846622277698913803038332467267763911712219048982194875224671456752 : ℤ) + (4958790366876019588973132332444987456681860306647102635775604143582214922624 : ℤ) := by
      simpa only [Nat.reduceAdd, row90, row91] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 90 1 1
    _ = _ := by decide +kernel

private theorem span88_92 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 88 4 = (-22660489985008726279053511998631372027308121929324251119929368024981097522688 : ℤ) := by
  calc
    _ = (-20194615995038123590327730528038027016722218324259134706722777293338640988560 : ℤ) + (-2465873989970602688725781470593345010585903605065116413206590731642456534128 : ℤ) := by
      simpa only [Nat.reduceAdd, span88_90, span90_92] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 88 2 2
    _ = _ := by decide +kernel

private theorem span92_94 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 92 2 = (-10569147498614056206323941904823244108571213787756979765189531593406890045000 : ℤ) := by
  calc
    _ = (-17238730654626351936049738525772795898621527205330551968761231975745841194408 : ℤ) + (6669583156012295729725796620949551790050313417573572203571700382338951149408 : ℤ) := by
      simpa only [Nat.reduceAdd, row92, row93] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 92 1 1
    _ = _ := by decide +kernel

private theorem span94_96 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 94 2 = (-36505250861828117151879506956282557408556944247445929823097864857212026931744 : ℤ) := by
  calc
    _ = (-7130095961954519570547863856216412196021429352393297793978259358782730257992 : ℤ) + (-29375154899873597581331643100066145212535514895052632029119605498429296673752 : ℤ) := by
      simpa only [Nat.reduceAdd, row94, row95] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 94 1 1
    _ = _ := by decide +kernel

private theorem span92_96 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 92 4 = (-47074398360442173358203448861105801517128158035202909588287396450618916976744 : ℤ) := by
  calc
    _ = (-10569147498614056206323941904823244108571213787756979765189531593406890045000 : ℤ) + (-36505250861828117151879506956282557408556944247445929823097864857212026931744 : ℤ) := by
      simpa only [Nat.reduceAdd, span92_94, span94_96] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 92 2 2
    _ = _ := by decide +kernel

private theorem span88_96 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 88 8 = (-69734888345450899637256960859737173544436279964527160708216764475600014499432 : ℤ) := by
  calc
    _ = (-22660489985008726279053511998631372027308121929324251119929368024981097522688 : ℤ) + (-47074398360442173358203448861105801517128158035202909588287396450618916976744 : ℤ) := by
      simpa only [Nat.reduceAdd, span88_92, span92_96] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 88 4 4
    _ = _ := by decide +kernel

private theorem span80_96 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 80 16 = (-76098514952888493645771045249841768144716247535432759080734491761312645234848 : ℤ) := by
  calc
    _ = (-6363626607437594008514084390104594600279967570905598372517727285712630735416 : ℤ) + (-69734888345450899637256960859737173544436279964527160708216764475600014499432 : ℤ) := by
      simpa only [Nat.reduceAdd, span80_88, span88_96] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 80 8 8
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows80To96 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 80 16 = (-76098514952888493645771045249841768144716247535432759080734491761312645234848 : ℤ) :=
  span80_96

#print axioms dottieFastReferenceRows80To96

end QuarticModel
