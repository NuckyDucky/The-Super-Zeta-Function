import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row32_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 32 =
    (-2447127191937129813441736933191331509772148998577907223560984711510142338424 : ℤ) := by decide +kernel

private theorem row32_block0 : dottiePairRowBlock dottieFastReferenceWeight 32 0 32 =
    (-29147940013004269046981497855836431223784182089365508638024871334950542246112 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 32 0 32).symm.trans (by decide +kernel)

private theorem row32 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 32 1 = (-31595067204941398860423234789027762733556331087943415861585856046460684584536 : ℤ) := by
  rw [dottiePairedRowSpan_one, row32_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 32 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 32 % 1024 = 32 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row32_block0]
  decide +kernel

private theorem row33_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 33 =
    (1647534228324912036572627888555779009577625333768067707682101183853623913600 : ℤ) := by decide +kernel

private theorem row33_block0 : dottiePairRowBlock dottieFastReferenceWeight 33 0 33 =
    (-32317038062537892247401132500184303585484623058845490591532310759740163112168 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 33 0 33).symm.trans (by decide +kernel)

private theorem row33 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 33 1 = (-30669503834212980210828504611628524575906997725077422883850209575886539198568 : ℤ) := by
  rw [dottiePairedRowSpan_one, row33_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 33 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 33 % 1024 = 33 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row33_block0]
  decide +kernel

private theorem row34_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 34 =
    (3179841313731398010657119969155210774664223651978521380710662104216592509568 : ℤ) := by decide +kernel

private theorem row34_block0 : dottiePairRowBlock dottieFastReferenceWeight 34 0 34 =
    (-4131935085471283548589381725570634797477621284594049127459738471083444129536 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 34 0 34).symm.trans (by decide +kernel)

private theorem row34 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 34 1 = (-952093771739885537932261756415424022813397632615527746749076366866851619968 : ℤ) := by
  rw [dottiePairedRowSpan_one, row34_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 34 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 34 % 1024 = 34 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row34_block0]
  decide +kernel

private theorem row35_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 35 =
    (3333515240569673939719109465435720322351487518048448498416889666033173509632 : ℤ) := by decide +kernel

private theorem row35_block0 : dottiePairRowBlock dottieFastReferenceWeight 35 0 35 =
    (-19481113261525640213469831244693602119529504919251729077739920657310549536032 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 35 0 35).symm.trans (by decide +kernel)

private theorem row35 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 35 1 = (-16147598020955966273750721779257881797178017401203280579323030991277376026400 : ℤ) := by
  rw [dottiePairedRowSpan_one, row35_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 35 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 35 % 1024 = 35 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row35_block0]
  decide +kernel

private theorem row36_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 36 =
    (1797616789179624989828835177244109903614276740473784433982467726048520927872 : ℤ) := by decide +kernel

private theorem row36_block0 : dottiePairRowBlock dottieFastReferenceWeight 36 0 36 =
    (-26275049998082777545422508361942096193085314629393484005181765871851112098896 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 36 0 36).symm.trans (by decide +kernel)

private theorem row36 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 36 1 = (-24477433208903152555593673184697986289471037888919699571199298145802591171024 : ℤ) := by
  rw [dottiePairedRowSpan_one, row36_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 36 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 36 % 1024 = 36 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row36_block0]
  decide +kernel

private theorem row37_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 37 =
    (-2238370999322722337197650093901952219666453483349310041841195879895779754080 : ℤ) := by decide +kernel

private theorem row37_block0 : dottiePairRowBlock dottieFastReferenceWeight 37 0 37 =
    (-18173267804830256018980537525612858371341993702163906449114612717628741598880 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 37 0 37).symm.trans (by decide +kernel)

private theorem row37 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 37 1 = (-20411638804152978356178187619514810591008447185513216490955808597524521352960 : ℤ) := by
  rw [dottiePairedRowSpan_one, row37_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 37 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 37 % 1024 = 37 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row37_block0]
  decide +kernel

private theorem row38_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 38 =
    (428747948389182975670405760417374790764485625425744629514497778972365285376 : ℤ) := by decide +kernel

private theorem row38_block0 : dottiePairRowBlock dottieFastReferenceWeight 38 0 38 =
    (9459829211391101621328834025838059903465174273234847299621070025436197287312 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 38 0 38).symm.trans (by decide +kernel)

private theorem row38 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 38 1 = (9888577159780284596999239786255434694229659898660591929135567804408562572688 : ℤ) := by
  rw [dottiePairedRowSpan_one, row38_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 38 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 38 % 1024 = 38 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row38_block0]
  decide +kernel

private theorem row39_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 39 =
    (-124403358688917252790721370659437474341012562772792735372033191674537495480 : ℤ) := by decide +kernel

private theorem row39_block0 : dottiePairRowBlock dottieFastReferenceWeight 39 0 39 =
    (-1746211865040060826677648154251743508362081889746524936018440630483590731024 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 39 0 39).symm.trans (by decide +kernel)

private theorem row39 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 39 1 = (-1870615223728978079468369524911180982703094452519317671390473822158128226504 : ℤ) := by
  rw [dottiePairedRowSpan_one, row39_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 39 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 39 % 1024 = 39 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row39_block0]
  decide +kernel

private theorem row40_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 40 =
    (0 : ℤ) := by decide +kernel

private theorem row40_block0 : dottiePairRowBlock dottieFastReferenceWeight 40 0 40 =
    (736494975696332514400684770608133915391794060063912474840949912432412691872 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 40 0 40).symm.trans (by decide +kernel)

private theorem row40 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 40 1 = (736494975696332514400684770608133915391794060063912474840949912432412691872 : ℤ) := by
  rw [dottiePairedRowSpan_one, row40_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 40 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 40 % 1024 = 40 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row40_block0]
  decide +kernel

private theorem row41_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 41 =
    (-330545411329971102020610940434794501350815481473192948394423196645834532864 : ℤ) := by decide +kernel

private theorem row41_block0 : dottiePairRowBlock dottieFastReferenceWeight 41 0 41 =
    (11175192020388816327297073963929780594295827676010793408492073643692991292224 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 41 0 41).symm.trans (by decide +kernel)

private theorem row41 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 41 1 = (10844646609058845225276463023494986092945012194537600460097650447047156759360 : ℤ) := by
  rw [dottiePairedRowSpan_one, row41_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 41 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 41 % 1024 = 41 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row41_block0]
  decide +kernel

private theorem row42_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 42 =
    (1726053915511964199784572321394532064610146710004502064439458149543904234880 : ℤ) := by decide +kernel

private theorem row42_block0 : dottiePairRowBlock dottieFastReferenceWeight 42 0 42 =
    (9374390379385339700521372845837726580797642473097527198011135527520945474280 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 42 0 42).symm.trans (by decide +kernel)

private theorem row42 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 42 1 = (11100444294897303900305945167232258645407789183102029262450593677064849709160 : ℤ) := by
  rw [dottiePairedRowSpan_one, row42_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 42 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 42 % 1024 = 42 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row42_block0]
  decide +kernel

private theorem row43_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 43 =
    (-1258897035889620217231678481650228250275683555865230663486013168026682700680 : ℤ) := by decide +kernel

private theorem row43_block0 : dottiePairRowBlock dottieFastReferenceWeight 43 0 43 =
    (11280352845801110416393969933306132107225099583482816900903320562229353453872 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 43 0 43).symm.trans (by decide +kernel)

private theorem row43 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 43 1 = (10021455809911490199162291451655903856949416027617586237417307394202670753192 : ℤ) := by
  rw [dottiePairedRowSpan_one, row43_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 43 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 43 % 1024 = 43 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row43_block0]
  decide +kernel

private theorem row44_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 44 =
    (275885631092235941387927523684335587452966153118695733681501945868017423208 : ℤ) := by decide +kernel

private theorem row44_block0 : dottiePairRowBlock dottieFastReferenceWeight 44 0 44 =
    (27726407222054126222931361373946193272143500208055138863077791558307158786136 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 44 0 44).symm.trans (by decide +kernel)

private theorem row44 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 44 1 = (28002292853146362164319288897630528859596466361173834596759293504175176209344 : ℤ) := by
  rw [dottiePairedRowSpan_one, row44_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 44 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 44 % 1024 = 44 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row44_block0]
  decide +kernel

private theorem row45_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 45 =
    (-587815235679881053935035666248873318522398427395033675105258809584358424576 : ℤ) := by decide +kernel

private theorem row45_block0 : dottiePairRowBlock dottieFastReferenceWeight 45 0 45 =
    (-33379647552018231586119486687173703387373665904465929867411438386050310721128 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 45 0 45).symm.trans (by decide +kernel)

private theorem row45 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 45 1 = (-33967462787698112640054522353422576705896064331860963542516697195634669145704 : ℤ) := by
  rw [dottiePairedRowSpan_one, row45_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 45 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 45 % 1024 = 45 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row45_block0]
  decide +kernel

private theorem row46_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 46 =
    (-2649988762388389561044918596978074045563302776815096564368102439161770801896 : ℤ) := by decide +kernel

private theorem row46_block0 : dottiePairRowBlock dottieFastReferenceWeight 46 0 46 =
    (-7924043085523610997586788116442905220523862456300398096626998046662949128840 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 46 0 46).symm.trans (by decide +kernel)

private theorem row46 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 46 1 = (-10574031847912000558631706713420979266087165233115494660995100485824719930736 : ℤ) := by
  rw [dottiePairedRowSpan_one, row46_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 46 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 46 % 1024 = 46 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row46_block0]
  decide +kernel

private theorem row47_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 47 =
    (2222700353397476576789601445091668735548277384392560380590593860881800520048 : ℤ) := by decide +kernel

private theorem row47_block0 : dottiePairRowBlock dottieFastReferenceWeight 47 0 47 =
    (27539626436459581531216310578374399374810274424210791072242247108705320416656 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 47 0 47).symm.trans (by decide +kernel)

private theorem row47 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 47 1 = (29762326789857058108005912023466068110358551808603351452832840969587120936704 : ℤ) := by
  rw [dottiePairedRowSpan_one, row47_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 47 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 47 % 1024 = 47 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row47_block0]
  decide +kernel

private theorem row48_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 48 =
    (-2578528564748455444910904030017679913570822875723397322901038227950432458752 : ℤ) := by decide +kernel

private theorem row48_block0 : dottiePairRowBlock dottieFastReferenceWeight 48 0 48 =
    (5743918624045637280172900898130802573043974313153419550857751487642923331088 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 48 0 48).symm.trans (by decide +kernel)

private theorem row48 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 48 1 = (3165390059297181835261996868113122659473151437430022227956713259692490872336 : ℤ) := by
  rw [dottiePairedRowSpan_one, row48_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 48 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 48 % 1024 = 48 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row48_block0]
  decide +kernel

private theorem row49_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 49 =
    (2262030178941719490893395909130212186135828291359231822406914323521275380160 : ℤ) := by decide +kernel

private theorem row49_block0 : dottiePairRowBlock dottieFastReferenceWeight 49 0 49 =
    (-14345065800737896857648982473446448587565549158505325976449289789861502630680 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 49 0 49).symm.trans (by decide +kernel)

private theorem row49 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 49 1 = (-12083035621796177366755586564316236401429720867146094154042375466340227250520 : ℤ) := by
  rw [dottiePairedRowSpan_one, row49_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 49 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 49 % 1024 = 49 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row49_block0]
  decide +kernel

private theorem row50_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 50 =
    (-1478758027038754525018331371131261790758973401422861381136118122609294266072 : ℤ) := by decide +kernel

private theorem row50_block0 : dottiePairRowBlock dottieFastReferenceWeight 50 0 50 =
    (38205982904770892669769903872741685839054670787866460410113605169895564681512 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 50 0 50).symm.trans (by decide +kernel)

private theorem row50 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 50 1 = (36727224877732138144751572501610424048295697386443599028977487047286270415440 : ℤ) := by
  rw [dottiePairedRowSpan_one, row50_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 50 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 50 % 1024 = 50 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row50_block0]
  decide +kernel

private theorem row51_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 51 =
    (882432764720154915332100674043153244709503816493000115356809543136051578656 : ℤ) := by decide +kernel

private theorem row51_block0 : dottiePairRowBlock dottieFastReferenceWeight 51 0 51 =
    (18979140897589123955300952922195647575449078316789947709112025273600847913632 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 51 0 51).symm.trans (by decide +kernel)

private theorem row51 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 51 1 = (19861573662309278870633053596238800820158582133282947824468834816736899492288 : ℤ) := by
  rw [dottiePairedRowSpan_one, row51_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 51 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 51 % 1024 = 51 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row51_block0]
  decide +kernel

private theorem row52_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 52 =
    (-1436461062019542501833986820264646119443477305887467959707119228549758595824 : ℤ) := by decide +kernel

private theorem row52_block0 : dottiePairRowBlock dottieFastReferenceWeight 52 0 52 =
    (11336329616734721199504320543967597446963813523111904681571474763374407088280 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 52 0 52).symm.trans (by decide +kernel)

private theorem row52 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 52 1 = (9899868554715178697670333723702951327520336217224436721864355534824648492456 : ℤ) := by
  rw [dottiePairedRowSpan_one, row52_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 52 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 52 % 1024 = 52 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row52_block0]
  decide +kernel

private theorem row53_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 53 =
    (-2047608200474283408803336896172824451497112326900337022338426790352020674960 : ℤ) := by decide +kernel

private theorem row53_block0 : dottiePairRowBlock dottieFastReferenceWeight 53 0 53 =
    (5665329813130026934516073007204357432903474846273634401633397620052183700544 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 53 0 53).symm.trans (by decide +kernel)

private theorem row53 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 53 1 = (3617721612655743525712736111031532981406362519373297379294970829700163025584 : ℤ) := by
  rw [dottiePairedRowSpan_one, row53_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 53 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 53 % 1024 = 53 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row53_block0]
  decide +kernel

private theorem row54_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 54 =
    (1460788201355744223568695519056984526532115837575714452189669929923893256192 : ℤ) := by decide +kernel

private theorem row54_block0 : dottiePairRowBlock dottieFastReferenceWeight 54 0 54 =
    (9588279575491033646805276128121666440504930187041495120597055505724790403712 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 54 0 54).symm.trans (by decide +kernel)

private theorem row54 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 54 1 = (11049067776846777870373971647178650967037046024617209572786725435648683659904 : ℤ) := by
  rw [dottiePairedRowSpan_one, row54_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 54 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 54 % 1024 = 54 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row54_block0]
  decide +kernel

private theorem row55_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 55 =
    (-771577711555886263817383257069889658306987251253411129232307829292469442672 : ℤ) := by decide +kernel

private theorem row55_block0 : dottiePairRowBlock dottieFastReferenceWeight 55 0 55 =
    (1687276316900845006499408173808085582666958942252574458656035661698549201776 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 55 0 55).symm.trans (by decide +kernel)

private theorem row55 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 55 1 = (915698605344958742682024916738195924359971690999163329423727832406079759104 : ℤ) := by
  rw [dottiePairedRowSpan_one, row55_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 55 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 55 % 1024 = 55 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row55_block0]
  decide +kernel

private theorem span33_35 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 33 2 = (-31621597605952865748760766368043948598720395357692950630599285942753390818536 : ℤ) := by
  calc
    _ = (-30669503834212980210828504611628524575906997725077422883850209575886539198568 : ℤ) + (-952093771739885537932261756415424022813397632615527746749076366866851619968 : ℤ) := by
      simpa only [Nat.reduceAdd, row33, row34] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 33 1 1
    _ = _ := by decide +kernel

private theorem span32_35 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 32 3 = (-63216664810894264609184001157071711332276726445636366492185141989214075403072 : ℤ) := by
  calc
    _ = (-31595067204941398860423234789027762733556331087943415861585856046460684584536 : ℤ) + (-31621597605952865748760766368043948598720395357692950630599285942753390818536 : ℤ) := by
      simpa only [Nat.reduceAdd, row32, span33_35] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 32 1 2
    _ = _ := by decide +kernel

private theorem span36_38 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 36 2 = (-44889072013056130911771860804212796880479485074432916062155106743327112523984 : ℤ) := by
  calc
    _ = (-24477433208903152555593673184697986289471037888919699571199298145802591171024 : ℤ) + (-20411638804152978356178187619514810591008447185513216490955808597524521352960 : ℤ) := by
      simpa only [Nat.reduceAdd, row36, row37] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 36 1 1
    _ = _ := by decide +kernel

private theorem span35_38 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 35 3 = (-61036670034012097185522582583470678677657502475636196641478137734604488550384 : ℤ) := by
  calc
    _ = (-16147598020955966273750721779257881797178017401203280579323030991277376026400 : ℤ) + (-44889072013056130911771860804212796880479485074432916062155106743327112523984 : ℤ) := by
      simpa only [Nat.reduceAdd, row35, span36_38] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 35 1 2
    _ = _ := by decide +kernel

private theorem span32_38 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 32 6 = (-124253334844906361794706583740542390009934228921272563133663279723818563953456 : ℤ) := by
  calc
    _ = (-63216664810894264609184001157071711332276726445636366492185141989214075403072 : ℤ) + (-61036670034012097185522582583470678677657502475636196641478137734604488550384 : ℤ) := by
      simpa only [Nat.reduceAdd, span32_35, span35_38] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 32 3 3
    _ = _ := by decide +kernel

private theorem span39_41 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 39 2 = (-1134120248032645565067684754303047067311300392455405196549523909725715534632 : ℤ) := by
  calc
    _ = (-1870615223728978079468369524911180982703094452519317671390473822158128226504 : ℤ) + (736494975696332514400684770608133915391794060063912474840949912432412691872 : ℤ) := by
      simpa only [Nat.reduceAdd, row39, row40] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 39 1 1
    _ = _ := by decide +kernel

private theorem span38_41 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 38 3 = (8754456911747639031931555031952387626918359506205186732586043894682847038056 : ℤ) := by
  calc
    _ = (9888577159780284596999239786255434694229659898660591929135567804408562572688 : ℤ) + (-1134120248032645565067684754303047067311300392455405196549523909725715534632 : ℤ) := by
      simpa only [Nat.reduceAdd, row38, span39_41] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 38 1 2
    _ = _ := by decide +kernel

private theorem span42_44 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 42 2 = (21121900104808794099468236618888162502357205210719615499867901071267520462352 : ℤ) := by
  calc
    _ = (11100444294897303900305945167232258645407789183102029262450593677064849709160 : ℤ) + (10021455809911490199162291451655903856949416027617586237417307394202670753192 : ℤ) := by
      simpa only [Nat.reduceAdd, row42, row43] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 42 1 1
    _ = _ := by decide +kernel

private theorem span41_44 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 41 3 = (31966546713867639324744699642383148595302217405257215959965551518314677221712 : ℤ) := by
  calc
    _ = (10844646609058845225276463023494986092945012194537600460097650447047156759360 : ℤ) + (21121900104808794099468236618888162502357205210719615499867901071267520462352 : ℤ) := by
      simpa only [Nat.reduceAdd, row41, span42_44] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 41 1 2
    _ = _ := by decide +kernel

private theorem span38_44 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 38 6 = (40721003625615278356676254674335536222220576911462402692551595412997524259768 : ℤ) := by
  calc
    _ = (8754456911747639031931555031952387626918359506205186732586043894682847038056 : ℤ) + (31966546713867639324744699642383148595302217405257215959965551518314677221712 : ℤ) := by
      simpa only [Nat.reduceAdd, span38_41, span41_44] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 38 3 3
    _ = _ := by decide +kernel

private theorem span32_44 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 32 12 = (-83532331219291083438030329066206853787713652009810160441111684310821039693688 : ℤ) := by
  calc
    _ = (-124253334844906361794706583740542390009934228921272563133663279723818563953456 : ℤ) + (40721003625615278356676254674335536222220576911462402692551595412997524259768 : ℤ) := by
      simpa only [Nat.reduceAdd, span32_38, span38_44] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 32 6 6
    _ = _ := by decide +kernel

private theorem span45_47 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 45 2 = (-44541494635610113198686229066843555971983229564976458203511797681459389076440 : ℤ) := by
  calc
    _ = (-33967462787698112640054522353422576705896064331860963542516697195634669145704 : ℤ) + (-10574031847912000558631706713420979266087165233115494660995100485824719930736 : ℤ) := by
      simpa only [Nat.reduceAdd, row45, row46] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 45 1 1
    _ = _ := by decide +kernel

private theorem span44_47 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 44 3 = (-16539201782463751034366940169213027112386763203802623606752504177284212867096 : ℤ) := by
  calc
    _ = (28002292853146362164319288897630528859596466361173834596759293504175176209344 : ℤ) + (-44541494635610113198686229066843555971983229564976458203511797681459389076440 : ℤ) := by
      simpa only [Nat.reduceAdd, row44, span45_47] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 44 1 2
    _ = _ := by decide +kernel

private theorem span48_50 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 48 2 = (-8917645562498995531493589696203113741956569429716071926085662206647736378184 : ℤ) := by
  calc
    _ = (3165390059297181835261996868113122659473151437430022227956713259692490872336 : ℤ) + (-12083035621796177366755586564316236401429720867146094154042375466340227250520 : ℤ) := by
      simpa only [Nat.reduceAdd, row48, row49] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 48 1 1
    _ = _ := by decide +kernel

private theorem span47_50 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 47 3 = (20844681227358062576512322327262954368401982378887279526747178762939384558520 : ℤ) := by
  calc
    _ = (29762326789857058108005912023466068110358551808603351452832840969587120936704 : ℤ) + (-8917645562498995531493589696203113741956569429716071926085662206647736378184 : ℤ) := by
      simpa only [Nat.reduceAdd, row47, span48_50] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 47 1 2
    _ = _ := by decide +kernel

private theorem span44_50 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 44 6 = (4305479444894311542145382158049927256015219175084655919994674585655171691424 : ℤ) := by
  calc
    _ = (-16539201782463751034366940169213027112386763203802623606752504177284212867096 : ℤ) + (20844681227358062576512322327262954368401982378887279526747178762939384558520 : ℤ) := by
      simpa only [Nat.reduceAdd, span44_47, span47_50] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 44 3 3
    _ = _ := by decide +kernel

private theorem span51_53 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 51 2 = (29761442217024457568303387319941752147678918350507384546333190351561547984744 : ℤ) := by
  calc
    _ = (19861573662309278870633053596238800820158582133282947824468834816736899492288 : ℤ) + (9899868554715178697670333723702951327520336217224436721864355534824648492456 : ℤ) := by
      simpa only [Nat.reduceAdd, row51, row52] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 51 1 1
    _ = _ := by decide +kernel

private theorem span50_53 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 50 3 = (66488667094756595713054959821552176195974615736950983575310677398847818400184 : ℤ) := by
  calc
    _ = (36727224877732138144751572501610424048295697386443599028977487047286270415440 : ℤ) + (29761442217024457568303387319941752147678918350507384546333190351561547984744 : ℤ) := by
      simpa only [Nat.reduceAdd, row50, span51_53] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 50 1 2
    _ = _ := by decide +kernel

private theorem span54_56 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 54 2 = (11964766382191736613055996563916846891397017715616372902210453268054763419008 : ℤ) := by
  calc
    _ = (11049067776846777870373971647178650967037046024617209572786725435648683659904 : ℤ) + (915698605344958742682024916738195924359971690999163329423727832406079759104 : ℤ) := by
      simpa only [Nat.reduceAdd, row54, row55] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 54 1 1
    _ = _ := by decide +kernel

private theorem span53_56 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 53 3 = (15582487994847480138768732674948379872803380234989670281505424097754926444592 : ℤ) := by
  calc
    _ = (3617721612655743525712736111031532981406362519373297379294970829700163025584 : ℤ) + (11964766382191736613055996563916846891397017715616372902210453268054763419008 : ℤ) := by
      simpa only [Nat.reduceAdd, row53, span54_56] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 53 1 2
    _ = _ := by decide +kernel

private theorem span50_56 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 50 6 = (82071155089604075851823692496500556068777995971940653856816101496602744844776 : ℤ) := by
  calc
    _ = (66488667094756595713054959821552176195974615736950983575310677398847818400184 : ℤ) + (15582487994847480138768732674948379872803380234989670281505424097754926444592 : ℤ) := by
      simpa only [Nat.reduceAdd, span50_53, span53_56] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 50 3 3
    _ = _ := by decide +kernel

private theorem span44_56 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 44 12 = (86376634534498387393969074654550483324793215147025309776810776082257916536200 : ℤ) := by
  calc
    _ = (4305479444894311542145382158049927256015219175084655919994674585655171691424 : ℤ) + (82071155089604075851823692496500556068777995971940653856816101496602744844776 : ℤ) := by
      simpa only [Nat.reduceAdd, span44_50, span50_56] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 44 6 6
    _ = _ := by decide +kernel

private theorem span32_56 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 32 24 = (2844303315207303955938745588343629537079563137215149335699091771436876842512 : ℤ) := by
  calc
    _ = (-83532331219291083438030329066206853787713652009810160441111684310821039693688 : ℤ) + (86376634534498387393969074654550483324793215147025309776810776082257916536200 : ℤ) := by
      simpa only [Nat.reduceAdd, span32_44, span44_56] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 32 12 12
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows32To56 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 32 24 = (2844303315207303955938745588343629537079563137215149335699091771436876842512 : ℤ) :=
  span32_56

#print axioms dottieFastReferenceRows32To56

end QuarticModel
