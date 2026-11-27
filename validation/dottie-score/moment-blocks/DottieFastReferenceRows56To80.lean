import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row56_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 56 =
    (1173635386106296043167589187245653315388752506087049217513539272562388467832 : ℤ) := by decide +kernel

private theorem row56_block0 : dottiePairRowBlock dottieFastReferenceWeight 56 0 56 =
    (33513588445977390205494529846660296547022744132221231588025797197131339011080 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 56 0 56).symm.trans (by decide +kernel)

private theorem row56 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 56 1 = (34687223832083686248662119033905949862411496638308280805539336469693727478912 : ℤ) := by
  rw [dottiePairedRowSpan_one, row56_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 56 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 56 % 1024 = 56 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row56_block0]
  decide +kernel

private theorem row57_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 57 =
    (1316645917185795582120543327762250373463636720101847048047424174659576342536 : ℤ) := by decide +kernel

private theorem row57_block0 : dottiePairRowBlock dottieFastReferenceWeight 57 0 57 =
    (22846992498028887348890576327455915598883717683828532163056101360573783026648 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 57 0 57).symm.trans (by decide +kernel)

private theorem row57 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 57 1 = (24163638415214682931011119655218165972347354403930379211103525535233359369184 : ℤ) := by
  rw [dottiePairedRowSpan_one, row57_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 57 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 57 % 1024 = 57 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row57_block0]
  decide +kernel

private theorem row58_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 58 =
    (-207200802515958851911981698370018821628655709805205596561101009750080805632 : ℤ) := by decide +kernel

private theorem row58_block0 : dottiePairRowBlock dottieFastReferenceWeight 58 0 58 =
    (4284664900641333096704817378967676642931728082411795264591406039684082364784 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 58 0 58).symm.trans (by decide +kernel)

private theorem row58 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 58 1 = (4077464098125374244792835680597657821303072372606589668030305029934001559152 : ℤ) := by
  rw [dottiePairedRowSpan_one, row58_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 58 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 58 % 1024 = 58 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row58_block0]
  decide +kernel

private theorem row59_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 59 =
    (-294698649111441393207925659207169238158523299908536131496232579012328014880 : ℤ) := by decide +kernel

private theorem row59_block0 : dottiePairRowBlock dottieFastReferenceWeight 59 0 59 =
    (28691436788564566964520113640901662104309925444830158581962228069128164029712 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 59 0 59).symm.trans (by decide +kernel)

private theorem row59 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 59 1 = (28396738139453125571312187981694492866151402144921622450465995490115836014832 : ℤ) := by
  rw [dottiePairedRowSpan_one, row59_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 59 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 59 % 1024 = 59 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row59_block0]
  decide +kernel

private theorem row60_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 60 =
    (-1244728570704741267226226032820428729943128469172193148742115978072276991448 : ℤ) := by decide +kernel

private theorem row60_block0 : dottiePairRowBlock dottieFastReferenceWeight 60 0 60 =
    (-3128038401498259752538406212731441185292779244048275515228276393386149445952 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 60 0 60).symm.trans (by decide +kernel)

private theorem row60 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 60 1 = (-4372766972203001019764632245551869915235907713220468663970392371458426437400 : ℤ) := by
  rw [dottiePairedRowSpan_one, row60_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 60 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 60 % 1024 = 60 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row60_block0]
  decide +kernel

private theorem row61_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 61 =
    (626427556482293388897933061548417822910943493366163254779944039286325231680 : ℤ) := by decide +kernel

private theorem row61_block0 : dottiePairRowBlock dottieFastReferenceWeight 61 0 61 =
    (17181546326016497124164376499293248070095848728691734778827623641007091624584 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 61 0 61).symm.trans (by decide +kernel)

private theorem row61 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 61 1 = (17807973882498790513062309560841665893006792222057898033607567680293416856264 : ℤ) := by
  rw [dottiePairedRowSpan_one, row61_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 61 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 61 % 1024 = 61 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row61_block0]
  decide +kernel

private theorem row62_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 62 =
    (573394396433167246741418860607995781682631050939071027653955622896608510448 : ℤ) := by decide +kernel

private theorem row62_block0 : dottiePairRowBlock dottieFastReferenceWeight 62 0 62 =
    (-5519468479394192480327848858395681110644160143641629066566497480391046172360 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 62 0 62).symm.trans (by decide +kernel)

private theorem row62 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 62 1 = (-4946074082961025233586429997787685328961529092702558038912541857494437661912 : ℤ) := by
  rw [dottiePairedRowSpan_one, row62_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 62 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 62 % 1024 = 62 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row62_block0]
  decide +kernel

private theorem row63_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 63 =
    (1365698650282121021526429165866846879720140107493127906839099050171770046720 : ℤ) := by decide +kernel

private theorem row63_block0 : dottiePairRowBlock dottieFastReferenceWeight 63 0 63 =
    (21851965535638872389239735154730439038795957487676821754881206437277938436616 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 63 0 63).symm.trans (by decide +kernel)

private theorem row63 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 63 1 = (23217664185920993410766164320597285918516097595169949661720305487449708483336 : ℤ) := by
  rw [dottiePairedRowSpan_one, row63_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 63 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 63 % 1024 = 63 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row63_block0]
  decide +kernel

private theorem row64_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 64 =
    (1953557918972718692434632307431567801313154953359076422024228608171374918400 : ℤ) := by decide +kernel

private theorem row64_block0 : dottiePairRowBlock dottieFastReferenceWeight 64 0 64 =
    (17859263971561175445097584093335994685390540950627318274079739579168649720992 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 64 0 64).symm.trans (by decide +kernel)

private theorem row64 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 64 1 = (19812821890533894137532216400767562486703695903986394696103968187340024639392 : ℤ) := by
  rw [dottiePairedRowSpan_one, row64_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 64 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 64 % 1024 = 64 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row64_block0]
  decide +kernel

private theorem row65_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 65 =
    (517686350747271594587912199336739511420633450585075185799594496903340922952 : ℤ) := by decide +kernel

private theorem row65_block0 : dottiePairRowBlock dottieFastReferenceWeight 65 0 65 =
    (5503710258971740792747357057926207627873393322132874638286216765058282912728 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 65 0 65).symm.trans (by decide +kernel)

private theorem row65 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 65 1 = (6021396609719012387335269257262947139294026772717949824085811261961623835680 : ℤ) := by
  rw [dottiePairedRowSpan_one, row65_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 65 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 65 % 1024 = 65 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row65_block0]
  decide +kernel

private theorem row66_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 66 =
    (271349799465724966283121980213863601185716388736396402492980436001383477864 : ℤ) := by decide +kernel

private theorem row66_block0 : dottiePairRowBlock dottieFastReferenceWeight 66 0 66 =
    (25767996108827964665945315582799760817416704754051310987255618972941305914584 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 66 0 66).symm.trans (by decide +kernel)

private theorem row66 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 66 1 = (26039345908293689632228437563013624418602421142787707389748599408942689392448 : ℤ) := by
  rw [dottiePairedRowSpan_one, row66_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 66 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 66 % 1024 = 66 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row66_block0]
  decide +kernel

private theorem row67_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 67 =
    (-1432161867755115057538077433484353759176042550009408600044140152949414556456 : ℤ) := by decide +kernel

private theorem row67_block0 : dottiePairRowBlock dottieFastReferenceWeight 67 0 67 =
    (4848747140340286208186068560752670777392969880481962118675552528781416142360 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 67 0 67).symm.trans (by decide +kernel)

private theorem row67 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 67 1 = (3416585272585171150647991127268317018216927330472553518631412375832001585904 : ℤ) := by
  rw [dottiePairedRowSpan_one, row67_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 67 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 67 % 1024 = 67 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row67_block0]
  decide +kernel

private theorem row68_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 68 =
    (65644635092311538891265537942403941629154008662154298274104598712307142888 : ℤ) := by decide +kernel

private theorem row68_block0 : dottiePairRowBlock dottieFastReferenceWeight 68 0 68 =
    (26810588954314021409854703395416540490582333778464768839650554409896215609576 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 68 0 68).symm.trans (by decide +kernel)

private theorem row68 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 68 1 = (26876233589406332948745968933358944432211487787126923137924659008608522752464 : ℤ) := by
  rw [dottiePairedRowSpan_one, row68_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 68 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 68 % 1024 = 68 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row68_block0]
  decide +kernel

private theorem row69_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 69 =
    (-1810761546957779150135415467126346122044840303128810217737185704021813243136 : ℤ) := by decide +kernel

private theorem row69_block0 : dottiePairRowBlock dottieFastReferenceWeight 69 0 69 =
    (-5322692373060643693377825833479059274192923789660411765504766662109197834600 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 69 0 69).symm.trans (by decide +kernel)

private theorem row69 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 69 1 = (-7133453920018422843513241300605405396237764092789221983241952366131011077736 : ℤ) := by
  rw [dottiePairedRowSpan_one, row69_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 69 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 69 % 1024 = 69 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row69_block0]
  decide +kernel

private theorem row70_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 70 =
    (686875144738634066749019724880342064923688373909298238731139120342271408896 : ℤ) := by decide +kernel

private theorem row70_block0 : dottiePairRowBlock dottieFastReferenceWeight 70 0 70 =
    (2677191149485493898568437100429745090931114139611124513715703473159083881064 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 70 0 70).symm.trans (by decide +kernel)

private theorem row70 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 70 1 = (3364066294224127965317456825310087155854802513520422752446842593501355289960 : ℤ) := by
  rw [dottiePairedRowSpan_one, row70_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 70 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 70 % 1024 = 70 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row70_block0]
  decide +kernel

private theorem row71_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 71 =
    (-1287118530476225619129504315903717885611841901154235989289783850374539354112 : ℤ) := by decide +kernel

private theorem row71_block0 : dottiePairRowBlock dottieFastReferenceWeight 71 0 71 =
    (-4869152623203770964341623378784564068859909722121473046009514579904933095384 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 71 0 71).symm.trans (by decide +kernel)

private theorem row71 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 71 1 = (-6156271153679996583471127694688281954471751623275709035299298430279472449496 : ℤ) := by
  rw [dottiePairedRowSpan_one, row71_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 71 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 71 % 1024 = 71 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row71_block0]
  decide +kernel

private theorem row72_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 72 =
    (429483006089097201782538125416310252552803091076516363144463995857778681744 : ℤ) := by decide +kernel

private theorem row72_block0 : dottiePairRowBlock dottieFastReferenceWeight 72 0 72 =
    (18453026783864294422893724491523666015087751104686458319724277685875071733224 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 72 0 72).symm.trans (by decide +kernel)

private theorem row72 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 72 1 = (18882509789953391624676262616939976267640554195762974682868741681732850414968 : ℤ) := by
  rw [dottiePairedRowSpan_one, row72_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 72 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 72 % 1024 = 72 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row72_block0]
  decide +kernel

private theorem row73_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 73 =
    (-1414317099511126605173692721552224030141183230310293825329397679858128498336 : ℤ) := by decide +kernel

private theorem row73_block0 : dottiePairRowBlock dottieFastReferenceWeight 73 0 73 =
    (6509731923691624563465600476751387178109373964809930920195636073338552953760 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 73 0 73).symm.trans (by decide +kernel)

private theorem row73 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 73 1 = (5095414824180497958291907755199163147968190734499637094866238393480424455424 : ℤ) := by
  rw [dottiePairedRowSpan_one, row73_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 73 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 73 % 1024 = 73 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row73_block0]
  decide +kernel

private theorem row74_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 74 =
    (-1622258971866071377652048397846593156318506868983059640715094116272600441280 : ℤ) := by decide +kernel

private theorem row74_block0 : dottiePairRowBlock dottieFastReferenceWeight 74 0 74 =
    (10873765136622908526063435143667978686153615107608927178653333878711098797168 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 74 0 74).symm.trans (by decide +kernel)

private theorem row74 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 74 1 = (9251506164756837148411386745821385529835108238625867537938239762438498355888 : ℤ) := by
  rw [dottiePairedRowSpan_one, row74_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 74 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 74 % 1024 = 74 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row74_block0]
  decide +kernel

private theorem row75_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 75 =
    (520997763814565584091072948421391990340501999133025343885463868137909363280 : ℤ) := by decide +kernel

private theorem row75_block0 : dottiePairRowBlock dottieFastReferenceWeight 75 0 75 =
    (5142800435615282218030417863200853963689250497969876556557774875944352810104 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 75 0 75).symm.trans (by decide +kernel)

private theorem row75 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 75 1 = (5663798199429847802121490811622245954029752497102901900443238744082262173384 : ℤ) := by
  rw [dottiePairedRowSpan_one, row75_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 75 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 75 % 1024 = 75 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row75_block0]
  decide +kernel

private theorem row76_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 76 =
    (-1448895651384676692011172527985079674943433463165703393607555315507945870560 : ℤ) := by decide +kernel

private theorem row76_block0 : dottiePairRowBlock dottieFastReferenceWeight 76 0 76 =
    (8966815298275402029514806334397547374391344732626888620300411185179338390848 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 76 0 76).symm.trans (by decide +kernel)

private theorem row76 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 76 1 = (7517919646890725337503633806412467699447911269461185226692855869671392520288 : ℤ) := by
  rw [dottiePairedRowSpan_one, row76_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 76 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 76 % 1024 = 76 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row76_block0]
  decide +kernel

private theorem row77_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 77 =
    (-849158540950329879450161711330012819096870630336686566095278664824563191424 : ℤ) := by decide +kernel

private theorem row77_block0 : dottiePairRowBlock dottieFastReferenceWeight 77 0 77 =
    (-20658360627935357844416358106048645505171332824181468320989289321397545015456 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 77 0 77).symm.trans (by decide +kernel)

private theorem row77 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 77 1 = (-21507519168885687723866519817378658324268203454518154887084567986222108206880 : ℤ) := by
  rw [dottiePairedRowSpan_one, row77_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 77 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 77 % 1024 = 77 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row77_block0]
  decide +kernel

private theorem row78_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 78 =
    (-1057114473593125990084280211846897948345728638204224309570351543081301678088 : ℤ) := by decide +kernel

private theorem row78_block0 : dottiePairRowBlock dottieFastReferenceWeight 78 0 78 =
    (-10057903636456910785453580540173889570417537341295435217842079306309759620768 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 78 0 78).symm.trans (by decide +kernel)

private theorem row78 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 78 1 = (-11115018110050036775537860752020787518763265979499659527412430849391061298856 : ℤ) := by
  rw [dottiePairedRowSpan_one, row78_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 78 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 78 % 1024 = 78 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row78_block0]
  decide +kernel

private theorem row79_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 79 =
    (-584870067977625853387524517992581297912497791402814669973950883230644330368 : ℤ) := by decide +kernel

private theorem row79_block0 : dottiePairRowBlock dottieFastReferenceWeight 79 0 79 =
    (-1264645425505124033515678014267352769197500783001286257040129604776645156016 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 79 0 79).symm.trans (by decide +kernel)

private theorem row79 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 79 1 = (-1849515493482749886903202532259934067109998574404100927014080488007289486384 : ℤ) := by
  rw [dottiePairedRowSpan_one, row79_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 79 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 79 % 1024 = 79 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row79_block0]
  decide +kernel

private theorem span57_59 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 57 2 = (28241102513340057175803955335815823793650426776536968879133830565167360928336 : ℤ) := by
  calc
    _ = (24163638415214682931011119655218165972347354403930379211103525535233359369184 : ℤ) + (4077464098125374244792835680597657821303072372606589668030305029934001559152 : ℤ) := by
      simpa only [Nat.reduceAdd, row57, row58] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 57 1 1
    _ = _ := by decide +kernel

private theorem span56_59 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 56 3 = (62928326345423743424466074369721773656061923414845249684673167034861088407248 : ℤ) := by
  calc
    _ = (34687223832083686248662119033905949862411496638308280805539336469693727478912 : ℤ) + (28241102513340057175803955335815823793650426776536968879133830565167360928336 : ℤ) := by
      simpa only [Nat.reduceAdd, row56, span57_59] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 56 1 2
    _ = _ := by decide +kernel

private theorem span60_62 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 60 2 = (13435206910295789493297677315289795977770884508837429369637175308834990418864 : ℤ) := by
  calc
    _ = (-4372766972203001019764632245551869915235907713220468663970392371458426437400 : ℤ) + (17807973882498790513062309560841665893006792222057898033607567680293416856264 : ℤ) := by
      simpa only [Nat.reduceAdd, row60, row61] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 60 1 1
    _ = _ := by decide +kernel

private theorem span59_62 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 59 3 = (41831945049748915064609865296984288843922286653759051820103170798950826433696 : ℤ) := by
  calc
    _ = (28396738139453125571312187981694492866151402144921622450465995490115836014832 : ℤ) + (13435206910295789493297677315289795977770884508837429369637175308834990418864 : ℤ) := by
      simpa only [Nat.reduceAdd, row59, span60_62] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 59 1 2
    _ = _ := by decide +kernel

private theorem span56_62 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 56 6 = (104760271395172658489075939666706062499984210068604301504776337833811914840944 : ℤ) := by
  calc
    _ = (62928326345423743424466074369721773656061923414845249684673167034861088407248 : ℤ) + (41831945049748915064609865296984288843922286653759051820103170798950826433696 : ℤ) := by
      simpa only [Nat.reduceAdd, span56_59, span59_62] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 56 3 3
    _ = _ := by decide +kernel

private theorem span63_65 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 63 2 = (43030486076454887548298380721364848405219793499156344357824273674789733122728 : ℤ) := by
  calc
    _ = (23217664185920993410766164320597285918516097595169949661720305487449708483336 : ℤ) + (19812821890533894137532216400767562486703695903986394696103968187340024639392 : ℤ) := by
      simpa only [Nat.reduceAdd, row63, row64] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 63 1 1
    _ = _ := by decide +kernel

private theorem span62_65 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 62 3 = (38084411993493862314711950723577163076258264406453786318911731817295295460816 : ℤ) := by
  calc
    _ = (-4946074082961025233586429997787685328961529092702558038912541857494437661912 : ℤ) + (43030486076454887548298380721364848405219793499156344357824273674789733122728 : ℤ) := by
      simpa only [Nat.reduceAdd, row62, span63_65] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 62 1 2
    _ = _ := by decide +kernel

private theorem span66_68 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 66 2 = (29455931180878860782876428690281941436819348473260260908380011784774690978352 : ℤ) := by
  calc
    _ = (26039345908293689632228437563013624418602421142787707389748599408942689392448 : ℤ) + (3416585272585171150647991127268317018216927330472553518631412375832001585904 : ℤ) := by
      simpa only [Nat.reduceAdd, row66, row67] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 66 1 1
    _ = _ := by decide +kernel

private theorem span65_68 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 65 3 = (35477327790597873170211697947544888576113375245978210732465823046736314814032 : ℤ) := by
  calc
    _ = (6021396609719012387335269257262947139294026772717949824085811261961623835680 : ℤ) + (29455931180878860782876428690281941436819348473260260908380011784774690978352 : ℤ) := by
      simpa only [Nat.reduceAdd, row65, span66_68] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 65 1 2
    _ = _ := by decide +kernel

private theorem span62_68 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 62 6 = (73561739784091735484923648671122051652371639652431997051377554864031610274848 : ℤ) := by
  calc
    _ = (38084411993493862314711950723577163076258264406453786318911731817295295460816 : ℤ) + (35477327790597873170211697947544888576113375245978210732465823046736314814032 : ℤ) := by
      simpa only [Nat.reduceAdd, span62_65, span65_68] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 62 3 3
    _ = _ := by decide +kernel

private theorem span56_68 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 56 12 = (178322011179264393973999588337828114152355849721036298556153892697843525115792 : ℤ) := by
  calc
    _ = (104760271395172658489075939666706062499984210068604301504776337833811914840944 : ℤ) + (73561739784091735484923648671122051652371639652431997051377554864031610274848 : ℤ) := by
      simpa only [Nat.reduceAdd, span56_62, span62_68] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 56 6 6
    _ = _ := by decide +kernel

private theorem span69_71 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 69 2 = (-3769387625794294878195784475295318240382961579268799230795109772629655787776 : ℤ) := by
  calc
    _ = (-7133453920018422843513241300605405396237764092789221983241952366131011077736 : ℤ) + (3364066294224127965317456825310087155854802513520422752446842593501355289960 : ℤ) := by
      simpa only [Nat.reduceAdd, row69, row70] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 69 1 1
    _ = _ := by decide +kernel

private theorem span68_71 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 68 3 = (23106845963612038070550184458063626191828526207858123907129549235978866964688 : ℤ) := by
  calc
    _ = (26876233589406332948745968933358944432211487787126923137924659008608522752464 : ℤ) + (-3769387625794294878195784475295318240382961579268799230795109772629655787776 : ℤ) := by
      simpa only [Nat.reduceAdd, row68, span69_71] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 68 1 2
    _ = _ := by decide +kernel

private theorem span72_74 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 72 2 = (23977924614133889582968170372139139415608744930262611777734980075213274870392 : ℤ) := by
  calc
    _ = (18882509789953391624676262616939976267640554195762974682868741681732850414968 : ℤ) + (5095414824180497958291907755199163147968190734499637094866238393480424455424 : ℤ) := by
      simpa only [Nat.reduceAdd, row72, row73] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 72 1 1
    _ = _ := by decide +kernel

private theorem span71_74 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 71 3 = (17821653460453892999497042677450857461136993306986902742435681644933802420896 : ℤ) := by
  calc
    _ = (-6156271153679996583471127694688281954471751623275709035299298430279472449496 : ℤ) + (23977924614133889582968170372139139415608744930262611777734980075213274870392 : ℤ) := by
      simpa only [Nat.reduceAdd, row71, span72_74] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 71 1 2
    _ = _ := by decide +kernel

private theorem span68_74 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 68 6 = (40928499424065931070047227135514483652965519514845026649565230880912669385584 : ℤ) := by
  calc
    _ = (23106845963612038070550184458063626191828526207858123907129549235978866964688 : ℤ) + (17821653460453892999497042677450857461136993306986902742435681644933802420896 : ℤ) := by
      simpa only [Nat.reduceAdd, span68_71, span71_74] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 68 3 3
    _ = _ := by decide +kernel

private theorem span75_77 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 75 2 = (13181717846320573139625124618034713653477663766564087127136094613753654693672 : ℤ) := by
  calc
    _ = (5663798199429847802121490811622245954029752497102901900443238744082262173384 : ℤ) + (7517919646890725337503633806412467699447911269461185226692855869671392520288 : ℤ) := by
      simpa only [Nat.reduceAdd, row75, row76] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 75 1 1
    _ = _ := by decide +kernel

private theorem span74_77 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 74 3 = (22433224011077410288036511363856099183312772005189954665074334376192153049560 : ℤ) := by
  calc
    _ = (9251506164756837148411386745821385529835108238625867537938239762438498355888 : ℤ) + (13181717846320573139625124618034713653477663766564087127136094613753654693672 : ℤ) := by
      simpa only [Nat.reduceAdd, row74, span75_77] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 74 1 2
    _ = _ := by decide +kernel

private theorem span78_80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 78 2 = (-12964533603532786662441063284280721585873264553903760454426511337398350785240 : ℤ) := by
  calc
    _ = (-11115018110050036775537860752020787518763265979499659527412430849391061298856 : ℤ) + (-1849515493482749886903202532259934067109998574404100927014080488007289486384 : ℤ) := by
      simpa only [Nat.reduceAdd, row78, row79] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 78 1 1
    _ = _ := by decide +kernel

private theorem span77_80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 77 3 = (-34472052772418474386307583101659379910141468008421915341511079323620458992120 : ℤ) := by
  calc
    _ = (-21507519168885687723866519817378658324268203454518154887084567986222108206880 : ℤ) + (-12964533603532786662441063284280721585873264553903760454426511337398350785240 : ℤ) := by
      simpa only [Nat.reduceAdd, row77, span78_80] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 77 1 2
    _ = _ := by decide +kernel

private theorem span74_80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 74 6 = (-12038828761341064098271071737803280726828696003231960676436744947428305942560 : ℤ) := by
  calc
    _ = (22433224011077410288036511363856099183312772005189954665074334376192153049560 : ℤ) + (-34472052772418474386307583101659379910141468008421915341511079323620458992120 : ℤ) := by
      simpa only [Nat.reduceAdd, span74_77, span77_80] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 74 3 3
    _ = _ := by decide +kernel

private theorem span68_80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 68 12 = (28889670662724866971776155397711202926136823511613065973128485933484363443024 : ℤ) := by
  calc
    _ = (40928499424065931070047227135514483652965519514845026649565230880912669385584 : ℤ) + (-12038828761341064098271071737803280726828696003231960676436744947428305942560 : ℤ) := by
      simpa only [Nat.reduceAdd, span68_74, span74_80] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 68 6 6
    _ = _ := by decide +kernel

private theorem span56_80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 56 24 = (207211681841989260945775743735539317078492673232649364529282378631327888558816 : ℤ) := by
  calc
    _ = (178322011179264393973999588337828114152355849721036298556153892697843525115792 : ℤ) + (28889670662724866971776155397711202926136823511613065973128485933484363443024 : ℤ) := by
      simpa only [Nat.reduceAdd, span56_68, span68_80] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 56 12 12
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows56To80 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 56 24 = (207211681841989260945775743735539317078492673232649364529282378631327888558816 : ℤ) :=
  span56_80

#print axioms dottieFastReferenceRows56To80

end QuarticModel
