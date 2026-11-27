import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row96_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 96 =
    (832061064992678705110295917788418388810647399660808318228833601122968347440 : ℤ) := by decide +kernel

private theorem row96_block0 : dottiePairRowBlock dottieFastReferenceWeight 96 0 96 =
    (4585630110548056315249288454882855106463392275295029088919168794692550565888 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 96 0 96).symm.trans (by decide +kernel)

private theorem row96 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 96 1 = (5417691175540735020359584372671273495274039674955837407148002395815518913328 : ℤ) := by
  rw [dottiePairedRowSpan_one, row96_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 96 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 96 % 1024 = 96 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row96_block0]
  decide +kernel

private theorem row97_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 97 =
    (1242897350967446690628005024656641378012081478460740832100917086850710529192 : ℤ) := by decide +kernel

private theorem row97_block0 : dottiePairRowBlock dottieFastReferenceWeight 97 0 97 =
    (-10618315018976830113455191984271893011453565887696217093169532046112387199312 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 97 0 97).symm.trans (by decide +kernel)

private theorem row97 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 97 1 = (-9375417668009383422827186959615251633441484409235476261068614959261676670120 : ℤ) := by
  rw [dottiePairedRowSpan_one, row97_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 97 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 97 % 1024 = 97 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row97_block0]
  decide +kernel

private theorem row98_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 98 =
    (-119774175656006804940592968829856170085910405860922094467236353953076379008 : ℤ) := by decide +kernel

private theorem row98_block0 : dottiePairRowBlock dottieFastReferenceWeight 98 0 98 =
    (-16494722521082932210395808541118930284735590481373792552972343275629963485424 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 98 0 98).symm.trans (by decide +kernel)

private theorem row98 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 98 1 = (-16614496696738939015336401509948786454821500887234714647439579629583039864432 : ℤ) := by
  rw [dottiePairedRowSpan_one, row98_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 98 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 98 % 1024 = 98 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row98_block0]
  decide +kernel

private theorem row99_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 99 =
    (-1270440316679796144703643675642740979127946868757487531364940060588016410624 : ℤ) := by decide +kernel

private theorem row99_block0 : dottiePairRowBlock dottieFastReferenceWeight 99 0 99 =
    (2326685127719177611579091308298237168392143685082481660374611481752705421392 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 99 0 99).symm.trans (by decide +kernel)

private theorem row99 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 99 1 = (1056244811039381466875447632655496189264196816324994129009671421164689010768 : ℤ) := by
  rw [dottiePairedRowSpan_one, row99_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 99 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 99 % 1024 = 99 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row99_block0]
  decide +kernel

private theorem row100_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 100 =
    (1053578462526339403001028579872518443752417895651327639659772629479275521112 : ℤ) := by decide +kernel

private theorem row100_block0 : dottiePairRowBlock dottieFastReferenceWeight 100 0 100 =
    (-3106622727207380136707536635433316961298115415610848713201215959020164100488 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 100 0 100).symm.trans (by decide +kernel)

private theorem row100 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 100 1 = (-2053044264681040733706508055560798517545697519959521073541443329540888579376 : ℤ) := by
  rw [dottiePairedRowSpan_one, row100_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 100 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 100 % 1024 = 100 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row100_block0]
  decide +kernel

private theorem row101_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 101 =
    (1082245554549766264081916133653723700713308565722240478474147129800762800736 : ℤ) := by decide +kernel

private theorem row101_block0 : dottiePairRowBlock dottieFastReferenceWeight 101 0 101 =
    (-14739739880756859505538871742447086896306214298861519248849081158507723480216 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 101 0 101).symm.trans (by decide +kernel)

private theorem row101 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 101 1 = (-13657494326207093241456955608793363195592905733139278770374934028706960679480 : ℤ) := by
  rw [dottiePairedRowSpan_one, row101_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 101 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 101 % 1024 = 101 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row101_block0]
  decide +kernel

private theorem row102_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 102 =
    (687448920557312843768030082390427405778097755570147263614036456360047911040 : ℤ) := by decide +kernel

private theorem row102_block0 : dottiePairRowBlock dottieFastReferenceWeight 102 0 102 =
    (-11350429478626309573341983586687271845813547126440963332211321027703153919008 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 102 0 102).symm.trans (by decide +kernel)

private theorem row102 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 102 1 = (-10662980558068996729573953504296844440035449370870816068597284571343106007968 : ℤ) := by
  rw [dottiePairedRowSpan_one, row102_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 102 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 102 % 1024 = 102 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row102_block0]
  decide +kernel

private theorem row103_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 103 =
    (-864497447974840469085240477258732593656000039719549163119494213324649401376 : ℤ) := by decide +kernel

private theorem row103_block0 : dottiePairRowBlock dottieFastReferenceWeight 103 0 103 =
    (-23641589070563184287683215470391405577514208381936006459729342197699676883688 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 103 0 103).symm.trans (by decide +kernel)

private theorem row103 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 103 1 = (-24506086518538024756768455947650138171170208421655555622848836411024326285064 : ℤ) := by
  rw [dottiePairedRowSpan_one, row103_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 103 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 103 % 1024 = 103 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row103_block0]
  decide +kernel

private theorem row104_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 104 =
    (1207565489964080184064367475293497265678452133583280315438655743876803854336 : ℤ) := by decide +kernel

private theorem row104_block0 : dottiePairRowBlock dottieFastReferenceWeight 104 0 104 =
    (-4824643849362933897914327365368739573509094545746723760239872848643055854440 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 104 0 104).symm.trans (by decide +kernel)

private theorem row104 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 104 1 = (-3617078359398853713849959890075242307830642412163443444801217104766252000104 : ℤ) := by
  rw [dottiePairedRowSpan_one, row104_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 104 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 104 % 1024 = 104 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row104_block0]
  decide +kernel

private theorem row105_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 105 =
    (268649653820335078167461985694409704731298194993473751170845039189341803536 : ℤ) := by decide +kernel

private theorem row105_block0 : dottiePairRowBlock dottieFastReferenceWeight 105 0 105 =
    (4596346962528466826449237360222296243697795837342491070763502141364698983960 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 105 0 105).symm.trans (by decide +kernel)

private theorem row105 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 105 1 = (4864996616348801904616699345916705948429094032335964821934347180554040787496 : ℤ) := by
  rw [dottiePairedRowSpan_one, row105_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 105 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 105 % 1024 = 105 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row105_block0]
  decide +kernel

private theorem row106_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 106 =
    (-996166561695684961412605523652613594660315842887773013632479091962367706624 : ℤ) := by decide +kernel

private theorem row106_block0 : dottiePairRowBlock dottieFastReferenceWeight 106 0 106 =
    (6338506070132343743897796536847291438578112116430722346888855045163425321696 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 106 0 106).symm.trans (by decide +kernel)

private theorem row106 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 106 1 = (5342339508436658782485191013194677843917796273542949333256375953201057615072 : ℤ) := by
  rw [dottiePairedRowSpan_one, row106_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 106 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 106 % 1024 = 106 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row106_block0]
  decide +kernel

private theorem row107_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 107 =
    (701030291651404806289672250034292056607186835056399728087628468492745737088 : ℤ) := by decide +kernel

private theorem row107_block0 : dottiePairRowBlock dottieFastReferenceWeight 107 0 107 =
    (-5494617347065738860849978559883508632190417067855894418341054773584149815384 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 107 0 107).symm.trans (by decide +kernel)

private theorem row107 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 107 1 = (-4793587055414334054560306309849216575583230232799494690253426305091404078296 : ℤ) := by
  rw [dottiePairedRowSpan_one, row107_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 107 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 107 % 1024 = 107 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row107_block0]
  decide +kernel

private theorem row108_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 108 =
    (573430566204095875851401134487017235359554553543686668177399694965629233920 : ℤ) := by decide +kernel

private theorem row108_block0 : dottiePairRowBlock dottieFastReferenceWeight 108 0 108 =
    (-348234876173382023084181171295097354471427706397145684015056070971089754848 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 108 0 108).symm.trans (by decide +kernel)

private theorem row108 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 108 1 = (225195690030713852767219963191919880888126847146540984162343623994539479072 : ℤ) := by
  rw [dottiePairedRowSpan_one, row108_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 108 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 108 % 1024 = 108 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row108_block0]
  decide +kernel

private theorem row109_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 109 =
    (-1030519697881542524929760001839446564064136365429072220011893986318622862032 : ℤ) := by decide +kernel

private theorem row109_block0 : dottiePairRowBlock dottieFastReferenceWeight 109 0 109 =
    (-8434832952528475815366547030783769801224356474337004430372230362046724082672 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 109 0 109).symm.trans (by decide +kernel)

private theorem row109 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 109 1 = (-9465352650410018340296307032623216365288492839766076650384124348365346944704 : ℤ) := by
  rw [dottiePairedRowSpan_one, row109_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 109 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 109 % 1024 = 109 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row109_block0]
  decide +kernel

private theorem row110_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 110 =
    (1043750654849027786733805152954967988447466526804596948784643498130977430656 : ℤ) := by decide +kernel

private theorem row110_block0 : dottiePairRowBlock dottieFastReferenceWeight 110 0 110 =
    (-4072873080546293211897715787599630928290827800181399531260856249486382715800 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 110 0 110).symm.trans (by decide +kernel)

private theorem row110 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 110 1 = (-3029122425697265425163910634644662939843361273376802582476212751355405285144 : ℤ) := by
  rw [dottiePairedRowSpan_one, row110_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 110 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 110 % 1024 = 110 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row110_block0]
  decide +kernel

private theorem row111_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 111 =
    (784477412284248794737134726847636762709318077833039837222562691406226799744 : ℤ) := by decide +kernel

private theorem row111_block0 : dottiePairRowBlock dottieFastReferenceWeight 111 0 111 =
    (-5656162973856989114164531935857712041975868444333227776800974192442217436872 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 111 0 111).symm.trans (by decide +kernel)

private theorem row111 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 111 1 = (-4871685561572740319427397209010075279266550366500187939578411501035990637128 : ℤ) := by
  rw [dottiePairedRowSpan_one, row111_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 111 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 111 % 1024 = 111 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row111_block0]
  decide +kernel

private theorem span96_98 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 96 2 = (-3957726492468648402467602586943978138167444734279638853920612563446157756792 : ℤ) := by
  calc
    _ = (5417691175540735020359584372671273495274039674955837407148002395815518913328 : ℤ) + (-9375417668009383422827186959615251633441484409235476261068614959261676670120 : ℤ) := by
      simpa only [Nat.reduceAdd, row96, row97] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 96 1 1
    _ = _ := by decide +kernel

private theorem span98_100 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 98 2 = (-15558251885699557548460953877293290265557304070909720518429908208418350853664 : ℤ) := by
  calc
    _ = (-16614496696738939015336401509948786454821500887234714647439579629583039864432 : ℤ) + (1056244811039381466875447632655496189264196816324994129009671421164689010768 : ℤ) := by
      simpa only [Nat.reduceAdd, row98, row99] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 98 1 1
    _ = _ := by decide +kernel

private theorem span96_100 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 96 4 = (-19515978378168205950928556464237268403724748805189359372350520771864508610456 : ℤ) := by
  calc
    _ = (-3957726492468648402467602586943978138167444734279638853920612563446157756792 : ℤ) + (-15558251885699557548460953877293290265557304070909720518429908208418350853664 : ℤ) := by
      simpa only [Nat.reduceAdd, span96_98, span98_100] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 96 2 2
    _ = _ := by decide +kernel

private theorem span100_102 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 100 2 = (-15710538590888133975163463664354161713138603253098799843916377358247849258856 : ℤ) := by
  calc
    _ = (-2053044264681040733706508055560798517545697519959521073541443329540888579376 : ℤ) + (-13657494326207093241456955608793363195592905733139278770374934028706960679480 : ℤ) := by
      simpa only [Nat.reduceAdd, row100, row101] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 100 1 1
    _ = _ := by decide +kernel

private theorem span102_104 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 102 2 = (-35169067076607021486342409451946982611205657792526371691446120982367432293032 : ℤ) := by
  calc
    _ = (-10662980558068996729573953504296844440035449370870816068597284571343106007968 : ℤ) + (-24506086518538024756768455947650138171170208421655555622848836411024326285064 : ℤ) := by
      simpa only [Nat.reduceAdd, row102, row103] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 102 1 1
    _ = _ := by decide +kernel

private theorem span100_104 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 100 4 = (-50879605667495155461505873116301144324344261045625171535362498340615281551888 : ℤ) := by
  calc
    _ = (-15710538590888133975163463664354161713138603253098799843916377358247849258856 : ℤ) + (-35169067076607021486342409451946982611205657792526371691446120982367432293032 : ℤ) := by
      simpa only [Nat.reduceAdd, span100_102, span102_104] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 100 2 2
    _ = _ := by decide +kernel

private theorem span96_104 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 96 8 = (-70395584045663361412434429580538412728069009850814530907713019112479790162344 : ℤ) := by
  calc
    _ = (-19515978378168205950928556464237268403724748805189359372350520771864508610456 : ℤ) + (-50879605667495155461505873116301144324344261045625171535362498340615281551888 : ℤ) := by
      simpa only [Nat.reduceAdd, span96_100, span100_104] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 96 4 4
    _ = _ := by decide +kernel

private theorem span104_106 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 104 2 = (1247918256949948190766739455841463640598451620172521377133130075787788787392 : ℤ) := by
  calc
    _ = (-3617078359398853713849959890075242307830642412163443444801217104766252000104 : ℤ) + (4864996616348801904616699345916705948429094032335964821934347180554040787496 : ℤ) := by
      simpa only [Nat.reduceAdd, row104, row105] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 104 1 1
    _ = _ := by decide +kernel

private theorem span106_108 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 106 2 = (548752453022324727924884703345461268334566040743454643002949648109653536776 : ℤ) := by
  calc
    _ = (5342339508436658782485191013194677843917796273542949333256375953201057615072 : ℤ) + (-4793587055414334054560306309849216575583230232799494690253426305091404078296 : ℤ) := by
      simpa only [Nat.reduceAdd, row106, row107] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 106 1 1
    _ = _ := by decide +kernel

private theorem span104_108 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 104 4 = (1796670709972272918691624159186924908933017660915976020136079723897442324168 : ℤ) := by
  calc
    _ = (1247918256949948190766739455841463640598451620172521377133130075787788787392 : ℤ) + (548752453022324727924884703345461268334566040743454643002949648109653536776 : ℤ) := by
      simpa only [Nat.reduceAdd, span104_106, span106_108] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 104 2 2
    _ = _ := by decide +kernel

private theorem span108_110 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 108 2 = (-9240156960379304487529087069431296484400365992619535666221780724370807465632 : ℤ) := by
  calc
    _ = (225195690030713852767219963191919880888126847146540984162343623994539479072 : ℤ) + (-9465352650410018340296307032623216365288492839766076650384124348365346944704 : ℤ) := by
      simpa only [Nat.reduceAdd, row108, row109] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 108 1 1
    _ = _ := by decide +kernel

private theorem span110_112 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 110 2 = (-7900807987270005744591307843654738219109911639876990522054624252391395922272 : ℤ) := by
  calc
    _ = (-3029122425697265425163910634644662939843361273376802582476212751355405285144 : ℤ) + (-4871685561572740319427397209010075279266550366500187939578411501035990637128 : ℤ) := by
      simpa only [Nat.reduceAdd, row110, row111] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 110 1 1
    _ = _ := by decide +kernel

private theorem span108_112 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 108 4 = (-17140964947649310232120394913086034703510277632496526188276404976762203387904 : ℤ) := by
  calc
    _ = (-9240156960379304487529087069431296484400365992619535666221780724370807465632 : ℤ) + (-7900807987270005744591307843654738219109911639876990522054624252391395922272 : ℤ) := by
      simpa only [Nat.reduceAdd, span108_110, span110_112] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 108 2 2
    _ = _ := by decide +kernel

private theorem span104_112 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 104 8 = (-15344294237677037313428770753899109794577259971580550168140325252864761063736 : ℤ) := by
  calc
    _ = (1796670709972272918691624159186924908933017660915976020136079723897442324168 : ℤ) + (-17140964947649310232120394913086034703510277632496526188276404976762203387904 : ℤ) := by
      simpa only [Nat.reduceAdd, span104_108, span108_112] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 104 4 4
    _ = _ := by decide +kernel

private theorem span96_112 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 96 16 = (-85739878283340398725863200334437522522646269822395081075853344365344551226080 : ℤ) := by
  calc
    _ = (-70395584045663361412434429580538412728069009850814530907713019112479790162344 : ℤ) + (-15344294237677037313428770753899109794577259971580550168140325252864761063736 : ℤ) := by
      simpa only [Nat.reduceAdd, span96_104, span104_112] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 96 8 8
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows96To112 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 96 16 = (-85739878283340398725863200334437522522646269822395081075853344365344551226080 : ℤ) :=
  span96_112

#print axioms dottieFastReferenceRows96To112

end QuarticModel
