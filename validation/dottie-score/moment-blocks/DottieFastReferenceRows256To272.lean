import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row256_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 256 =
    (423045783896948228804386038398707075530984065050989240853431491982800823936 : ℤ) := by decide +kernel

private theorem row256_block0 : dottiePairRowBlock dottieFastReferenceWeight 256 0 256 =
    (-6838116735746256257415783961748604919650689454793319680840491351903542778568 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 256 0 256).symm.trans (by decide +kernel)

private theorem row256 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 256 1 = (-6415070951849308028611397923349897844119705389742330439987059859920741954632 : ℤ) := by
  rw [dottiePairedRowSpan_one, row256_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 256 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 256 % 1024 = 256 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row256_block0]
  decide +kernel

private theorem row257_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 257 =
    (186188788031024035619633015744961431521681767878497313516053307737349965272 : ℤ) := by decide +kernel

private theorem row257_block0 : dottiePairRowBlock dottieFastReferenceWeight 257 0 257 =
    (-5713178050786584931599669481226883953654108681963672244785607155226934305472 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 257 0 257).symm.trans (by decide +kernel)

private theorem row257 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 257 1 = (-5526989262755560895980036465481922522132426914085174931269553847489584340200 : ℤ) := by
  rw [dottiePairedRowSpan_one, row257_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 257 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 257 % 1024 = 257 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row257_block0]
  decide +kernel

private theorem row258_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 258 =
    (-117673532047256035297872504085712364966629475896293670492995302073294252288 : ℤ) := by decide +kernel

private theorem row258_block0 : dottiePairRowBlock dottieFastReferenceWeight 258 0 258 =
    (-5029867177234614585674573659726959484669048136414168714132342271903019271472 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 258 0 258).symm.trans (by decide +kernel)

private theorem row258 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 258 1 = (-5147540709281870620972446163812671849635677612310462384625337573976313523760 : ℤ) := by
  rw [dottiePairedRowSpan_one, row258_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 258 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 258 % 1024 = 258 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row258_block0]
  decide +kernel

private theorem row259_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 259 =
    (353991938051293882815395459069203522240760762197512009267703829844427583112 : ℤ) := by decide +kernel

private theorem row259_block0 : dottiePairRowBlock dottieFastReferenceWeight 259 0 259 =
    (8894366091652845274943098873999623635359237957674323141973160936028871982472 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 259 0 259).symm.trans (by decide +kernel)

private theorem row259 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 259 1 = (9248358029704139157758494333068827157599998719871835151240864765873299565584 : ℤ) := by
  rw [dottiePairedRowSpan_one, row259_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 259 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 259 % 1024 = 259 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row259_block0]
  decide +kernel

private theorem row260_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 260 =
    (-481831646752258677862282206928655533246415806320408888534184909602801102888 : ℤ) := by decide +kernel

private theorem row260_block0 : dottiePairRowBlock dottieFastReferenceWeight 260 0 260 =
    (4160585411889308449276175667008179272742196383874362719482174329327844949928 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 260 0 260).symm.trans (by decide +kernel)

private theorem row260 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 260 1 = (3678753765137049771413893460079523739495780577553953830947989419725043847040 : ℤ) := by
  rw [dottiePairedRowSpan_one, row260_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 260 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 260 % 1024 = 260 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row260_block0]
  decide +kernel

private theorem row261_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 261 =
    (-427806116323689291245584584086923543313063027343804355336654484957905211688 : ℤ) := by decide +kernel

private theorem row261_block0 : dottiePairRowBlock dottieFastReferenceWeight 261 0 261 =
    (-6706141547292447904278725151200223848783644375262704514905425442603324508040 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 261 0 261).symm.trans (by decide +kernel)

private theorem row261 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 261 1 = (-7133947663616137195524309735287147392096707402606508870242079927561229719728 : ℤ) := by
  rw [dottiePairedRowSpan_one, row261_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 261 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 261 % 1024 = 261 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row261_block0]
  decide +kernel

private theorem row262_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 262 =
    (483704769036576107839828824506788520336542548002145562841490344275614120664 : ℤ) := by decide +kernel

private theorem row262_block0 : dottiePairRowBlock dottieFastReferenceWeight 262 0 262 =
    (7932519469396832110973452625011266141856877402733217004137833306853430140392 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 262 0 262).symm.trans (by decide +kernel)

private theorem row262 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 262 1 = (8416224238433408218813281449518054662193419950735362566979323651129044261056 : ℤ) := by
  rw [dottiePairedRowSpan_one, row262_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 262 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 262 % 1024 = 262 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row262_block0]
  decide +kernel

private theorem row263_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 263 =
    (-255816542195606298121943027066064052427297370552625327289867611805917658880 : ℤ) := by decide +kernel

private theorem row263_block0 : dottiePairRowBlock dottieFastReferenceWeight 263 0 263 =
    (1950664910573030553560143467710753737540916085128926607725956175532238932176 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 263 0 263).symm.trans (by decide +kernel)

private theorem row263 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 263 1 = (1694848368377424255438200440644689685113618714576301280436088563726321273296 : ℤ) := by
  rw [dottiePairedRowSpan_one, row263_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 263 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 263 % 1024 = 263 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row263_block0]
  decide +kernel

private theorem row264_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 264 =
    (465667347838674579780329413839556128620768221120292491251063627654702324104 : ℤ) := by decide +kernel

private theorem row264_block0 : dottiePairRowBlock dottieFastReferenceWeight 264 0 264 =
    (-8527016682312620198862734268631984679703224641100929620014868747854730948456 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 264 0 264).symm.trans (by decide +kernel)

private theorem row264 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 264 1 = (-8061349334473945619082404854792428551082456419980637128763805120200028624352 : ℤ) := by
  rw [dottiePairedRowSpan_one, row264_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 264 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 264 % 1024 = 264 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row264_block0]
  decide +kernel

private theorem row265_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 265 =
    (-477963922791474448486142313454799007389602969511024199822689411806534806632 : ℤ) := by decide +kernel

private theorem row265_block0 : dottiePairRowBlock dottieFastReferenceWeight 265 0 265 =
    (-6295788773286919306239623399325384349607822193345894977638437934971656396824 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 265 0 265).symm.trans (by decide +kernel)

private theorem row265 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 265 1 = (-6773752696078393754725765712780183356997425162856919177461127346778191203456 : ℤ) := by
  rw [dottiePairedRowSpan_one, row265_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 265 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 265 % 1024 = 265 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row265_block0]
  decide +kernel

private theorem row266_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 266 =
    (-446117570190893323103672062001195663195342491177904628869794036517234826808 : ℤ) := by decide +kernel

private theorem row266_block0 : dottiePairRowBlock dottieFastReferenceWeight 266 0 266 =
    (-2259881561520070255397537898424859857221412968091189524462507266578854006056 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 266 0 266).symm.trans (by decide +kernel)

private theorem row266 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 266 1 = (-2705999131710963578501209960426055520416755459269094153332301303096088832864 : ℤ) := by
  rw [dottiePairedRowSpan_one, row266_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 266 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 266 % 1024 = 266 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row266_block0]
  decide +kernel

private theorem row267_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 267 =
    (392942268592683878082341673830528611374253157646982206425600123422727312968 : ℤ) := by decide +kernel

private theorem row267_block0 : dottiePairRowBlock dottieFastReferenceWeight 267 0 267 =
    (7772606968704234697691027945308141350480672624120735921129153943493997481440 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 267 0 267).symm.trans (by decide +kernel)

private theorem row267 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 267 1 = (8165549237296918575773369619138669961854925781767718127554754066916724794408 : ℤ) := by
  rw [dottiePairedRowSpan_one, row267_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 267 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 267 % 1024 = 267 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row267_block0]
  decide +kernel

private theorem row268_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 268 =
    (251781680772390170417503874505121770528222347413057749149691565762076670336 : ℤ) := by decide +kernel

private theorem row268_block0 : dottiePairRowBlock dottieFastReferenceWeight 268 0 268 =
    (524433962780945433522793693983066157436314454721465403948178412966048303560 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 268 0 268).symm.trans (by decide +kernel)

private theorem row268 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 268 1 = (776215643553335603940297568488187927964536802134523153097869978728124973896 : ℤ) := by
  rw [dottiePairedRowSpan_one, row268_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 268 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 268 % 1024 = 268 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row268_block0]
  decide +kernel

private theorem row269_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 269 =
    (372719832255057490387730314782056516753911033508598673365270595776207432832 : ℤ) := by decide +kernel

private theorem row269_block0 : dottiePairRowBlock dottieFastReferenceWeight 269 0 269 =
    (-3324434348500779441810788919290646646693358987996028583202014379560369453560 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 269 0 269).symm.trans (by decide +kernel)

private theorem row269 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 269 1 = (-2951714516245721951423058604508590129939447954487429909836743783784162020728 : ℤ) := by
  rw [dottiePairedRowSpan_one, row269_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 269 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 269 % 1024 = 269 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row269_block0]
  decide +kernel

private theorem row270_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 270 =
    (419532216752979895235991244753130425266451655765438902620453654911270503624 : ℤ) := by decide +kernel

private theorem row270_block0 : dottiePairRowBlock dottieFastReferenceWeight 270 0 270 =
    (6643498673366245949398706923658454612907539298783512383988718704692217357640 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 270 0 270).symm.trans (by decide +kernel)

private theorem row270 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 270 1 = (7063030890119225844634698168411585038173990954548951286609172359603487861264 : ℤ) := by
  rw [dottiePairedRowSpan_one, row270_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 270 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 270 % 1024 = 270 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row270_block0]
  decide +kernel

private theorem row271_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 271 =
    (-463900258298338473076053991447101471304901618960919516561147967884045886816 : ℤ) := by decide +kernel

private theorem row271_block0 : dottiePairRowBlock dottieFastReferenceWeight 271 0 271 =
    (-6314813973663863625938181843075073389006483227465931613769347910837904225952 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 271 0 271).symm.trans (by decide +kernel)

private theorem row271 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 271 1 = (-6778714231962202099014235834522174860311384846426851130330495878721950112768 : ℤ) := by
  rw [dottiePairedRowSpan_one, row271_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 271 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 271 % 1024 = 271 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row271_block0]
  decide +kernel

private theorem span256_258 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 256 2 = (-11942060214604868924591434388831820366252132303827505371256613707410326294832 : ℤ) := by
  calc
    _ = (-6415070951849308028611397923349897844119705389742330439987059859920741954632 : ℤ) + (-5526989262755560895980036465481922522132426914085174931269553847489584340200 : ℤ) := by
      simpa only [Nat.reduceAdd, row256, row257] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 256 1 1
    _ = _ := by decide +kernel

private theorem span258_260 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 258 2 = (4100817320422268536786048169256155307964321107561372766615527191896986041824 : ℤ) := by
  calc
    _ = (-5147540709281870620972446163812671849635677612310462384625337573976313523760 : ℤ) + (9248358029704139157758494333068827157599998719871835151240864765873299565584 : ℤ) := by
      simpa only [Nat.reduceAdd, row258, row259] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 258 1 1
    _ = _ := by decide +kernel

private theorem span256_260 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 256 4 = (-7841242894182600387805386219575665058287811196266132604641086515513340253008 : ℤ) := by
  calc
    _ = (-11942060214604868924591434388831820366252132303827505371256613707410326294832 : ℤ) + (4100817320422268536786048169256155307964321107561372766615527191896986041824 : ℤ) := by
      simpa only [Nat.reduceAdd, span256_258, span258_260] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 256 2 2
    _ = _ := by decide +kernel

private theorem span260_262 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 260 2 = (-3455193898479087424110416275207623652600926825052555039294090507836185872688 : ℤ) := by
  calc
    _ = (3678753765137049771413893460079523739495780577553953830947989419725043847040 : ℤ) + (-7133947663616137195524309735287147392096707402606508870242079927561229719728 : ℤ) := by
      simpa only [Nat.reduceAdd, row260, row261] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 260 1 1
    _ = _ := by decide +kernel

private theorem span262_264 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 262 2 = (10111072606810832474251481890162744347307038665311663847415412214855365534352 : ℤ) := by
  calc
    _ = (8416224238433408218813281449518054662193419950735362566979323651129044261056 : ℤ) + (1694848368377424255438200440644689685113618714576301280436088563726321273296 : ℤ) := by
      simpa only [Nat.reduceAdd, row262, row263] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 262 1 1
    _ = _ := by decide +kernel

private theorem span260_264 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 260 4 = (6655878708331745050141065614955120694706111840259108808121321707019179661664 : ℤ) := by
  calc
    _ = (-3455193898479087424110416275207623652600926825052555039294090507836185872688 : ℤ) + (10111072606810832474251481890162744347307038665311663847415412214855365534352 : ℤ) := by
      simpa only [Nat.reduceAdd, span260_262, span262_264] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 260 2 2
    _ = _ := by decide +kernel

private theorem span256_264 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 256 8 = (-1185364185850855337664320604620544363581699356007023796519764808494160591344 : ℤ) := by
  calc
    _ = (-7841242894182600387805386219575665058287811196266132604641086515513340253008 : ℤ) + (6655878708331745050141065614955120694706111840259108808121321707019179661664 : ℤ) := by
      simpa only [Nat.reduceAdd, span256_260, span260_264] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 256 4 4
    _ = _ := by decide +kernel

private theorem span264_266 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 264 2 = (-14835102030552339373808170567572611908079881582837556306224932466978219827808 : ℤ) := by
  calc
    _ = (-8061349334473945619082404854792428551082456419980637128763805120200028624352 : ℤ) + (-6773752696078393754725765712780183356997425162856919177461127346778191203456 : ℤ) := by
      simpa only [Nat.reduceAdd, row264, row265] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 264 1 1
    _ = _ := by decide +kernel

private theorem span266_268 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 266 2 = (5459550105585954997272159658712614441438170322498623974222452763820635961544 : ℤ) := by
  calc
    _ = (-2705999131710963578501209960426055520416755459269094153332301303096088832864 : ℤ) + (8165549237296918575773369619138669961854925781767718127554754066916724794408 : ℤ) := by
      simpa only [Nat.reduceAdd, row266, row267] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 266 1 1
    _ = _ := by decide +kernel

private theorem span264_268 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 264 4 = (-9375551924966384376536010908859997466641711260338932332002479703157583866264 : ℤ) := by
  calc
    _ = (-14835102030552339373808170567572611908079881582837556306224932466978219827808 : ℤ) + (5459550105585954997272159658712614441438170322498623974222452763820635961544 : ℤ) := by
      simpa only [Nat.reduceAdd, span264_266, span266_268] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 264 2 2
    _ = _ := by decide +kernel

private theorem span268_270 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 268 2 = (-2175498872692386347482761036020402201974911152352906756738873805056037046832 : ℤ) := by
  calc
    _ = (776215643553335603940297568488187927964536802134523153097869978728124973896 : ℤ) + (-2951714516245721951423058604508590129939447954487429909836743783784162020728 : ℤ) := by
      simpa only [Nat.reduceAdd, row268, row269] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 268 1 1
    _ = _ := by decide +kernel

private theorem span270_272 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 270 2 = (284316658157023745620462333889410177862606108122100156278676480881537748496 : ℤ) := by
  calc
    _ = (7063030890119225844634698168411585038173990954548951286609172359603487861264 : ℤ) + (-6778714231962202099014235834522174860311384846426851130330495878721950112768 : ℤ) := by
      simpa only [Nat.reduceAdd, row270, row271] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 270 1 1
    _ = _ := by decide +kernel

private theorem span268_272 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 268 4 = (-1891182214535362601862298702130992024112305044230806600460197324174499298336 : ℤ) := by
  calc
    _ = (-2175498872692386347482761036020402201974911152352906756738873805056037046832 : ℤ) + (284316658157023745620462333889410177862606108122100156278676480881537748496 : ℤ) := by
      simpa only [Nat.reduceAdd, span268_270, span270_272] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 268 2 2
    _ = _ := by decide +kernel

private theorem span264_272 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 264 8 = (-11266734139501746978398309610990989490754016304569738932462677027332083164600 : ℤ) := by
  calc
    _ = (-9375551924966384376536010908859997466641711260338932332002479703157583866264 : ℤ) + (-1891182214535362601862298702130992024112305044230806600460197324174499298336 : ℤ) := by
      simpa only [Nat.reduceAdd, span264_268, span268_272] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 264 4 4
    _ = _ := by decide +kernel

private theorem span256_272 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 256 16 = (-12452098325352602316062630215611533854335715660576762728982441835826243755944 : ℤ) := by
  calc
    _ = (-1185364185850855337664320604620544363581699356007023796519764808494160591344 : ℤ) + (-11266734139501746978398309610990989490754016304569738932462677027332083164600 : ℤ) := by
      simpa only [Nat.reduceAdd, span256_264, span264_272] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 256 8 8
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows256To272 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 256 16 = (-12452098325352602316062630215611533854335715660576762728982441835826243755944 : ℤ) :=
  span256_272

#print axioms dottieFastReferenceRows256To272

end QuarticModel
