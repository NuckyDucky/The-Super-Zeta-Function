import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row384_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 384 =
    (-35804025689758704116225799718998058293592816392156736853789869751174853344 : ℤ) := by decide +kernel

private theorem row384_block0 : dottiePairRowBlock dottieFastReferenceWeight 384 0 384 =
    (-5803382723175978958440520069573659325280341388699289362295861729901633584128 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 384 0 384).symm.trans (by decide +kernel)

private theorem row384 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 384 1 = (-5839186748865737662556745869292657383573934205091446099149651599652808437472 : ℤ) := by
  rw [dottiePairedRowSpan_one, row384_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 384 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 384 % 1024 = 384 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row384_block0]
  decide +kernel

private theorem row385_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 385 =
    (-267147834648328294310950195438876364428315573327243261985386026711351014400 : ℤ) := by decide +kernel

private theorem row385_block0 : dottiePairRowBlock dottieFastReferenceWeight 385 0 385 =
    (-2024958942294379317156981877318295923315036020515675859832102262036951374200 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 385 0 385).symm.trans (by decide +kernel)

private theorem row385 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 385 1 = (-2292106776942707611467932072757172287743351593842919121817488288748302388600 : ℤ) := by
  rw [dottiePairedRowSpan_one, row385_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 385 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 385 % 1024 = 385 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row385_block0]
  decide +kernel

private theorem row386_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 386 =
    (-176224475736237087376171775152326939513407031949020814190281528909927916160 : ℤ) := by decide +kernel

private theorem row386_block0 : dottiePairRowBlock dottieFastReferenceWeight 386 0 386 =
    (3319380042399366416766398846246086774872846152807214114841637705772068266560 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 386 0 386).symm.trans (by decide +kernel)

private theorem row386 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 386 1 = (3143155566663129329390227071093759835359439120858193300651356176862140350400 : ℤ) := by
  rw [dottiePairedRowSpan_one, row386_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 386 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 386 % 1024 = 386 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row386_block0]
  decide +kernel

private theorem row387_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 387 =
    (327584520141631024108145443064392697241855590759144904580191872600014661000 : ℤ) := by decide +kernel

private theorem row387_block0 : dottiePairRowBlock dottieFastReferenceWeight 387 0 387 =
    (-81148336203273786739026791095287838880154129464231421409528977454033591416 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 387 0 387).symm.trans (by decide +kernel)

private theorem row387 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 387 1 = (246436183938357237369118651969104858361701461294913483170662895145981069584 : ℤ) := by
  rw [dottiePairedRowSpan_one, row387_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 387 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 387 % 1024 = 387 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row387_block0]
  decide +kernel

private theorem row388_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 388 =
    (142195061964985990889753889853797631722000280003062399253117912464776353152 : ℤ) := by decide +kernel

private theorem row388_block0 : dottiePairRowBlock dottieFastReferenceWeight 388 0 388 =
    (-7960770825257399763182222423932543628738179567173774028564607350421993459640 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 388 0 388).symm.trans (by decide +kernel)

private theorem row388 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 388 1 = (-7818575763292413772292468534078745997016179287170711629311489437957217106488 : ℤ) := by
  rw [dottiePairedRowSpan_one, row388_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 388 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 388 % 1024 = 388 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row388_block0]
  decide +kernel

private theorem row389_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 389 =
    (-192225423770897164747229181866775655190430576997547080227711606712887631616 : ℤ) := by decide +kernel

private theorem row389_block0 : dottiePairRowBlock dottieFastReferenceWeight 389 0 389 =
    (-2663183747593543105150892618407712618813686547485372058263441527609407529008 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 389 0 389).symm.trans (by decide +kernel)

private theorem row389 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 389 1 = (-2855409171364440269898121800274488274004117124482919138491153134322295160624 : ℤ) := by
  rw [dottiePairedRowSpan_one, row389_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 389 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 389 % 1024 = 389 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row389_block0]
  decide +kernel

private theorem row390_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 390 =
    (-150559663593721574671268613778137650494123543991926662995071635487726940224 : ℤ) := by decide +kernel

private theorem row390_block0 : dottiePairRowBlock dottieFastReferenceWeight 390 0 390 =
    (-14299567228904973697117525219481543563421978409394451502204532682642320032032 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 390 0 390).symm.trans (by decide +kernel)

private theorem row390 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 390 1 = (-14450126892498695271788793833259681213916101953386378165199604318130046972256 : ℤ) := by
  rw [dottiePairedRowSpan_one, row390_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 390 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 390 % 1024 = 390 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row390_block0]
  decide +kernel

private theorem row391_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 391 =
    (139854101604188903166217248859832990754612782261404926200451313772305471488 : ℤ) := by decide +kernel

private theorem row391_block0 : dottiePairRowBlock dottieFastReferenceWeight 391 0 391 =
    (-1109483412028434830504263580848001072251803072761059259211362769832822387992 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 391 0 391).symm.trans (by decide +kernel)

private theorem row391 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 391 1 = (-969629310424245927338046331988168081497190290499654333010911456060516916504 : ℤ) := by
  rw [dottiePairedRowSpan_one, row391_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 391 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 391 % 1024 = 391 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row391_block0]
  decide +kernel

private theorem span384_386 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 384 2 = (-8131293525808445274024677942049829671317285798934365220967139888401110826072 : ℤ) := by
  calc
    _ = (-5839186748865737662556745869292657383573934205091446099149651599652808437472 : ℤ) + (-2292106776942707611467932072757172287743351593842919121817488288748302388600 : ℤ) := by
      simpa only [Nat.reduceAdd, row384, row385] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 384 1 1
    _ = _ := by decide +kernel

private theorem span386_388 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 386 2 = (3389591750601486566759345723062864693721140582153106783822019072008121419984 : ℤ) := by
  calc
    _ = (3143155566663129329390227071093759835359439120858193300651356176862140350400 : ℤ) + (246436183938357237369118651969104858361701461294913483170662895145981069584 : ℤ) := by
      simpa only [Nat.reduceAdd, row386, row387] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 386 1 1
    _ = _ := by decide +kernel

private theorem span384_388 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 384 4 = (-4741701775206958707265332218986964977596145216781258437145120816392989406088 : ℤ) := by
  calc
    _ = (-8131293525808445274024677942049829671317285798934365220967139888401110826072 : ℤ) + (3389591750601486566759345723062864693721140582153106783822019072008121419984 : ℤ) := by
      simpa only [Nat.reduceAdd, span384_386, span386_388] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 384 2 2
    _ = _ := by decide +kernel

private theorem span388_390 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 388 2 = (-10673984934656854042190590334353234271020296411653630767802642572279512267112 : ℤ) := by
  calc
    _ = (-7818575763292413772292468534078745997016179287170711629311489437957217106488 : ℤ) + (-2855409171364440269898121800274488274004117124482919138491153134322295160624 : ℤ) := by
      simpa only [Nat.reduceAdd, row388, row389] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 388 1 1
    _ = _ := by decide +kernel

private theorem span390_392 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 390 2 = (-15419756202922941199126840165247849295413292243886032498210515774190563888760 : ℤ) := by
  calc
    _ = (-14450126892498695271788793833259681213916101953386378165199604318130046972256 : ℤ) + (-969629310424245927338046331988168081497190290499654333010911456060516916504 : ℤ) := by
      simpa only [Nat.reduceAdd, row390, row391] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 390 1 1
    _ = _ := by decide +kernel

private theorem span388_392 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 388 4 = (-26093741137579795241317430499601083566433588655539663266013158346470076155872 : ℤ) := by
  calc
    _ = (-10673984934656854042190590334353234271020296411653630767802642572279512267112 : ℤ) + (-15419756202922941199126840165247849295413292243886032498210515774190563888760 : ℤ) := by
      simpa only [Nat.reduceAdd, span388_390, span390_392] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 388 2 2
    _ = _ := by decide +kernel

private theorem span384_392 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 384 8 = (-30835442912786753948582762718588048544029733872320921703158279162863065561960 : ℤ) := by
  calc
    _ = (-4741701775206958707265332218986964977596145216781258437145120816392989406088 : ℤ) + (-26093741137579795241317430499601083566433588655539663266013158346470076155872 : ℤ) := by
      simpa only [Nat.reduceAdd, span384_388, span388_392] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 384 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows384To392 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 384 8 = (-30835442912786753948582762718588048544029733872320921703158279162863065561960 : ℤ) :=
  span384_392

#print axioms dottieFastReferenceRows384To392

end QuarticModel
