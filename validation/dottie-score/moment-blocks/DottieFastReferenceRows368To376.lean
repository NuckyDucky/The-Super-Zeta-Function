import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row368_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 368 =
    (0 : ℤ) := by decide +kernel

private theorem row368_block0 : dottiePairRowBlock dottieFastReferenceWeight 368 0 368 =
    (1725122733003168467080881804504554766411867795232127712340372311562906962752 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 368 0 368).symm.trans (by decide +kernel)

private theorem row368 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 368 1 = (1725122733003168467080881804504554766411867795232127712340372311562906962752 : ℤ) := by
  rw [dottiePairedRowSpan_one, row368_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 368 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 368 % 1024 = 368 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row368_block0]
  decide +kernel

private theorem row369_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 369 =
    (-72288895226457902268215015079152629544185044693158260420602728075686883712 : ℤ) := by decide +kernel

private theorem row369_block0 : dottiePairRowBlock dottieFastReferenceWeight 369 0 369 =
    (-295846609199670980221842408992089927363612819497899567970809830735152776744 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 369 0 369).symm.trans (by decide +kernel)

private theorem row369 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 369 1 = (-368135504426128882490057424071242556907797864191057828391412558810839660456 : ℤ) := by
  rw [dottiePairedRowSpan_one, row369_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 369 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 369 % 1024 = 369 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row369_block0]
  decide +kernel

private theorem row370_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 370 =
    (-339814600743889101054569080622222346064756532091100218879038411781478689920 : ℤ) := by decide +kernel

private theorem row370_block0 : dottiePairRowBlock dottieFastReferenceWeight 370 0 370 =
    (-3993999980129991490712548575772541334490775021172355351387736105840369327224 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 370 0 370).symm.trans (by decide +kernel)

private theorem row370 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 370 1 = (-4333814580873880591767117656394763680555531553263455570266774517621848017144 : ℤ) := by
  rw [dottiePairedRowSpan_one, row370_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 370 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 370 % 1024 = 370 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row370_block0]
  decide +kernel

private theorem row371_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 371 =
    (-331418101926536229522151494059135489208518777132829861547294583637423191408 : ℤ) := by decide +kernel

private theorem row371_block0 : dottiePairRowBlock dottieFastReferenceWeight 371 0 371 =
    (-2928672707520466013043932208391108152637689653306572907371674770872240622496 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 371 0 371).symm.trans (by decide +kernel)

private theorem row371 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 371 1 = (-3260090809447002242566083702450243641846208430439402768918969354509663813904 : ℤ) := by
  rw [dottiePairedRowSpan_one, row371_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 371 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 371 % 1024 = 371 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row371_block0]
  decide +kernel

private theorem row372_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 372 =
    (-63853741100650068838185126414110588933224431355061325468032233201644189696 : ℤ) := by decide +kernel

private theorem row372_block0 : dottiePairRowBlock dottieFastReferenceWeight 372 0 372 =
    (3790453966966343066063664638631224628620298367041327322036595344170301337280 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 372 0 372).symm.trans (by decide +kernel)

private theorem row372 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 372 1 = (3726600225865692997225479512217114039687073935686265996568563110968657147584 : ℤ) := by
  rw [dottiePairedRowSpan_one, row372_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 372 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 372 % 1024 = 372 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row372_block0]
  decide +kernel

private theorem row373_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 373 =
    (-223636482641858830640746037573368434559840764652694851105324676328080904016 : ℤ) := by decide +kernel

private theorem row373_block0 : dottiePairRowBlock dottieFastReferenceWeight 373 0 373 =
    (-6825930471021771342800834828003328743175419377954888126460254656981950604056 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 373 0 373).symm.trans (by decide +kernel)

private theorem row373 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 373 1 = (-7049566953663630173441580865576697177735260142607582977565579333310031508072 : ℤ) := by
  rw [dottiePairedRowSpan_one, row373_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 373 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 373 % 1024 = 373 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row373_block0]
  decide +kernel

private theorem row374_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 374 =
    (32414535300396896891636536373166475350918167302053933432127091905168194784 : ℤ) := by decide +kernel

private theorem row374_block0 : dottiePairRowBlock dottieFastReferenceWeight 374 0 374 =
    (3275307869978534078857963069499259117619883121979109418732934030312943599288 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 374 0 374).symm.trans (by decide +kernel)

private theorem row374 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 374 1 = (3307722405278930975749599605872425592970801289281163352165061122218111794072 : ℤ) := by
  rw [dottiePairedRowSpan_one, row374_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 374 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 374 % 1024 = 374 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row374_block0]
  decide +kernel

private theorem row375_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 375 =
    (39393466899729338233321707477726168136807504119406179500675042139121399680 : ℤ) := by decide +kernel

private theorem row375_block0 : dottiePairRowBlock dottieFastReferenceWeight 375 0 375 =
    (3422973103312872399769646933314998221977387711935418929666603944897176881960 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 375 0 375).symm.trans (by decide +kernel)

private theorem row375 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 375 1 = (3462366570212601738002968640792724390114195216054825109167278987036298281640 : ℤ) := by
  rw [dottiePairedRowSpan_one, row375_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 375 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 375 % 1024 = 375 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row375_block0]
  decide +kernel

private theorem span368_370 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 368 2 = (1356987228577039584590824380433312209504069931041069883948959752752067302296 : ℤ) := by
  calc
    _ = (1725122733003168467080881804504554766411867795232127712340372311562906962752 : ℤ) + (-368135504426128882490057424071242556907797864191057828391412558810839660456 : ℤ) := by
      simpa only [Nat.reduceAdd, row368, row369] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 368 1 1
    _ = _ := by decide +kernel

private theorem span370_372 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 370 2 = (-7593905390320882834333201358845007322401739983702858339185743872131511831048 : ℤ) := by
  calc
    _ = (-4333814580873880591767117656394763680555531553263455570266774517621848017144 : ℤ) + (-3260090809447002242566083702450243641846208430439402768918969354509663813904 : ℤ) := by
      simpa only [Nat.reduceAdd, row370, row371] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 370 1 1
    _ = _ := by decide +kernel

private theorem span368_372 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 368 4 = (-6236918161743843249742376978411695112897670052661788455236784119379444528752 : ℤ) := by
  calc
    _ = (1356987228577039584590824380433312209504069931041069883948959752752067302296 : ℤ) + (-7593905390320882834333201358845007322401739983702858339185743872131511831048 : ℤ) := by
      simpa only [Nat.reduceAdd, span368_370, span370_372] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 368 2 2
    _ = _ := by decide +kernel

private theorem span372_374 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 372 2 = (-3322966727797937176216101353359583138048186206921316980997016222341374360488 : ℤ) := by
  calc
    _ = (3726600225865692997225479512217114039687073935686265996568563110968657147584 : ℤ) + (-7049566953663630173441580865576697177735260142607582977565579333310031508072 : ℤ) := by
      simpa only [Nat.reduceAdd, row372, row373] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 372 1 1
    _ = _ := by decide +kernel

private theorem span374_376 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 374 2 = (6770088975491532713752568246665149983084996505335988461332340109254410075712 : ℤ) := by
  calc
    _ = (3307722405278930975749599605872425592970801289281163352165061122218111794072 : ℤ) + (3462366570212601738002968640792724390114195216054825109167278987036298281640 : ℤ) := by
      simpa only [Nat.reduceAdd, row374, row375] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 374 1 1
    _ = _ := by decide +kernel

private theorem span372_376 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 372 4 = (3447122247693595537536466893305566845036810298414671480335323886913035715224 : ℤ) := by
  calc
    _ = (-3322966727797937176216101353359583138048186206921316980997016222341374360488 : ℤ) + (6770088975491532713752568246665149983084996505335988461332340109254410075712 : ℤ) := by
      simpa only [Nat.reduceAdd, span372_374, span374_376] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 372 2 2
    _ = _ := by decide +kernel

private theorem span368_376 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 368 8 = (-2789795914050247712205910085106128267860859754247116974901460232466408813528 : ℤ) := by
  calc
    _ = (-6236918161743843249742376978411695112897670052661788455236784119379444528752 : ℤ) + (3447122247693595537536466893305566845036810298414671480335323886913035715224 : ℤ) := by
      simpa only [Nat.reduceAdd, span368_372, span372_376] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 368 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows368To376 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 368 8 = (-2789795914050247712205910085106128267860859754247116974901460232466408813528 : ℤ) :=
  span368_376

#print axioms dottieFastReferenceRows368To376

end QuarticModel
