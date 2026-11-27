import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row360_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 360 =
    (-287886860149657533647780853764483152267131090493880491183944721539404164600 : ℤ) := by decide +kernel

private theorem row360_block0 : dottiePairRowBlock dottieFastReferenceWeight 360 0 360 =
    (1530497948743922041387862590407458025729624993684199930274477458459095182392 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 360 0 360).symm.trans (by decide +kernel)

private theorem row360 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 360 1 = (1242611088594264507740081736642974873462493903190319439090532736919691017792 : ℤ) := by
  rw [dottiePairedRowSpan_one, row360_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 360 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 360 % 1024 = 360 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row360_block0]
  decide +kernel

private theorem row361_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 361 =
    (-344073404741206028023579782089504193230640025498695377851818287945312752656 : ℤ) := by decide +kernel

private theorem row361_block0 : dottiePairRowBlock dottieFastReferenceWeight 361 0 361 =
    (9284580060125495341873086979095557343372889657049863743139814897828805771600 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 361 0 361).symm.trans (by decide +kernel)

private theorem row361 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 361 1 = (8940506655384289313849507197006053150142249631551168365287996609883493018944 : ℤ) := by
  rw [dottiePairedRowSpan_one, row361_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 361 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 361 % 1024 = 361 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row361_block0]
  decide +kernel

private theorem row362_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 362 =
    (-336070111777037732280665191506954249923594918436258053095736942021923956512 : ℤ) := by decide +kernel

private theorem row362_block0 : dottiePairRowBlock dottieFastReferenceWeight 362 0 362 =
    (-5837045312898709079337570479272324498694819750628555030960319231841933145704 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 362 0 362).symm.trans (by decide +kernel)

private theorem row362 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 362 1 = (-6173115424675746811618235670779278748618414669064813084056056173863857102216 : ℤ) := by
  rw [dottiePairedRowSpan_one, row362_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 362 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 362 % 1024 = 362 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row362_block0]
  decide +kernel

private theorem row363_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 363 =
    (-143486093002917805791429673950236052351114736165880880714943670731516891864 : ℤ) := by decide +kernel

private theorem row363_block0 : dottiePairRowBlock dottieFastReferenceWeight 363 0 363 =
    (-1533393059622796527607239826876508775406962455341494828751267774793872071528 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 363 0 363).symm.trans (by decide +kernel)

private theorem row363 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 363 1 = (-1676879152625714333398669500826744827758077191507375709466211445525388963392 : ℤ) := by
  rw [dottiePairedRowSpan_one, row363_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 363 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 363 % 1024 = 363 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row363_block0]
  decide +kernel

private theorem row364_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 364 =
    (279166308402270216950179722028781781950365484093878921485310081992357422136 : ℤ) := by decide +kernel

private theorem row364_block0 : dottiePairRowBlock dottieFastReferenceWeight 364 0 364 =
    (2099611528825733778747531133887657356353199711404208182556432307116484466520 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 364 0 364).symm.trans (by decide +kernel)

private theorem row364 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 364 1 = (2378777837228003995697710855916439138303565195498087104041742389108841888656 : ℤ) := by
  rw [dottiePairedRowSpan_one, row364_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 364 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 364 % 1024 = 364 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row364_block0]
  decide +kernel

private theorem row365_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 365 =
    (346704795250865087458108245109577971690677037056216383071546293621508414464 : ℤ) := by decide +kernel

private theorem row365_block0 : dottiePairRowBlock dottieFastReferenceWeight 365 0 365 =
    (-2346556954796640044115373586126158158847657184874234871939600713142651327344 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 365 0 365).symm.trans (by decide +kernel)

private theorem row365 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 365 1 = (-1999852159545774956657265341016580187156980147818018488868054419521142912880 : ℤ) := by
  rw [dottiePairedRowSpan_one, row365_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 365 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 365 % 1024 = 365 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row365_block0]
  decide +kernel

private theorem row366_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 366 =
    (-11522802989062534849100613263479374604382171723653143659925917529924742016 : ℤ) := by decide +kernel

private theorem row366_block0 : dottiePairRowBlock dottieFastReferenceWeight 366 0 366 =
    (-2021942966137129645114753684155360956600504810659323925492933401637152773080 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 366 0 366).symm.trans (by decide +kernel)

private theorem row366 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 366 1 = (-2033465769126192179963854297418840331204886982382977069152859319167077515096 : ℤ) := by
  rw [dottiePairedRowSpan_one, row366_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 366 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 366 % 1024 = 366 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row366_block0]
  decide +kernel

private theorem row367_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 367 =
    (-296969602258540447942561781319025971293664975176015861112443534760608727984 : ℤ) := by decide +kernel

private theorem row367_block0 : dottiePairRowBlock dottieFastReferenceWeight 367 0 367 =
    (-11095653969390640093382711349586702683527276531047234606863152163728947187872 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 367 0 367).symm.trans (by decide +kernel)

private theorem row367 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 367 1 = (-11392623571649180541325273130905728654820941506223250467975595698489555915856 : ℤ) := by
  rw [dottiePairedRowSpan_one, row367_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 367 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 367 % 1024 = 367 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row367_block0]
  decide +kernel

private theorem span360_362 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 360 2 = (10183117743978553821589588933649028023604743534741487804378529346803184036736 : ℤ) := by
  calc
    _ = (1242611088594264507740081736642974873462493903190319439090532736919691017792 : ℤ) + (8940506655384289313849507197006053150142249631551168365287996609883493018944 : ℤ) := by
      simpa only [Nat.reduceAdd, row360, row361] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 360 1 1
    _ = _ := by decide +kernel

private theorem span362_364 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 362 2 = (-7849994577301461145016905171606023576376491860572188793522267619389246065608 : ℤ) := by
  calc
    _ = (-6173115424675746811618235670779278748618414669064813084056056173863857102216 : ℤ) + (-1676879152625714333398669500826744827758077191507375709466211445525388963392 : ℤ) := by
      simpa only [Nat.reduceAdd, row362, row363] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 362 1 1
    _ = _ := by decide +kernel

private theorem span360_364 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 360 4 = (2333123166677092676572683762043004447228251674169299010856261727413937971128 : ℤ) := by
  calc
    _ = (10183117743978553821589588933649028023604743534741487804378529346803184036736 : ℤ) + (-7849994577301461145016905171606023576376491860572188793522267619389246065608 : ℤ) := by
      simpa only [Nat.reduceAdd, span360_362, span362_364] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 360 2 2
    _ = _ := by decide +kernel

private theorem span364_366 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 364 2 = (378925677682229039040445514899858951146585047680068615173687969587698975776 : ℤ) := by
  calc
    _ = (2378777837228003995697710855916439138303565195498087104041742389108841888656 : ℤ) + (-1999852159545774956657265341016580187156980147818018488868054419521142912880 : ℤ) := by
      simpa only [Nat.reduceAdd, row364, row365] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 364 1 1
    _ = _ := by decide +kernel

private theorem span366_368 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 366 2 = (-13426089340775372721289127428324568986025828488606227537128455017656633430952 : ℤ) := by
  calc
    _ = (-2033465769126192179963854297418840331204886982382977069152859319167077515096 : ℤ) + (-11392623571649180541325273130905728654820941506223250467975595698489555915856 : ℤ) := by
      simpa only [Nat.reduceAdd, row366, row367] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 366 1 1
    _ = _ := by decide +kernel

private theorem span364_368 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 364 4 = (-13047163663093143682248681913424710034879243440926158921954767048068934455176 : ℤ) := by
  calc
    _ = (378925677682229039040445514899858951146585047680068615173687969587698975776 : ℤ) + (-13426089340775372721289127428324568986025828488606227537128455017656633430952 : ℤ) := by
      simpa only [Nat.reduceAdd, span364_366, span366_368] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 364 2 2
    _ = _ := by decide +kernel

private theorem span360_368 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 360 8 = (-10714040496416051005675998151381705587650991766756859911098505320654996484048 : ℤ) := by
  calc
    _ = (2333123166677092676572683762043004447228251674169299010856261727413937971128 : ℤ) + (-13047163663093143682248681913424710034879243440926158921954767048068934455176 : ℤ) := by
      simpa only [Nat.reduceAdd, span360_364, span364_368] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 360 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows360To368 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 360 8 = (-10714040496416051005675998151381705587650991766756859911098505320654996484048 : ℤ) :=
  span360_368

#print axioms dottieFastReferenceRows360To368

end QuarticModel
