import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row336_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 336 =
    (175071014728263745314663798905098724372489783115260584969930975186944922640 : ℤ) := by decide +kernel

private theorem row336_block0 : dottiePairRowBlock dottieFastReferenceWeight 336 0 336 =
    (-6402707400340801901967688694474668006860016419547164395842925230445323231840 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 336 0 336).symm.trans (by decide +kernel)

private theorem row336 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 336 1 = (-6227636385612538156653024895569569282487526636431903810872994255258378309200 : ℤ) := by
  rw [dottiePairedRowSpan_one, row336_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 336 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 336 % 1024 = 336 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row336_block0]
  decide +kernel

private theorem row337_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 337 =
    (146771348273475737406279479822124899097906963161096962022752132489949393480 : ℤ) := by decide +kernel

private theorem row337_block0 : dottiePairRowBlock dottieFastReferenceWeight 337 0 337 =
    (-2598650434837297351799508421688936334271201136367539077883070674346820773648 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 337 0 337).symm.trans (by decide +kernel)

private theorem row337 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 337 1 = (-2451879086563821614393228941866811435173294173206442115860318541856871380168 : ℤ) := by
  rw [dottiePairedRowSpan_one, row337_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 337 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 337 % 1024 = 337 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row337_block0]
  decide +kernel

private theorem row338_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 338 =
    (87510174529272292416823625902152911317136221456385351066880028850002591744 : ℤ) := by decide +kernel

private theorem row338_block0 : dottiePairRowBlock dottieFastReferenceWeight 338 0 338 =
    (-942183631706594893801166367527658961988423669626574421988589485897964049240 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 338 0 338).symm.trans (by decide +kernel)

private theorem row338 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 338 1 = (-854673457177322601384342741625506050671287448170189070921709457047961457496 : ℤ) := by
  rw [dottiePairedRowSpan_one, row338_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 338 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 338 % 1024 = 338 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row338_block0]
  decide +kernel

private theorem row339_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 339 =
    (-112723556606427464251743054378345939499120702219789411887883187552420977408 : ℤ) := by decide +kernel

private theorem row339_block0 : dottiePairRowBlock dottieFastReferenceWeight 339 0 339 =
    (-55829625679294791469338267108738912781561326028202352916314974265293635456 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 339 0 339).symm.trans (by decide +kernel)

private theorem row339 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 339 1 = (-168553182285722255721081321487084852280682028247991764804198161817714612864 : ℤ) := by
  rw [dottiePairedRowSpan_one, row339_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 339 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 339 % 1024 = 339 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row339_block0]
  decide +kernel

private theorem row340_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 340 =
    (357389800580572870385316478480250034752233102297382915122369116729641540480 : ℤ) := by decide +kernel

private theorem row340_block0 : dottiePairRowBlock dottieFastReferenceWeight 340 0 340 =
    (4593823205690398402527644251795796241868682554658688494015273847808392314824 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 340 0 340).symm.trans (by decide +kernel)

private theorem row340 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 340 1 = (4951213006270971272912960730276046276620915656956071409137642964538033855304 : ℤ) := by
  rw [dottiePairedRowSpan_one, row340_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 340 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 340 % 1024 = 340 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row340_block0]
  decide +kernel

private theorem row341_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 341 =
    (163939487858008840008980391107081788788168952831281383723456850769557161344 : ℤ) := by decide +kernel

private theorem row341_block0 : dottiePairRowBlock dottieFastReferenceWeight 341 0 341 =
    (-4847090497695113304492886468738635310950607717778473263406289862134160142152 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 341 0 341).symm.trans (by decide +kernel)

private theorem row341 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 341 1 = (-4683151009837104464483906077631553522162438764947191879682833011364602980808 : ℤ) := by
  rw [dottiePairedRowSpan_one, row341_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 341 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 341 % 1024 = 341 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row341_block0]
  decide +kernel

private theorem row342_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 342 =
    (-226932990781560288580855044079225147621147465042016473256639906150112076064 : ℤ) := by decide +kernel

private theorem row342_block0 : dottiePairRowBlock dottieFastReferenceWeight 342 0 342 =
    (-4473476774121355679946161966920950014121802662391527180726510733952743861376 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 342 0 342).symm.trans (by decide +kernel)

private theorem row342 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 342 1 = (-4700409764902915968527017011000175161742950127433543653983150640102855937440 : ℤ) := by
  rw [dottiePairedRowSpan_one, row342_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 342 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 342 % 1024 = 342 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row342_block0]
  decide +kernel

private theorem row343_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 343 =
    (216205365567190479691643763598249754724629846691260208305678022000893037952 : ℤ) := by decide +kernel

private theorem row343_block0 : dottiePairRowBlock dottieFastReferenceWeight 343 0 343 =
    (-8803004163448728234320304786675546743062566163446173404153361372305175457192 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 343 0 343).symm.trans (by decide +kernel)

private theorem row343 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 343 1 = (-8586798797881537754628661023077296988337936316754913195847683350304282419240 : ℤ) := by
  rw [dottiePairedRowSpan_one, row343_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 343 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 343 % 1024 = 343 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row343_block0]
  decide +kernel

private theorem span336_338 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 336 2 = (-8679515472176359771046253837436380717660820809638345926733312797115249689368 : ℤ) := by
  calc
    _ = (-6227636385612538156653024895569569282487526636431903810872994255258378309200 : ℤ) + (-2451879086563821614393228941866811435173294173206442115860318541856871380168 : ℤ) := by
      simpa only [Nat.reduceAdd, row336, row337] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 336 1 1
    _ = _ := by decide +kernel

private theorem span338_340 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 338 2 = (-1023226639463044857105424063112590902951969476418180835725907618865676070360 : ℤ) := by
  calc
    _ = (-854673457177322601384342741625506050671287448170189070921709457047961457496 : ℤ) + (-168553182285722255721081321487084852280682028247991764804198161817714612864 : ℤ) := by
      simpa only [Nat.reduceAdd, row338, row339] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 338 1 1
    _ = _ := by decide +kernel

private theorem span336_340 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 336 4 = (-9702742111639404628151677900548971620612790286056526762459220415980925759728 : ℤ) := by
  calc
    _ = (-8679515472176359771046253837436380717660820809638345926733312797115249689368 : ℤ) + (-1023226639463044857105424063112590902951969476418180835725907618865676070360 : ℤ) := by
      simpa only [Nat.reduceAdd, span336_338, span338_340] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 336 2 2
    _ = _ := by decide +kernel

private theorem span340_342 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 340 2 = (268061996433866808429054652644492754458476892008879529454809953173430874496 : ℤ) := by
  calc
    _ = (4951213006270971272912960730276046276620915656956071409137642964538033855304 : ℤ) + (-4683151009837104464483906077631553522162438764947191879682833011364602980808 : ℤ) := by
      simpa only [Nat.reduceAdd, row340, row341] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 340 1 1
    _ = _ := by decide +kernel

private theorem span342_344 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 342 2 = (-13287208562784453723155678034077472150080886444188456849830833990407138356680 : ℤ) := by
  calc
    _ = (-4700409764902915968527017011000175161742950127433543653983150640102855937440 : ℤ) + (-8586798797881537754628661023077296988337936316754913195847683350304282419240 : ℤ) := by
      simpa only [Nat.reduceAdd, row342, row343] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 342 1 1
    _ = _ := by decide +kernel

private theorem span340_344 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 340 4 = (-13019146566350586914726623381432979395622409552179577320376024037233707482184 : ℤ) := by
  calc
    _ = (268061996433866808429054652644492754458476892008879529454809953173430874496 : ℤ) + (-13287208562784453723155678034077472150080886444188456849830833990407138356680 : ℤ) := by
      simpa only [Nat.reduceAdd, span340_342, span342_344] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 340 2 2
    _ = _ := by decide +kernel

private theorem span336_344 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 336 8 = (-22721888677989991542878301281981951016235199838236104082835244453214633241912 : ℤ) := by
  calc
    _ = (-9702742111639404628151677900548971620612790286056526762459220415980925759728 : ℤ) + (-13019146566350586914726623381432979395622409552179577320376024037233707482184 : ℤ) := by
      simpa only [Nat.reduceAdd, span336_340, span340_344] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 336 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows336To344 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 336 8 = (-22721888677989991542878301281981951016235199838236104082835244453214633241912 : ℤ) :=
  span336_344

#print axioms dottieFastReferenceRows336To344

end QuarticModel
