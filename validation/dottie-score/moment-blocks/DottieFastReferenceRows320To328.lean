import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row320_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 320 =
    (-153883725053551980258466513338575315893999491247621155950783472338425851016 : ℤ) := by decide +kernel

private theorem row320_block0 : dottiePairRowBlock dottieFastReferenceWeight 320 0 320 =
    (9719896669518803240116686308191648855607870213955707957207798058228088445808 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 320 0 320).symm.trans (by decide +kernel)

private theorem row320 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 320 1 = (9566012944465251259858219794853073539713870722708086801257014585889662594792 : ℤ) := by
  rw [dottiePairedRowSpan_one, row320_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 320 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 320 % 1024 = 320 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row320_block0]
  decide +kernel

private theorem row321_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 321 =
    (-333834539471299467498034151522982437386349688830844656806373624713509564416 : ℤ) := by decide +kernel

private theorem row321_block0 : dottiePairRowBlock dottieFastReferenceWeight 321 0 321 =
    (-9966862995473719487759763697455280092362416435703304250034929308459957119528 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 321 0 321).symm.trans (by decide +kernel)

private theorem row321 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 321 1 = (-10300697534945018955257797848978262529748766124534148906841302933173466683944 : ℤ) := by
  rw [dottiePairedRowSpan_one, row321_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 321 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 321 % 1024 = 321 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row321_block0]
  decide +kernel

private theorem row322_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 322 =
    (-331297922282330442815605130369527316052559628969552852993941768057697492480 : ℤ) := by decide +kernel

private theorem row322_block0 : dottiePairRowBlock dottieFastReferenceWeight 322 0 322 =
    (-11047776713953989363422530189792608123418424483851138644737010167504111366872 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 322 0 322).symm.trans (by decide +kernel)

private theorem row322 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 322 1 = (-11379074636236319806238135320162135439470984112820691497730951935561808859352 : ℤ) := by
  rw [dottiePairedRowSpan_one, row322_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 322 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 322 % 1024 = 322 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row322_block0]
  decide +kernel

private theorem row323_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 323 =
    (16903793305371799140325836793935454922104170354629185496397527663297611952 : ℤ) := by decide +kernel

private theorem row323_block0 : dottiePairRowBlock dottieFastReferenceWeight 323 0 323 =
    (3316877170661236243978742178828631918767210938343090733460694175647740970664 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 323 0 323).symm.trans (by decide +kernel)

private theorem row323 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 323 1 = (3333780963966608043119068015622567373689315108697719918957091703311038582616 : ℤ) := by
  rw [dottiePairedRowSpan_one, row323_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 323 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 323 % 1024 = 323 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row323_block0]
  decide +kernel

private theorem row324_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 324 =
    (-125086949791718844086385952459747873138894848290306341763144475013897302032 : ℤ) := by decide +kernel

private theorem row324_block0 : dottiePairRowBlock dottieFastReferenceWeight 324 0 324 =
    (911418762884247378744415046886812371634758360837641562901784293908388125256 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 324 0 324).symm.trans (by decide +kernel)

private theorem row324 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 324 1 = (786331813092528534658029094427064498495863512547335221138639818894490823224 : ℤ) := by
  rw [dottiePairedRowSpan_one, row324_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 324 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 324 % 1024 = 324 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row324_block0]
  decide +kernel

private theorem row325_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 325 =
    (380973191033743574960395048985166979687462337189165478469419940613902445072 : ℤ) := by decide +kernel

private theorem row325_block0 : dottiePairRowBlock dottieFastReferenceWeight 325 0 325 =
    (-2671268707202704519857315210669565150071129348519859970098206171320750776048 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 325 0 325).symm.trans (by decide +kernel)

private theorem row325 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 325 1 = (-2290295516168960944896920161684398170383667011330694491628786230706848330976 : ℤ) := by
  rw [dottiePairedRowSpan_one, row325_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 325 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 325 % 1024 = 325 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row325_block0]
  decide +kernel

private theorem row326_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 326 =
    (-31377666814400000619181679900453609665182916654660106750224976788631347136 : ℤ) := by decide +kernel

private theorem row326_block0 : dottiePairRowBlock dottieFastReferenceWeight 326 0 326 =
    (6376719675365718068452142743992233602050546042785345035678346443585132346680 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 326 0 326).symm.trans (by decide +kernel)

private theorem row326 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 326 1 = (6345342008551318067832961064091779992385363126130684928928121466796500999544 : ℤ) := by
  rw [dottiePairedRowSpan_one, row326_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 326 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 326 % 1024 = 326 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row326_block0]
  decide +kernel

private theorem row327_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 327 =
    (0 : ℤ) := by decide +kernel

private theorem row327_block0 : dottiePairRowBlock dottieFastReferenceWeight 327 0 327 =
    (-9191424327554200758137878082375974776805748310364309803346439986507303958776 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 327 0 327).symm.trans (by decide +kernel)

private theorem row327 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 327 1 = (-9191424327554200758137878082375974776805748310364309803346439986507303958776 : ℤ) := by
  rw [dottiePairedRowSpan_one, row327_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 327 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 327 % 1024 = 327 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row327_block0]
  decide +kernel

private theorem span320_322 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 320 2 = (-734684590479767695399578054125188990034895401826062105584288347283804089152 : ℤ) := by
  calc
    _ = (9566012944465251259858219794853073539713870722708086801257014585889662594792 : ℤ) + (-10300697534945018955257797848978262529748766124534148906841302933173466683944 : ℤ) := by
      simpa only [Nat.reduceAdd, row320, row321] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 320 1 1
    _ = _ := by decide +kernel

private theorem span322_324 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 322 2 = (-8045293672269711763119067304539568065781669004122971578773860232250770276736 : ℤ) := by
  calc
    _ = (-11379074636236319806238135320162135439470984112820691497730951935561808859352 : ℤ) + (3333780963966608043119068015622567373689315108697719918957091703311038582616 : ℤ) := by
      simpa only [Nat.reduceAdd, row322, row323] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 322 1 1
    _ = _ := by decide +kernel

private theorem span320_324 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 320 4 = (-8779978262749479458518645358664757055816564405949033684358148579534574365888 : ℤ) := by
  calc
    _ = (-734684590479767695399578054125188990034895401826062105584288347283804089152 : ℤ) + (-8045293672269711763119067304539568065781669004122971578773860232250770276736 : ℤ) := by
      simpa only [Nat.reduceAdd, span320_322, span322_324] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 320 2 2
    _ = _ := by decide +kernel

private theorem span324_326 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 324 2 = (-1503963703076432410238891067257333671887803498783359270490146411812357507752 : ℤ) := by
  calc
    _ = (786331813092528534658029094427064498495863512547335221138639818894490823224 : ℤ) + (-2290295516168960944896920161684398170383667011330694491628786230706848330976 : ℤ) := by
      simpa only [Nat.reduceAdd, row324, row325] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 324 1 1
    _ = _ := by decide +kernel

private theorem span326_328 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 326 2 = (-2846082319002882690304917018284194784420385184233624874418318519710802959232 : ℤ) := by
  calc
    _ = (6345342008551318067832961064091779992385363126130684928928121466796500999544 : ℤ) + (-9191424327554200758137878082375974776805748310364309803346439986507303958776 : ℤ) := by
      simpa only [Nat.reduceAdd, row326, row327] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 326 1 1
    _ = _ := by decide +kernel

private theorem span324_328 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 324 4 = (-4350046022079315100543808085541528456308188683016984144908464931523160466984 : ℤ) := by
  calc
    _ = (-1503963703076432410238891067257333671887803498783359270490146411812357507752 : ℤ) + (-2846082319002882690304917018284194784420385184233624874418318519710802959232 : ℤ) := by
      simpa only [Nat.reduceAdd, span324_326, span326_328] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 324 2 2
    _ = _ := by decide +kernel

private theorem span320_328 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 320 8 = (-13130024284828794559062453444206285512124753088966017829266613511057734832872 : ℤ) := by
  calc
    _ = (-8779978262749479458518645358664757055816564405949033684358148579534574365888 : ℤ) + (-4350046022079315100543808085541528456308188683016984144908464931523160466984 : ℤ) := by
      simpa only [Nat.reduceAdd, span320_324, span324_328] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 320 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows320To328 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 320 8 = (-13130024284828794559062453444206285512124753088966017829266613511057734832872 : ℤ) :=
  span320_328

#print axioms dottieFastReferenceRows320To328

end QuarticModel
