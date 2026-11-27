import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row408_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 408 =
    (112837914911964226236797323367869227553447067963137229087596995848000289256 : ℤ) := by decide +kernel

private theorem row408_block0 : dottiePairRowBlock dottieFastReferenceWeight 408 0 408 =
    (1600550022493513100467658174617033850238035212874905332280603785705207610656 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 408 0 408).symm.trans (by decide +kernel)

private theorem row408 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 408 1 = (1713387937405477326704455497984903077791482280838042561368200781553207899912 : ℤ) := by
  rw [dottiePairedRowSpan_one, row408_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 408 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 408 % 1024 = 408 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row408_block0]
  decide +kernel

private theorem row409_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 409 =
    (0 : ℤ) := by decide +kernel

private theorem row409_block0 : dottiePairRowBlock dottieFastReferenceWeight 409 0 409 =
    (1337029118889692969759843594560334562726692175365820226715878595173796419472 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 409 0 409).symm.trans (by decide +kernel)

private theorem row409 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 409 1 = (1337029118889692969759843594560334562726692175365820226715878595173796419472 : ℤ) := by
  rw [dottiePairedRowSpan_one, row409_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 409 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 409 % 1024 = 409 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row409_block0]
  decide +kernel

private theorem row410_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 410 =
    (-79398914443762127660634819894565805393655376902755816180449141321330676048 : ℤ) := by decide +kernel

private theorem row410_block0 : dottiePairRowBlock dottieFastReferenceWeight 410 0 410 =
    (1174913382248945625417329509985906033165259135912374150130431095319606339408 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 410 0 410).symm.trans (by decide +kernel)

private theorem row410 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 410 1 = (1095514467805183497756694690091340227771603759009618333949981953998275663360 : ℤ) := by
  rw [dottiePairedRowSpan_one, row410_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 410 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 410 % 1024 = 410 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row410_block0]
  decide +kernel

private theorem row411_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 411 =
    (-73779439415596532437831749159223032901621143448546390882823259481134715016 : ℤ) := by decide +kernel

private theorem row411_block0 : dottiePairRowBlock dottieFastReferenceWeight 411 0 411 =
    (-7192287948558645120853896509958012127066187316449565451939619611635408164688 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 411 0 411).symm.trans (by decide +kernel)

private theorem row411 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 411 1 = (-7266067387974241653291728259117235159967808459898111842822442871116542879704 : ℤ) := by
  rw [dottiePairedRowSpan_one, row411_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 411 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 411 % 1024 = 411 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row411_block0]
  decide +kernel

private theorem row412_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 412 =
    (197465603825932281288970607337369497482601744033627099033013474351781133928 : ℤ) := by decide +kernel

private theorem row412_block0 : dottiePairRowBlock dottieFastReferenceWeight 412 0 412 =
    (596637383327152638059051257833295906297077754203194080214208436997306110888 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 412 0 412).symm.trans (by decide +kernel)

private theorem row412 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 412 1 = (794102987153084919348021865170665403779679498236821179247221911349087244816 : ℤ) := by
  rw [dottiePairedRowSpan_one, row412_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 412 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 412 % 1024 = 412 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row412_block0]
  decide +kernel

private theorem row413_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 413 =
    (254291649807915677512238979946571325436238494921093352758799448292039080024 : ℤ) := by decide +kernel

private theorem row413_block0 : dottiePairRowBlock dottieFastReferenceWeight 413 0 413 =
    (-3390807883551124441943329759858659311130771722074970447235720771815331028704 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 413 0 413).symm.trans (by decide +kernel)

private theorem row413 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 413 1 = (-3136516233743208764431090779912087985694533227153877094476921323523291948680 : ℤ) := by
  rw [dottiePairedRowSpan_one, row413_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 413 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 413 % 1024 = 413 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row413_block0]
  decide +kernel

private theorem row414_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 414 =
    (-182648932316653868714956639996930532571241118116505531333354982833337936120 : ℤ) := by decide +kernel

private theorem row414_block0 : dottiePairRowBlock dottieFastReferenceWeight 414 0 414 =
    (-3643580540796874126563299763138417737549416082370378132155374715775353984448 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 414 0 414).symm.trans (by decide +kernel)

private theorem row414 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 414 1 = (-3826229473113527995278256403135348270120657200486883663488729698608691920568 : ℤ) := by
  rw [dottiePairedRowSpan_one, row414_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 414 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 414 % 1024 = 414 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row414_block0]
  decide +kernel

private theorem row415_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 415 =
    (-305657782681341880617872474092646053553792633161686773280775314971673360920 : ℤ) := by decide +kernel

private theorem row415_block0 : dottiePairRowBlock dottieFastReferenceWeight 415 0 415 =
    (-1126372800180622093636181903961946166933395268080477168194535356265418756168 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 415 0 415).symm.trans (by decide +kernel)

private theorem row415 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 415 1 = (-1432030582861963974254054378054592220487187901242163941475310671237092117088 : ℤ) := by
  rw [dottiePairedRowSpan_one, row415_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 415 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 415 % 1024 = 415 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row415_block0]
  decide +kernel

private theorem span408_410 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 408 2 = (3050417056295170296464299092545237640518174456203862788084079376727004319384 : ℤ) := by
  calc
    _ = (1713387937405477326704455497984903077791482280838042561368200781553207899912 : ℤ) + (1337029118889692969759843594560334562726692175365820226715878595173796419472 : ℤ) := by
      simpa only [Nat.reduceAdd, row408, row409] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 408 1 1
    _ = _ := by decide +kernel

private theorem span410_412 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 410 2 = (-6170552920169058155535033569025894932196204700888493508872460917118267216344 : ℤ) := by
  calc
    _ = (1095514467805183497756694690091340227771603759009618333949981953998275663360 : ℤ) + (-7266067387974241653291728259117235159967808459898111842822442871116542879704 : ℤ) := by
      simpa only [Nat.reduceAdd, row410, row411] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 410 1 1
    _ = _ := by decide +kernel

private theorem span408_412 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 408 4 = (-3120135863873887859070734476480657291678030244684630720788381540391262896960 : ℤ) := by
  calc
    _ = (3050417056295170296464299092545237640518174456203862788084079376727004319384 : ℤ) + (-6170552920169058155535033569025894932196204700888493508872460917118267216344 : ℤ) := by
      simpa only [Nat.reduceAdd, span408_410, span410_412] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 408 2 2
    _ = _ := by decide +kernel

private theorem span412_414 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 412 2 = (-2342413246590123845083068914741422581914853728917055915229699412174204703864 : ℤ) := by
  calc
    _ = (794102987153084919348021865170665403779679498236821179247221911349087244816 : ℤ) + (-3136516233743208764431090779912087985694533227153877094476921323523291948680 : ℤ) := by
      simpa only [Nat.reduceAdd, row412, row413] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 412 1 1
    _ = _ := by decide +kernel

private theorem span414_416 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 414 2 = (-5258260055975491969532310781189940490607845101729047604964040369845784037656 : ℤ) := by
  calc
    _ = (-3826229473113527995278256403135348270120657200486883663488729698608691920568 : ℤ) + (-1432030582861963974254054378054592220487187901242163941475310671237092117088 : ℤ) := by
      simpa only [Nat.reduceAdd, row414, row415] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 414 1 1
    _ = _ := by decide +kernel

private theorem span412_416 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 412 4 = (-7600673302565615814615379695931363072522698830646103520193739782019988741520 : ℤ) := by
  calc
    _ = (-2342413246590123845083068914741422581914853728917055915229699412174204703864 : ℤ) + (-5258260055975491969532310781189940490607845101729047604964040369845784037656 : ℤ) := by
      simpa only [Nat.reduceAdd, span412_414, span414_416] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 412 2 2
    _ = _ := by decide +kernel

private theorem span408_416 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 408 8 = (-10720809166439503673686114172412020364200729075330734240982121322411251638480 : ℤ) := by
  calc
    _ = (-3120135863873887859070734476480657291678030244684630720788381540391262896960 : ℤ) + (-7600673302565615814615379695931363072522698830646103520193739782019988741520 : ℤ) := by
      simpa only [Nat.reduceAdd, span408_412, span412_416] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 408 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows408To416 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 408 8 = (-10720809166439503673686114172412020364200729075330734240982121322411251638480 : ℤ) :=
  span408_416

#print axioms dottieFastReferenceRows408To416

end QuarticModel
