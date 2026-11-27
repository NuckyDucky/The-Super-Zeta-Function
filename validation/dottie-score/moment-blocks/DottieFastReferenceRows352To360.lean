import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row352_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 352 =
    (280200528618086992400382706845950268144848381980342674964799278488582576344 : ℤ) := by decide +kernel

private theorem row352_block0 : dottiePairRowBlock dottieFastReferenceWeight 352 0 352 =
    (220400071942254527682028085563583443518042300564367326500445326641231897616 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 352 0 352).symm.trans (by decide +kernel)

private theorem row352 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 352 1 = (500600600560341520082410792409533711662890682544710001465244605129814473960 : ℤ) := by
  rw [dottiePairedRowSpan_one, row352_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 352 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 352 % 1024 = 352 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row352_block0]
  decide +kernel

private theorem row353_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 353 =
    (321367142102338133170600390702640170947829878686622769710943288128142028808 : ℤ) := by decide +kernel

private theorem row353_block0 : dottiePairRowBlock dottieFastReferenceWeight 353 0 353 =
    (-12067299894715372502344447346286534229573084409005697483679250993626393598064 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 353 0 353).symm.trans (by decide +kernel)

private theorem row353 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 353 1 = (-11745932752613034369173846955583894058625254530319074713968307705498251569256 : ℤ) := by
  rw [dottiePairedRowSpan_one, row353_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 353 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 353 % 1024 = 353 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row353_block0]
  decide +kernel

private theorem row354_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 354 =
    (253145040680315087189720745114380015203930061780673607651398560579641679144 : ℤ) := by decide +kernel

private theorem row354_block0 : dottiePairRowBlock dottieFastReferenceWeight 354 0 354 =
    (2012712832538755767200948593009206416590688863200962204877010153026184975096 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 354 0 354).symm.trans (by decide +kernel)

private theorem row354 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 354 1 = (2265857873219070854390669338123586431794618924981635812528408713605826654240 : ℤ) := by
  rw [dottiePairedRowSpan_one, row354_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 354 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 354 % 1024 = 354 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row354_block0]
  decide +kernel

private theorem row355_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 355 =
    (-295636806380705560157754507185686691107271663807372617280942101539762948272 : ℤ) := by decide +kernel

private theorem row355_block0 : dottiePairRowBlock dottieFastReferenceWeight 355 0 355 =
    (-1720258528006410617579988860109409513436004000798663558606232763686945548992 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 355 0 355).symm.trans (by decide +kernel)

private theorem row355 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 355 1 = (-2015895334387116177737743367295096204543275664606036175887174865226708497264 : ℤ) := by
  rw [dottiePairedRowSpan_one, row355_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 355 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 355 % 1024 = 355 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row355_block0]
  decide +kernel

private theorem row356_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 356 =
    (55908855220511520482984021466594815169965685222879509793539834808237939512 : ℤ) := by decide +kernel

private theorem row356_block0 : dottiePairRowBlock dottieFastReferenceWeight 356 0 356 =
    (-6367486357367376824464239466348191353538141366742076177103412128954455184856 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 356 0 356).symm.trans (by decide +kernel)

private theorem row356 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 356 1 = (-6311577502146865303981255444881596538368175681519196667309872294146217245344 : ℤ) := by
  rw [dottiePairedRowSpan_one, row356_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 356 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 356 % 1024 = 356 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row356_block0]
  decide +kernel

private theorem row357_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 357 =
    (289801031368945423176038631720609332433486168708922546155421205214066681088 : ℤ) := by decide +kernel

private theorem row357_block0 : dottiePairRowBlock dottieFastReferenceWeight 357 0 357 =
    (1234293981673416924576349699454824035633449980125037554119946018007789901936 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 357 0 357).symm.trans (by decide +kernel)

private theorem row357 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 357 1 = (1524095013042362347752388331175433368066936148833960100275367223221856583024 : ℤ) := by
  rw [dottiePairedRowSpan_one, row357_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 357 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 357 % 1024 = 357 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row357_block0]
  decide +kernel

private theorem row358_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 358 =
    (353477324393272731029052862944970275871512039676676481114434688292542141832 : ℤ) := by decide +kernel

private theorem row358_block0 : dottiePairRowBlock dottieFastReferenceWeight 358 0 358 =
    (-2667750217624042667053050136776318778520843787440284393698853897390967034032 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 358 0 358).symm.trans (by decide +kernel)

private theorem row358 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 358 1 = (-2314272893230769936023997273831348502649331747763607912584419209098424892200 : ℤ) := by
  rw [dottiePairedRowSpan_one, row358_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 358 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 358 % 1024 = 358 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row358_block0]
  decide +kernel

private theorem row359_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 359 =
    (322560271460688486365098290633953520353943874001174665501716819206037800232 : ℤ) := by decide +kernel

private theorem row359_block0 : dottiePairRowBlock dottieFastReferenceWeight 359 0 359 =
    (-5062223193996598787352639957958137182380516065293289186852533491052942562720 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 359 0 359).symm.trans (by decide +kernel)

private theorem row359 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 359 1 = (-4739662922535910300987541667324183662026572191292114521350816671846904762488 : ℤ) := by
  rw [dottiePairedRowSpan_one, row359_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 359 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 359 % 1024 = 359 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row359_block0]
  decide +kernel

private theorem span352_354 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 352 2 = (-11245332152052692849091436163174360346962363847774364712503063100368437095296 : ℤ) := by
  calc
    _ = (500600600560341520082410792409533711662890682544710001465244605129814473960 : ℤ) + (-11745932752613034369173846955583894058625254530319074713968307705498251569256 : ℤ) := by
      simpa only [Nat.reduceAdd, row352, row353] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 352 1 1
    _ = _ := by decide +kernel

private theorem span354_356 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 354 2 = (249962538831954676652925970828490227251343260375599636641233848379118156976 : ℤ) := by
  calc
    _ = (2265857873219070854390669338123586431794618924981635812528408713605826654240 : ℤ) + (-2015895334387116177737743367295096204543275664606036175887174865226708497264 : ℤ) := by
      simpa only [Nat.reduceAdd, row354, row355] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 354 1 1
    _ = _ := by decide +kernel

private theorem span352_356 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 352 4 = (-10995369613220738172438510192345870119711020587398765075861829251989318938320 : ℤ) := by
  calc
    _ = (-11245332152052692849091436163174360346962363847774364712503063100368437095296 : ℤ) + (249962538831954676652925970828490227251343260375599636641233848379118156976 : ℤ) := by
      simpa only [Nat.reduceAdd, span352_354, span354_356] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 352 2 2
    _ = _ := by decide +kernel

private theorem span356_358 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 356 2 = (-4787482489104502956228867113706163170301239532685236567034505070924360662320 : ℤ) := by
  calc
    _ = (-6311577502146865303981255444881596538368175681519196667309872294146217245344 : ℤ) + (1524095013042362347752388331175433368066936148833960100275367223221856583024 : ℤ) := by
      simpa only [Nat.reduceAdd, row356, row357] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 356 1 1
    _ = _ := by decide +kernel

private theorem span358_360 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 358 2 = (-7053935815766680237011538941155532164675903939055722433935235880945329654688 : ℤ) := by
  calc
    _ = (-2314272893230769936023997273831348502649331747763607912584419209098424892200 : ℤ) + (-4739662922535910300987541667324183662026572191292114521350816671846904762488 : ℤ) := by
      simpa only [Nat.reduceAdd, row358, row359] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 358 1 1
    _ = _ := by decide +kernel

private theorem span356_360 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 356 4 = (-11841418304871183193240406054861695334977143471740959000969740951869690317008 : ℤ) := by
  calc
    _ = (-4787482489104502956228867113706163170301239532685236567034505070924360662320 : ℤ) + (-7053935815766680237011538941155532164675903939055722433935235880945329654688 : ℤ) := by
      simpa only [Nat.reduceAdd, span356_358, span358_360] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 356 2 2
    _ = _ := by decide +kernel

private theorem span352_360 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 352 8 = (-22836787918091921365678916247207565454688164059139724076831570203859009255328 : ℤ) := by
  calc
    _ = (-10995369613220738172438510192345870119711020587398765075861829251989318938320 : ℤ) + (-11841418304871183193240406054861695334977143471740959000969740951869690317008 : ℤ) := by
      simpa only [Nat.reduceAdd, span352_356, span356_360] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 352 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows352To360 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 352 8 = (-22836787918091921365678916247207565454688164059139724076831570203859009255328 : ℤ) :=
  span352_360

#print axioms dottieFastReferenceRows352To360

end QuarticModel
