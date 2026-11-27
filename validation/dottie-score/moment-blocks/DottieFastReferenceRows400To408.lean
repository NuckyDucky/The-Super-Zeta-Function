import DottieFastReferenceScore
import DottieWitnessPairBlocks

namespace QuarticModel

set_option maxHeartbeats 30000000
set_option maxRecDepth 12000

private theorem row400_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 400 =
    (205203588450566135054080966336457706571275892266450567780780343423313328000 : ℤ) := by decide +kernel

private theorem row400_block0 : dottiePairRowBlock dottieFastReferenceWeight 400 0 400 =
    (14577749116123833965414227561415161214470818736819802132267437026654791628864 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 400 0 400).symm.trans (by decide +kernel)

private theorem row400 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 400 1 = (14782952704574400100468308527751618921042094629086252700048217370078104956864 : ℤ) := by
  rw [dottiePairedRowSpan_one, row400_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 400 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 400 % 1024 = 400 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row400_block0]
  decide +kernel

private theorem row401_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 401 =
    (-289370564524643706481422946026901437355353977186449226341440691954871834784 : ℤ) := by decide +kernel

private theorem row401_block0 : dottiePairRowBlock dottieFastReferenceWeight 401 0 401 =
    (-8977829905500628118709042443093929196523361018683301074359440768203355162600 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 401 0 401).symm.trans (by decide +kernel)

private theorem row401 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 401 1 = (-9267200470025271825190465389120830633878714995869750300700881460158226997384 : ℤ) := by
  rw [dottiePairedRowSpan_one, row401_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 401 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 401 % 1024 = 401 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row401_block0]
  decide +kernel

private theorem row402_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 402 =
    (139959340672502875855003659605883686980209564540177514268940733126072916608 : ℤ) := by decide +kernel

private theorem row402_block0 : dottiePairRowBlock dottieFastReferenceWeight 402 0 402 =
    (-2440297737713246577804724726916600831416718379887515432927957440953497128288 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 402 0 402).symm.trans (by decide +kernel)

private theorem row402 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 402 1 = (-2300338397040743701949721067310717144436508815347337918659016707827424211680 : ℤ) := by
  rw [dottiePairedRowSpan_one, row402_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 402 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 402 % 1024 = 402 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row402_block0]
  decide +kernel

private theorem row403_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 403 =
    (305232125942943433514057667439560785754376744473280114413718377488898570240 : ℤ) := by decide +kernel

private theorem row403_block0 : dottiePairRowBlock dottieFastReferenceWeight 403 0 403 =
    (323590986507386339239795334233197369890141741098843247787939803007990105960 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 403 0 403).symm.trans (by decide +kernel)

private theorem row403 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 403 1 = (628823112450329772753853001672758155644518485572123362201658180496888676200 : ℤ) := by
  rw [dottiePairedRowSpan_one, row403_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 403 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 403 % 1024 = 403 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row403_block0]
  decide +kernel

private theorem row404_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 404 =
    (-278693281869038963219481438578137921709205273569423571146462836653876359768 : ℤ) := by decide +kernel

private theorem row404_block0 : dottiePairRowBlock dottieFastReferenceWeight 404 0 404 =
    (847837783581987813995980184621927813586265910677135561065694878853801226472 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 404 0 404).symm.trans (by decide +kernel)

private theorem row404 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 404 1 = (569144501712948850776498746043789891877060637107711989919232042199924866704 : ℤ) := by
  rw [dottiePairedRowSpan_one, row404_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 404 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 404 % 1024 = 404 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row404_block0]
  decide +kernel

private theorem row405_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 405 =
    (-46284133242378561156575852159612496294954900102392927843074829572540835840 : ℤ) := by decide +kernel

private theorem row405_block0 : dottiePairRowBlock dottieFastReferenceWeight 405 0 405 =
    (5176552812959839961801598447201748888186421307127137462632685280576401662304 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 405 0 405).symm.trans (by decide +kernel)

private theorem row405 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 405 1 = (5130268679717461400645022595042136391891466407024744534789610451003860826464 : ℤ) := by
  rw [dottiePairedRowSpan_one, row405_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 405 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 405 % 1024 = 405 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row405_block0]
  decide +kernel

private theorem row406_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 406 =
    (-182434810550820976532930349573982266781184367214747927898622979686546137576 : ℤ) := by decide +kernel

private theorem row406_block0 : dottiePairRowBlock dottieFastReferenceWeight 406 0 406 =
    (-1696285779429115622610174348100696400295911420125575943847675762202281541680 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 406 0 406).symm.trans (by decide +kernel)

private theorem row406 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 406 1 = (-1878720589979936599143104697674678667077095787340323871746298741888827679256 : ℤ) := by
  rw [dottiePairedRowSpan_one, row406_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 406 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 406 % 1024 = 406 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row406_block0]
  decide +kernel

private theorem row407_head : dottiePairRowHead 276824064 dottieFastReferenceWeight 407 =
    (297089821680290083437618606467322787118303369391155169268252362355730008448 : ℤ) := by decide +kernel

private theorem row407_block0 : dottiePairRowBlock dottieFastReferenceWeight 407 0 407 =
    (4325596426052663752835171045815744371938535149399266596412363764720407326784 : ℤ) :=
  (dottie_pair_row_block_with_sign_eq dottieLookupRowSign dottieLookupRowSign_eq
    dottieFastReferenceWeight 407 0 407).symm.trans (by decide +kernel)

private theorem row407 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 407 1 = (4622686247732953836272789652283067159056838518790421765680616127076137335232 : ℤ) := by
  rw [dottiePairedRowSpan_one, row407_head, dottiePairRowBlock_eq_blocks _ _ _ 1024]
  rw [show dottiePairRowSize 276824064 407 / 1024 = 0 by decide +kernel,
    show dottiePairRowSize 276824064 407 % 1024 = 407 by decide +kernel]
  simp only [Finset.sum_range_zero, Nat.zero_mul,
    row407_block0]
  decide +kernel

private theorem span400_402 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 400 2 = (5515752234549128275277843138630788287163379633216502399347335909919877959480 : ℤ) := by
  calc
    _ = (14782952704574400100468308527751618921042094629086252700048217370078104956864 : ℤ) + (-9267200470025271825190465389120830633878714995869750300700881460158226997384 : ℤ) := by
      simpa only [Nat.reduceAdd, row400, row401] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 400 1 1
    _ = _ := by decide +kernel

private theorem span402_404 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 402 2 = (-1671515284590413929195868065637958988791990329775214556457358527330535535480 : ℤ) := by
  calc
    _ = (-2300338397040743701949721067310717144436508815347337918659016707827424211680 : ℤ) + (628823112450329772753853001672758155644518485572123362201658180496888676200 : ℤ) := by
      simpa only [Nat.reduceAdd, row402, row403] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 402 1 1
    _ = _ := by decide +kernel

private theorem span400_404 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 400 4 = (3844236949958714346081975072992829298371389303441287842889977382589342424000 : ℤ) := by
  calc
    _ = (5515752234549128275277843138630788287163379633216502399347335909919877959480 : ℤ) + (-1671515284590413929195868065637958988791990329775214556457358527330535535480 : ℤ) := by
      simpa only [Nat.reduceAdd, span400_402, span402_404] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 400 2 2
    _ = _ := by decide +kernel

private theorem span404_406 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 404 2 = (5699413181430410251421521341085926283768527044132456524708842493203785693168 : ℤ) := by
  calc
    _ = (569144501712948850776498746043789891877060637107711989919232042199924866704 : ℤ) + (5130268679717461400645022595042136391891466407024744534789610451003860826464 : ℤ) := by
      simpa only [Nat.reduceAdd, row404, row405] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 404 1 1
    _ = _ := by decide +kernel

private theorem span406_408 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 406 2 = (2743965657753017237129684954608388491979742731450097893934317385187309655976 : ℤ) := by
  calc
    _ = (-1878720589979936599143104697674678667077095787340323871746298741888827679256 : ℤ) + (4622686247732953836272789652283067159056838518790421765680616127076137335232 : ℤ) := by
      simpa only [Nat.reduceAdd, row406, row407] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 406 1 1
    _ = _ := by decide +kernel

private theorem span404_408 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 404 4 = (8443378839183427488551206295694314775748269775582554418643159878391095349144 : ℤ) := by
  calc
    _ = (5699413181430410251421521341085926283768527044132456524708842493203785693168 : ℤ) + (2743965657753017237129684954608388491979742731450097893934317385187309655976 : ℤ) := by
      simpa only [Nat.reduceAdd, span404_406, span406_408] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 404 2 2
    _ = _ := by decide +kernel

private theorem span400_408 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 400 8 = (12287615789142141834633181368687144074119659079023842261533137260980437773144 : ℤ) := by
  calc
    _ = (3844236949958714346081975072992829298371389303441287842889977382589342424000 : ℤ) + (8443378839183427488551206295694314775748269775582554418643159878391095349144 : ℤ) := by
      simpa only [Nat.reduceAdd, span400_404, span404_408] using
        dottiePairedRowSpan_add 276824064 dottieFastReferenceWeight 400 4 4
    _ = _ := by decide +kernel

theorem dottieFastReferenceRows400To408 :
    dottiePairedRowSpan 276824064 dottieFastReferenceWeight 400 8 = (12287615789142141834633181368687144074119659079023842261533137260980437773144 : ℤ) :=
  span400_408

#print axioms dottieFastReferenceRows400To408

end QuarticModel
