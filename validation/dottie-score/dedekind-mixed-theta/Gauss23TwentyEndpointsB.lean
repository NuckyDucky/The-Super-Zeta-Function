import Gauss23PanelEndpoint
import Mathlib.Tactic.FinCases

/-! Directed panel checks at the remaining marked endpoints through height twenty. -/

namespace FieldTarget

private def panelEnds273 : List ℤ :=
  [-34369351579761169338611, 59516817369394548742552, -23001183611376630039498, -11977576714519422945511,
    13298861205115952905291, -3270690292145295341987, -456466471810492617084, 288522445326918573843,
    -28806975027196866399, -186969440233687904, 62263926470858833, -669195562099674,
    189768880214, 908285997, -65285, -21]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_273_clearsError : gauss23ClearsError 273 16 true := by
  refine gauss23_clearsError_of_panel_ends 273 16 true panelEnds273 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_273_clearsError

private def panelEnds274 : List ℤ :=
  [-34521667153973814107820, 59023667032670021427842, -21430389061419211403490, -13102931778618116650615,
    13259977267109168191094, -2906929228712954476508, -590780654640672481305, 295061543365912899005,
    -25546387767822176318, -527867099859925869, 66887300145402305, -598390876242593,
    -213475141310, 1026227376, -57711, 15]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_274_clearsError : gauss23ClearsError 274 16 false := by
  refine gauss23_clearsError_of_panel_ends 274 16 false panelEnds274 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_274_clearsError

private def panelEnds289 : List ℤ :=
  [-35670298478904639705826, 48611573636707097154468, 1400722573190683866251, -22530885349615209160216,
    6707262712240142491972, 2758519291387892614085, -1327970716160801261162, 21120544971266694476,
    31619867779108421553, -1634904790511722231, -29907550897247891, 731076012868911,
    -425232307169, -978313756, 50298, 23]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_289_clearsError : gauss23ClearsError 289 16 false := by
  refine gauss23_clearsError_of_panel_ends 289 16 false panelEnds289 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_289_clearsError

private def panelEnds290 : List ℤ :=
  [-35673498150967280939734, 47757202598203857452480, 2768601019988964429146, -22630805823492527375328,
    5999126377583264669515, 3035195624547493171850, -1277537577000567706068, -9948451882255704733,
    33083421956417314485, -1380463751780084112, -39279324211081465, 704387857979186,
    -30792705023, -1068055509, 38341, -19]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_290_clearsError : gauss23ClearsError 290 16 true := by
  refine gauss23_clearsError_of_panel_ends 290 16 true panelEnds290 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_290_clearsError

private def panelEnds305 : List ℤ :=
  [-34698796922297835983721, 33690721182232242318079, 18839189445476981433457, -17293756705938201836672,
    -4499882700846130354350, 3916656498275950387636, 300629007659253310158, -256091631293632314517,
    -869423470111875780, 2212977083129494635, -11030847285844131, -696602055125735,
    648842591267, 1029292806, -28493, -22]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_305_clearsError : gauss23ClearsError 305 16 true := by
  refine gauss23_clearsError_of_panel_ends 305 16 true panelEnds305 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_305_clearsError

private def panelEnds306 : List ℤ :=
  [-34568934598880705697782, 32711147789625105019402, 19568332591624617744790, -16579043943019793966260,
    -5052488445741676778343, 3760699999266562862721, 412558214458160423456, -249497393861330379442,
    -4980553431027439638, 2207558867291821945, -503672451629861, -715528261448488,
    268372424836, 1090004872, -13894, 23]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_306_clearsError : gauss23ClearsError 306 16 false := by
  refine gauss23_clearsError_of_panel_ends 306 16 false panelEnds306 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_306_clearsError

end FieldTarget
