import Gauss23PanelEndpoint
import Mathlib.Tactic.FinCases

/-! Directed panel checks at the remaining marked endpoints through height twenty. -/

namespace FieldTarget

private def panelEnds182 : List ℤ :=
  [20497655750973418424979, -50706800682642784983810, 56759885196402298028093, -42352952227970488962296,
    22061157701271500786798, -7758893954282791327456, 1672520746894363439802, -174057282248434583637,
    357177054529380498, 1203034596839945097, -61695354696036374, 797406107111732,
    -2315876380594, 1094080811, -52119, 0]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_182_clearsError : gauss23ClearsError 182 16 true := by
  refine gauss23_clearsError_of_panel_ends 182 16 true panelEnds182 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_182_clearsError

private def panelEnds183 : List ℤ :=
  [19502334989245167719474, -48419856981237265802798, 54615740116559478788835, -41270217516446106175434,
    21922979151612168481435, -7955443580723445141504, 1814115077918617658057, -217087033881437102196,
    6697256115608081201, 787602185291437375, -51672174283549318, 734036045404370,
    -2290341233029, 1169109995, -62016, 34]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_183_clearsError : gauss23ClearsError 183 16 false := by
  refine gauss23_clearsError_of_panel_ends 183 16 false panelEnds183 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_183_clearsError

private def panelEnds206 : List ℤ :=
  [-1379231861817500870694, 3408749764785860862094, -3802988681594238594143, 2810669557287214812139,
    -1427524077453867592572, 469089679036984814671, -81291277268194077919, 696288972423306023,
    2093665163475179011, -277421944218598910, 11649702700276058, -149197952359904,
    465419774642, -252626695, 15178, 30]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_206_clearsError : gauss23ClearsError 206 16 false := by
  refine gauss23_clearsError_of_panel_ends 206 16 false panelEnds206 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_206_clearsError

private def panelEnds207 : List ℤ :=
  [-2190579610684933836772, 5490525001300637611187, -6319048997340705867123, 4938026718820650775433,
    -2764842715953299595978, 1090248062630146141950, -286225228823534832789, 45597133592874261970,
    -3835446883910714708, 136443494830119174, -1215237512601263, -6346125902836,
    38082580758, -12740903, -743, -3]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_207_clearsError : gauss23ClearsError 207 16 true := by
  refine gauss23_clearsError_of_panel_ends 207 16 true panelEnds207 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_207_clearsError

private def panelEnds234 : List ℤ :=
  [-20602283619292500551249, 49330755937576125049355, -51709350596876408966670, 34888848118395499065150,
    -15756211235575266941367, 4486204610596576412151, -641749813418255159931, -11131931154972249505,
    16744130761358943301, -1895427433626250592, 70771462820372231, -795593242946228,
    2056628101327, -806785073, 23419, -8]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_234_clearsError : gauss23ClearsError 234 16 true := by
  refine gauss23_clearsError_of_panel_ends 234 16 true panelEnds234 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_234_clearsError

private def panelEnds235 : List ℤ :=
  [-21148160566494797626888, 50401570610640989809413, -52297157634699314195294, 34659658571996748333697,
    -15168103240623212170853, 4049861640906391991954, -465967839884552564520, -51134721811093519060,
    21503139909435191556, -2143879760004501033, 74612093615517382, -785360712213672,
    1861876181460, -619559440, 8078, 28]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_235_clearsError : gauss23ClearsError 235 16 false := by
  refine gauss23_clearsError_of_panel_ends 235 16 false panelEnds235 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_235_clearsError

private def panelEnds263 : List ℤ :=
  [-32305298860498541604236, 62672433032857680022015, -37781610811514673561976, 1669508271915973908649,
    10296660575441702711627, -5559981798465804036334, 988384957541129373835, 49142592050375849574,
    -31635461709460875275, 2434372421633372802, -36643302579656956, -233376453770414,
    1978145906895, -1024699170, 16579, 25]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_263_clearsError : gauss23ClearsError 263 16 false := by
  refine gauss23_clearsError_of_panel_ends 263 16 false panelEnds263 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_263_clearsError

private def panelEnds264 : List ℤ :=
  [-32556452220216121596013, 62513173256630439305847, -36421524685535165958648, 159728224277634328650,
    10869446408378743170023, -5472664661770912723973, 856620643193436390050, 83373657391943130630,
    -33999997031373686895, 2325911889788903593, -26183963293072724, -355236297555958,
    2102615940791, -900891990, 1069, -18]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gauss23_at_264_clearsError : gauss23ClearsError 264 16 true := by
  refine gauss23_clearsError_of_panel_ends 264 16 true panelEnds264 ?_ (by decide +kernel)
  intro j
  fin_cases j <;> decide +kernel

#print axioms gauss23_at_264_clearsError

end FieldTarget
