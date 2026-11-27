import DottieSharpScoreRanges

namespace QuarticModel.DottieFixedIntervals

set_option autoImplicit false

/-- The admissible real and imaginary tick endpoints in degree order. -/
def dottieSharpScoreRangeTable : List ((ℤ × ℤ) × (ℤ × ℤ)) := [
  ((11387621558886979486, 11387655500896075113), (13924985513402935335, 13925019455412030962)),
  ((1714071264240360469, 1714105206249456093), (-2734401988232412106, -2734368046223316482)),
  ((-387635148122409773, -387601206113314148), (284610039208708328, 284643981217803952)),
  ((43951661758845573, 43985603767941197), (464035418990593, 497977428086217)),
  ((-1373694286837228, -1339752277741604), (-5739787647238761, -5705845638143137)),
  ((-472956016458371, -439014007362747), (1196041388220313, 1229983397315937)),
  ((90164519826081, 124106528921705), (-183452397801720, -149510388706096)),
  ((-31510291561718, 2431717533906), (812357769627, 34754366865251)),
  ((-15465138513344, 18476870582280), (-18551483688332, 15390525407292)),
  ((-17100424072800, 16841585022824), (-16849938411342, 17092070684282)),
  ((-16961396050727, 16980613044897), (-16979179176830, 16962829918794))
]

theorem dottie_sharp_score_range_table_eq (k : Fin 11) :
    (let r := dottieSharpAdmissibleTicks k
     ((r.re.lo, r.re.hi), (r.im.lo, r.im.hi))) =
      dottieSharpScoreRangeTable.getD k ((0,0),(0,0)) := by
  fin_cases k <;> decide +kernel

theorem dottie_sharp_score_range_min_width (k : Fin 11) :
    let r := dottieSharpAdmissibleTicks k
    (33942009095624 : ℤ) ≤ r.re.hi - r.re.lo ∧
      (33942009095624 : ℤ) ≤ r.im.hi - r.im.lo := by
  fin_cases k <;> decide +kernel

#print axioms dottie_sharp_score_range_table_eq
#print axioms dottie_sharp_score_range_min_width

end QuarticModel.DottieFixedIntervals
