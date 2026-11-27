import DedekindDiscriminant23NineteenHalvesCellChecks

namespace FieldTarget

set_option maxRecDepth 16384
set_option maxHeartbeats 24000000

theorem discriminant23_nineteenHalves_left_checks (j : Fin 5) :
    (discriminant23NineteenHalvesCell false (67 + j.val) (-2) (-1)).im.hi < -(6 * 10 ^ 17) := by
  fin_cases j <;> decide +kernel

theorem discriminant23_nineteenHalves_right_checks (j : Fin 5) :
    6 * 10 ^ 17 < (discriminant23NineteenHalvesCell false (67 + j.val) 1 2).im.lo := by
  fin_cases j <;> decide +kernel

#print axioms discriminant23_nineteenHalves_left_checks
#print axioms discriminant23_nineteenHalves_right_checks

end FieldTarget
