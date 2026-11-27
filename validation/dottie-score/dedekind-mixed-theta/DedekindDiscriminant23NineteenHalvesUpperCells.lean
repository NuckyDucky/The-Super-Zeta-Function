import DedekindDiscriminant23NineteenHalvesCellChecks

namespace FieldTarget

set_option maxRecDepth 16384
set_option maxHeartbeats 24000000

theorem discriminant23_nineteenHalves_above_left_checks (j : Fin 4) :
    (discriminant23NineteenHalvesCell false (72 + j.val) (-2) 0).re.hi < -(6 * 10 ^ 17) := by
  fin_cases j <;> decide +kernel

theorem discriminant23_nineteenHalves_above_right_checks (j : Fin 4) :
    (discriminant23NineteenHalvesCell false (72 + j.val) 0 2).re.hi < -(6 * 10 ^ 17) := by
  fin_cases j <;> decide +kernel

#print axioms discriminant23_nineteenHalves_above_left_checks
#print axioms discriminant23_nineteenHalves_above_right_checks

end FieldTarget
