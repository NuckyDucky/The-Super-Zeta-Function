import DedekindDiscriminant23CoefficientData
import DedekindDiscriminant23ReadingCells

/-! The fixed-point polynomial checks for the sign certificate through height 19/2. -/

namespace FieldTarget

open DottieOriented.NativeSpectrum.MellinFixed

def discriminant23NineteenHalvesCell (odd : Bool) (k : ℕ) (l r : ℤ) : ComplexBox :=
  discriminant23ReadingCellBoxUpTo (discriminant23StoredReadingCoefficientBox odd)
    68 (2 * (k : ℤ) + 1) 1 96 l r 24

set_option maxRecDepth 16384
set_option maxHeartbeats 24000000

theorem discriminant23_nineteenHalves_below_checks (j : Fin 3) :
    6 * 10 ^ 17 < (discriminant23NineteenHalvesCell false (64 + j.val) (-2) 2).re.lo := by
  fin_cases j <;> decide +kernel

theorem discriminant23_nineteenHalves_slope_checks (j : Fin 5) :
    2 * 10 ^ 18 < (discriminant23NineteenHalvesCell true (67 + j.val) (-1) 1).im.lo := by
  fin_cases j <;> decide +kernel

#print axioms discriminant23_nineteenHalves_below_checks
#print axioms discriminant23_nineteenHalves_slope_checks

end FieldTarget
