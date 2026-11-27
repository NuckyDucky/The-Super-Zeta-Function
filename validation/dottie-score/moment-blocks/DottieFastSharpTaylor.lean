import DottieJointMomentScore

/-! Preserve the original Taylor intervals while evaluating only the two nonzero products. -/

namespace QuarticModel.DottieFixedIntervals

open private factorialCoeff from DottieFixedTaylor
open private ceilDiv from DottieFixedIntervals

set_option autoImplicit false
set_option maxRecDepth 8000

private def factorialTickTable : Array (ℤ × ℤ) := #[
  (18446744073709551616, 18446744073709551616),
  (18446744073709551616, 18446744073709551616),
  (9223372036854775808, 9223372036854775808),
  (3074457345618258602, 3074457345618258603),
  (768614336404564650, 768614336404564651),
  (153722867280912930, 153722867280912931),
  (25620477880152155, 25620477880152156),
  (3660068268593165, 3660068268593166),
  (457508533574145, 457508533574146),
  (50834281508238, 50834281508239),
  (5083428150823, 5083428150824),
  (462129831893, 462129831894),
  (38510819324, 38510819325),
  (2962370717, 2962370718),
  (211597908, 211597909),
  (14106527, 14106528),
  (881657, 881658),
  (51862, 51863),
  (2881, 2882),
  (151, 152),
  (7, 8),
  (0, 1),
  (0, 1),
  (0, 1)
]

def dottieCachedFactorialInterval (k : ℕ) : Interval :=
  if k < 24 then
    let p := factorialTickTable[k]!
    ⟨p.1,p.2⟩
  else Interval.rational (1/(k.factorial:ℚ)) (1/(k.factorial:ℚ))

private theorem cached_factorial_endpoints (k : Fin 24) :
    (dottieCachedFactorialInterval k).lo = (factorialCoeff k).re.lo ∧
    (dottieCachedFactorialInterval k).hi = (factorialCoeff k).re.hi := by
  fin_cases k <;> decide +kernel

theorem dottie_cached_factorial_interval_eq (k : ℕ) :
    dottieCachedFactorialInterval k = Interval.rational (1/(k.factorial:ℚ)) (1/(k.factorial:ℚ)) := by
  by_cases hk : k < 24
  · obtain ⟨hl,hh⟩ := cached_factorial_endpoints ⟨k,hk⟩
    exact congrArg₂ Interval.mk hl hh
  · simp only [dottieCachedFactorialInterval, if_neg hk]

private theorem zeroInterval_mul (b : Interval) :
    (⟨0,0⟩ : Interval).mul b = ⟨0,0⟩ := by
  simp [Interval.mul, ceilDiv]

private theorem imaginary_mul (theta : Interval) (z : Rect) :
    (imaginaryBox theta).mul z = ⟨(theta.mul z.im).neg,theta.mul z.re⟩ := by
  simp only [imaginaryBox, Rect.mul, zeroInterval_mul, Interval.sub, Interval.add, zero_add]

private def imaginaryHorner (theta : Interval) : ℕ → (ℕ → Interval) → Rect
  | 0, _ => Rect.zero
  | len+1, coeff =>
    let tail := imaginaryHorner theta len (fun j => coeff (j+1))
    ⟨(coeff 0).add ((theta.mul tail.im).neg), theta.mul tail.re⟩

private theorem imaginaryHorner_eq (theta : Interval) (len : ℕ) (coeff : ℕ → Interval) :
    imaginaryHorner theta len coeff =
      (imaginaryBox theta).horner len (fun k => ⟨coeff k,⟨0,0⟩⟩) := by
  induction len generalizing coeff with
  | zero => rfl
  | succ len ih =>
    simp only [imaginaryHorner, ih, Rect.horner, imaginary_mul, Rect.add, Interval.add, zero_add]

def dottieFastImaginaryExpBox (theta : Interval) : Rect :=
  (imaginaryHorner theta 24 dottieCachedFactorialInterval).pad expTail

theorem dottie_fast_imaginary_exp_eq (theta : Interval) :
    dottieFastImaginaryExpBox theta = (imaginaryBox theta).expBox := by
  simp only [dottieFastImaginaryExpBox, imaginaryHorner_eq, dottie_cached_factorial_interval_eq,
    Rect.expBox]
  rfl

#print axioms dottie_cached_factorial_interval_eq
#print axioms dottie_fast_imaginary_exp_eq

end QuarticModel.DottieFixedIntervals
