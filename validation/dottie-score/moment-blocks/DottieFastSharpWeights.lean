import DottieJointMomentScore
import DottieFastReferenceScore
import DottieFastSharpTaylor

/-! Integer phase reduction for the original sharp moment weights. -/

namespace QuarticModel.DottieFixedIntervals

open private phaseBase piTicks heightTicks pi_ticks_eq from DottieFastReferenceScore
open private inverseSqrtBox normalizedLogBox reducedHalfPhase momentPhaseBox Interval.power
  from DottieFixedMomentWeights
open private momentColumn momentColumns addMomentPair jointMomentFold from DottieJointMomentScore
open private signRadix readPairSign from DottieCertifiedPairSigns

set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem cachedLog_eq (n : ℕ) : dottieCachedLogLowerTicks n = dottieQuickLogLowerTicks n := by
  cases n with
  | zero => decide +kernel
  | succ n => exact dottieCachedLogLowerTicks_eq _ (Nat.succ_pos n)

private def periodTicks : ℕ := 2*piTicks

private def rawSharpTicks (ticks : ℕ) : ℤ := -((heightTicks*ticks : ℕ) : ℤ)

private def reducedSharpTicks (ticks : ℕ) : ℤ :=
  (rawSharpTicks ticks + (piTicks : ℤ)) % (periodTicks : ℤ) - (piTicks : ℤ)

private theorem sharp_angle_eq (n : ℕ) :
    dottieMomentAngle n =
      (rawSharpTicks (dottieCachedLogLowerTicks n) : ℚ)/phaseBase := by
  rw [cachedLog_eq]
  unfold dottieMomentAngle rawSharpTicks
  push_cast
  norm_num [phaseBase, heightTicks, dottieMomentHeightRat]
  ring

private theorem sharp_turn_eq (n : ℕ) :
    dottieMomentAngleTurn n =
      (rawSharpTicks (dottieCachedLogLowerTicks n) + (piTicks : ℤ))/(periodTicks : ℤ) := by
  unfold dottieMomentAngleTurn
  rw [sharp_angle_eq, pi_ticks_eq]
  have hBase : (phaseBase : ℚ) ≠ 0 := by norm_num [phaseBase]
  have hFraction (r : ℤ) :
      ((r : ℚ)/phaseBase + (piTicks : ℚ)/phaseBase) / (2*((piTicks : ℚ)/phaseBase)) =
        ((r + (piTicks : ℤ) : ℤ) : ℚ)/periodTicks := by
    rw [← add_div, ← mul_div_assoc, div_div_div_cancel_right₀ hBase]
    simp only [periodTicks, Nat.cast_mul, Nat.cast_ofNat, Int.cast_add, Int.cast_natCast]
  rw [hFraction, Rat.floor_intCast_div_natCast]

private theorem sharp_reduced_angle_eq (n : ℕ) :
    dottieMomentReducedAngle n =
      (reducedSharpTicks (dottieCachedLogLowerTicks n) : ℚ)/phaseBase := by
  rw [dottieMomentReducedAngle, sharp_angle_eq, sharp_turn_eq, pi_ticks_eq]
  unfold reducedSharpTicks
  have h := Int.emod_def
    (rawSharpTicks (dottieCachedLogLowerTicks n) + (piTicks : ℤ)) (periodTicks : ℤ)
  rw [h]
  simp only [periodTicks, Nat.cast_mul, Nat.cast_ofNat, Int.cast_add, Int.cast_sub,
    Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
  ring

private def intervalFromTicks (lo hi : ℤ) (den : ℕ) : Interval :=
  ⟨lo*scale/(den : ℤ), -((-hi*scale)/(den : ℤ))⟩

private theorem intervalFromTicks_eq (lo hi : ℤ) (den : ℕ) :
    intervalFromTicks lo hi den = Interval.rational ((lo : ℚ)/den) ((hi : ℚ)/den) := by
  unfold intervalFromTicks Interval.rational
  have hFloor (x : ℤ) :
      ⌊(x : ℚ)/(den : ℚ) * (scale : ℚ)⌋ = x*scale/(den : ℤ) := by
    rw [div_mul_eq_mul_div, ← Int.cast_mul, Rat.floor_intCast_div_natCast]
  have hCeil : ⌈(hi : ℚ)/(den : ℚ)*(scale : ℚ)⌉ =
      -⌊-((hi : ℚ)/(den : ℚ)*(scale : ℚ))⌋ := by
    rw [Int.floor_neg, neg_neg]
  rw [hFloor, hCeil, ← neg_mul, ← neg_div, ← Int.cast_neg, hFloor]

private def normalizedLogFromTicks (ticks : ℕ) : Interval :=
  intervalFromTicks (-((ticks : ℤ)+128)) (-(ticks : ℤ)) (2^101)

private theorem normalizedLogFromTicks_eq (n : ℕ) :
    normalizedLogFromTicks (dottieCachedLogLowerTicks n) = normalizedLogBox n := by
  rw [normalizedLogFromTicks, intervalFromTicks_eq, normalizedLogBox, cachedLog_eq]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_ofNat,
    Nat.cast_pow, Nat.cast_ofNat]

private def halfPhaseFromTicks (ticks : ℕ) : Interval :=
  let reduced := reducedSharpTicks ticks
  intervalFromTicks reduced reduced (2*phaseBase)

private theorem halfPhaseFromTicks_eq (n : ℕ) :
    imaginaryBox (halfPhaseFromTicks (dottieCachedLogLowerTicks n)) = reducedHalfPhase n := by
  unfold halfPhaseFromTicks reducedHalfPhase
  dsimp only
  rw [intervalFromTicks_eq, sharp_reduced_angle_eq]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [div_div, mul_comm (2:ℚ) (phaseBase:ℚ)]

private def phaseFromTicks (ticks : ℕ) : Rect :=
  let half := dottieFastImaginaryExpBox (halfPhaseFromTicks ticks)
  (half.mul half).pad (1/10^13)

private theorem phaseFromTicks_eq (n : ℕ) :
    phaseFromTicks (dottieCachedLogLowerTicks n) = momentPhaseBox n := by
  unfold phaseFromTicks momentPhaseBox
  rw [dottie_fast_imaginary_exp_eq, halfPhaseFromTicks_eq]

private def fastMomentColumn (inverse power : Interval) (phase : Rect) (k : ℕ) : ℤ × ℤ :=
  let box := ((inverse.mul power).mul (dottieCachedFactorialInterval k)).scaleBy phase
  (box.re.midpointTicks,box.im.midpointTicks)

private theorem fastMomentColumn_eq (inverse power : Interval) (phase : Rect) (k : ℕ) :
    fastMomentColumn inverse power phase k = momentColumn inverse power phase k := by
  simp only [fastMomentColumn, momentColumn, dottie_cached_factorial_interval_eq]

private def fastMomentColumns (inverse logBox : Interval) (phase : Rect) :
    ℕ → ℕ → Interval → List (ℤ × ℤ)
  | 0, _, _ => []
  | width+1, degree, power =>
    fastMomentColumn inverse power phase degree ::
      fastMomentColumns inverse logBox phase width (degree+1) (power.mul logBox)

private theorem fastMomentColumns_eq (inverse logBox : Interval) (phase : Rect)
    (width degree : ℕ) (power : Interval) :
    fastMomentColumns inverse logBox phase width degree power =
      momentColumns inverse logBox phase width degree power := by
  induction width generalizing degree power with
  | zero => rfl
  | succ width ih => simp only [fastMomentColumns, momentColumns, fastMomentColumn_eq, ih]

/-- Compute both normalized logarithm and phase from the same cached integer log ticks. -/
def dottieFastJointMomentWeightTicks (n width : ℕ) : List (ℤ × ℤ) :=
  let ticks := dottieCachedLogLowerTicks n
  let logBox := normalizedLogFromTicks ticks
  fastMomentColumns (inverseSqrtBox n) logBox (phaseFromTicks ticks) width 0 (Interval.power logBox 0)

theorem dottie_fast_joint_moment_weight_eq (n width : ℕ) :
    dottieFastJointMomentWeightTicks n width = dottieJointMomentWeightTicks n width := by
  simp only [dottieFastJointMomentWeightTicks, dottieJointMomentWeightTicks,
    fastMomentColumns_eq, normalizedLogFromTicks_eq n, phaseFromTicks_eq n]

private def fastAdd (sign : ℤ) (n width : ℕ) (total : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  if sign = 0 then total
  else List.zipWith (fun x y => (x.1 + sign*y.1, x.2 + sign*y.2)) total
    (dottieFastJointMomentWeightTicks n width)

private def fastFold (a width : ℕ) : ℕ → ℕ → ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, _, _, total => total
  | len+1, b, packed, total =>
    fastFold a width len (b+1) (packed/signRadix)
      (fastAdd (readPairSign packed) ((a+1)^2+(b+1)^2) width total)

private theorem fastFold_eq (a width len lo signs : ℕ) (total : List (ℤ × ℤ)) :
    fastFold a width len lo signs total = jointMomentFold a width len lo signs total := by
  induction len generalizing lo signs total with
  | zero => rfl
  | succ len ih =>
    simp only [fastFold, jointMomentFold, ih, fastAdd, addMomentPair,
      dottie_fast_joint_moment_weight_eq]

/-- Evaluate an entire joint moment block using the cached integer phase path. -/
def dottieFastJointMomentBlock (width a lo len signs : ℕ) : List (ℤ × ℤ) :=
  fastFold a width len lo signs (List.replicate width (0,0))

theorem dottie_fast_joint_moment_block_eq (width a lo len signs : ℕ) :
    dottieFastJointMomentBlock width a lo len signs = dottieJointMomentBlock width a lo len signs :=
  fastFold_eq a width len lo signs _

#print axioms dottie_fast_joint_moment_weight_eq
#print axioms dottie_fast_joint_moment_block_eq

end QuarticModel.DottieFixedIntervals
