import DottieCertifiedPairSigns
import DottieNormalizedMomentScore

/-! Evaluate the real and imaginary moment ticks together on a certified sign block. -/

namespace QuarticModel.DottieFixedIntervals

open private inverseSqrtBox normalizedLogBox Interval.power momentPhaseBox
  from DottieFixedMomentWeights
open private signRadix readPairSign foldPairSigns from DottieCertifiedPairSigns
open private applyPairedWeight applyPairedWeight_eq from DottieStructuralPairBlocks

set_option autoImplicit false
set_option maxHeartbeats 1000000

private def momentColumn (inverse power : Interval) (phase : Rect) (k : ℕ) : ℤ × ℤ :=
  let factor : ℚ := 1 / (k.factorial : ℚ)
  let box := ((inverse.mul power).mul (Interval.rational factor factor)).scaleBy phase
  (box.re.midpointTicks, box.im.midpointTicks)

private def momentColumns (inverse logBox : Interval) (phase : Rect) :
    ℕ → ℕ → Interval → List (ℤ × ℤ)
  | 0, _, _ => []
  | width+1, degree, power =>
    momentColumn inverse power phase degree ::
      momentColumns inverse logBox phase width (degree+1) (power.mul logBox)

private theorem momentColumns_length (inverse logBox : Interval) (phase : Rect)
    (width degree : ℕ) (power : Interval) :
    (momentColumns inverse logBox phase width degree power).length = width := by
  induction width generalizing degree power with
  | zero => rfl
  | succ width ih => simp only [momentColumns, List.length_cons, ih]

private theorem momentColumns_getD (inverse logBox : Interval) (phase : Rect)
    (width degree k : ℕ) (hk : k < width) :
    (momentColumns inverse logBox phase width degree (Interval.power logBox degree)).getD k (0,0) =
      momentColumn inverse (Interval.power logBox (degree+k)) phase (degree+k) := by
  induction width generalizing degree k with
  | zero => omega
  | succ width ih =>
    cases k with
    | zero => simp only [momentColumns, List.getD_cons_zero, Nat.add_zero]
    | succ k =>
      have h := ih (degree+1) k (by omega)
      simpa only [momentColumns, List.getD_cons_succ, Interval.power,
        show degree+1+k = degree+(k+1) by omega] using h

/-- Compute the shared inverse square root, logarithm, and phase before advancing the degrees. -/
def dottieJointMomentWeightTicks (n width : ℕ) : List (ℤ × ℤ) :=
  let logBox := normalizedLogBox n
  momentColumns (inverseSqrtBox n) logBox (momentPhaseBox n) width 0 (Interval.power logBox 0)

private theorem dottieJointMomentWeightTicks_length (n width : ℕ) :
    (dottieJointMomentWeightTicks n width).length = width :=
  momentColumns_length _ _ _ _ _ _

theorem dottie_joint_moment_weights_getD (n : ℕ) {width k : ℕ} (hk : k < width) :
    (dottieJointMomentWeightTicks n width).getD k (0,0) =
      (momentWeightRealTicks n k, momentWeightImagTicks n k) := by
  simpa only [dottieJointMomentWeightTicks, Nat.zero_add, momentColumn,
    momentWeightRealTicks, momentWeightImagTicks, normalizedMomentWeightBox] using
    momentColumns_getD (inverseSqrtBox n) (normalizedLogBox n) (momentPhaseBox n) width 0 k hk

private def addMomentPair (sign : ℤ) (n width : ℕ) (total : List (ℤ × ℤ)) :
    List (ℤ × ℤ) :=
  if sign = 0 then total
  else List.zipWith (fun x y => (x.1 + sign*y.1, x.2 + sign*y.2)) total
    (dottieJointMomentWeightTicks n width)

private theorem addMomentPair_length (sign : ℤ) (n width : ℕ) (total : List (ℤ × ℤ))
    (hTotal : total.length = width) :
    (addMomentPair sign n width total).length = width := by
  by_cases h : sign = 0 <;>
    simp only [addMomentPair, h, if_true, if_false, List.length_zipWith, hTotal,
      dottieJointMomentWeightTicks_length, min_self]

private theorem addMomentPair_getD (sign : ℤ) (n width : ℕ) (total : List (ℤ × ℤ))
    (hTotal : total.length = width) {k : ℕ} (hk : k < width) :
    (addMomentPair sign n width total).getD k (0,0) =
      ((total.getD k (0,0)).1 + applyPairedWeight sign (fun () => momentWeightRealTicks n k),
       (total.getD k (0,0)).2 + applyPairedWeight sign (fun () => momentWeightImagTicks n k)) := by
  by_cases hz : sign = 0
  · simp [addMomentPair, applyPairedWeight_eq, hz]
  · rw [addMomentPair, if_neg hz, applyPairedWeight_eq, applyPairedWeight_eq, if_neg hz, if_neg hz]
    have hOut : k < (List.zipWith (fun (x y : ℤ × ℤ) => (x.1 + sign*y.1, x.2 + sign*y.2)) total
        (dottieJointMomentWeightTicks n width)).length := by
      simpa only [List.length_zipWith, hTotal, dottieJointMomentWeightTicks_length, min_self] using hk
    rw [← List.getElem_eq_getD (h := hOut) (0,0), List.getElem_zipWith]
    have ht : k < total.length := by simpa only [hTotal] using hk
    have hw : k < (dottieJointMomentWeightTicks n width).length := by
      simpa only [dottieJointMomentWeightTicks_length] using hk
    rw [List.getElem_eq_getD (h := ht) (0,0), List.getElem_eq_getD (h := hw) (0,0),
      dottie_joint_moment_weights_getD n hk]

private def jointMomentFold (a width : ℕ) : ℕ → ℕ → ℕ → List (ℤ × ℤ) → List (ℤ × ℤ)
  | 0, _, _, total => total
  | len+1, b, packed, total =>
    jointMomentFold a width len (b+1) (packed/signRadix)
      (addMomentPair (readPairSign packed) ((a+1)^2+(b+1)^2) width total)

private theorem jointMomentFold_getD (a width len b packed : ℕ) (total : List (ℤ × ℤ))
    (hTotal : total.length = width) {k : ℕ} (hk : k < width) :
    (jointMomentFold a width len b packed total).getD k (0,0) =
      (foldPairSigns (fun n => momentWeightRealTicks n k) a len b packed (total.getD k (0,0)).1,
       foldPairSigns (fun n => momentWeightImagTicks n k) a len b packed (total.getD k (0,0)).2) := by
  induction len generalizing b packed total with
  | zero => rfl
  | succ len ih =>
    simp only [jointMomentFold, foldPairSigns, ih _ _ _ (addMomentPair_length _ _ _ _ hTotal),
      addMomentPair_getD _ _ _ _ hTotal hk]

/-- Accumulate all requested moment tick pairs while traversing the compact Gaussian signs once. -/
def dottieJointMomentBlock (width a lo len signs : ℕ) : List (ℤ × ℤ) :=
  jointMomentFold a width len lo signs (List.replicate width (0,0))

theorem dottie_joint_moment_block_getD (a lo len signs : ℕ) {width k : ℕ} (hk : k < width) :
    (dottieJointMomentBlock width a lo len signs).getD k (0,0) =
      (dottiePackedPairSignBlock (fun n => momentWeightRealTicks n k) a lo len signs,
       dottiePackedPairSignBlock (fun n => momentWeightImagTicks n k) a lo len signs) := by
  have hZero : (List.replicate width ((0,0) : ℤ × ℤ)).getD k (0,0) = (0,0) :=
    List.getD_replicate (0,0) hk
  simp only [dottieJointMomentBlock, jointMomentFold_getD _ _ _ _ _ _ List.length_replicate hk,
    hZero, dottiePackedPairSignBlock]

#print axioms dottie_joint_moment_weights_getD
#print axioms dottie_joint_moment_block_getD

end QuarticModel.DottieFixedIntervals
