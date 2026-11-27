import DottieJointMomentScore

namespace QuarticModel.DottieFixedIntervals

open private rowLimit axisTerm positiveTerm positiveSign positiveNorm from DottieSymmetricScore
open private addMomentPair addMomentPair_length addMomentPair_getD from DottieJointMomentScore
open private applyPairedWeight applyPairedWeight_eq from DottieStructuralPairBlocks

set_option autoImplicit false

private theorem applyPairedWeight_mul (s z : ℤ) :
    applyPairedWeight s (fun () => z) = s*z := by
  by_cases h : s = 0 <;> simp [applyPairedWeight_eq, h]

private def jointMomentAxis (width a : ℕ) : List (ℤ × ℤ) :=
  addMomentPair (dottieRowSign ((a : ℤ)+1) 0) ((a+1)^2) width (List.replicate width (0,0))

private theorem jointMomentAxis_length (width a : ℕ) :
    (jointMomentAxis width a).length = width :=
  addMomentPair_length _ _ _ _ List.length_replicate

private theorem jointMomentAxis_getD (width a : ℕ) {k : ℕ} (hk : k < width) :
    (jointMomentAxis width a).getD k (0,0) =
      (axisTerm (fun n => momentWeightRealTicks n k) a,
       axisTerm (fun n => momentWeightImagTicks n k) a) := by
  have hZero : (List.replicate width ((0,0) : ℤ × ℤ)).getD k (0,0) = (0,0) :=
    List.getD_replicate (0,0) hk
  simp only [jointMomentAxis, addMomentPair_getD _ _ _ _ List.length_replicate hk,
    hZero, applyPairedWeight_mul, zero_add, axisTerm]

/-- The axis and the diagonal, when present, are counted once in every column. -/
def dottieJointMomentRowHead (width N a : ℕ) : List (ℤ × ℤ) :=
  let axis := jointMomentAxis width a
  if a < rowLimit N a then
    addMomentPair (dottieRowSign ((a : ℤ)+1) ((a : ℤ)+1)) ((a+1)^2+(a+1)^2) width axis
  else axis

theorem dottie_joint_moment_row_head_length (width N a : ℕ) :
    (dottieJointMomentRowHead width N a).length = width := by
  unfold dottieJointMomentRowHead
  dsimp only
  split
  · exact addMomentPair_length _ _ _ _ (jointMomentAxis_length width a)
  · exact jointMomentAxis_length width a

theorem dottie_joint_moment_row_head_getD (width N a : ℕ) {k : ℕ} (hk : k < width) :
    (dottieJointMomentRowHead width N a).getD k (0,0) =
      (dottiePairRowHead N (fun n => momentWeightRealTicks n k) a,
       dottiePairRowHead N (fun n => momentWeightImagTicks n k) a) := by
  by_cases h : a < rowLimit N a
  · simp only [dottieJointMomentRowHead, if_pos h,
      addMomentPair_getD _ _ _ _ (jointMomentAxis_length width a) hk,
      jointMomentAxis_getD width a hk, applyPairedWeight_mul,
      dottiePairRowHead, positiveTerm, positiveSign, positiveNorm]
  · simp only [dottieJointMomentRowHead, if_neg h, jointMomentAxis_getD width a hk,
      dottiePairRowHead, add_zero]

/-- Add tables of real and imaginary ticks column by column. -/
def dottieMomentTicksAdd (left right : List (ℤ × ℤ)) : List (ℤ × ℤ) :=
  List.zipWith (fun x y => (x.1+y.1, x.2+y.2)) left right

theorem dottie_moment_ticks_add_getD (left right : List (ℤ × ℤ)) {k : ℕ}
    (hLeft : k < left.length) (hRight : k < right.length) :
    (dottieMomentTicksAdd left right).getD k (0,0) =
      ((left.getD k (0,0)).1+(right.getD k (0,0)).1,
       (left.getD k (0,0)).2+(right.getD k (0,0)).2) := by
  have hOut : k < (List.zipWith (fun (x y : ℤ × ℤ) => (x.1+y.1, x.2+y.2)) left right).length := by
    rw [List.length_zipWith, Nat.lt_min]
    exact ⟨hLeft,hRight⟩
  rw [dottieMomentTicksAdd, ← List.getElem_eq_getD (h := hOut) (0,0), List.getElem_zipWith,
    List.getElem_eq_getD (h := hLeft) (0,0), List.getElem_eq_getD (h := hRight) (0,0)]

/-- Adjoin the checked head to all of a row's off-diagonal pairs. -/
theorem dottie_joint_moment_row_getD (width N a : ℕ) (body : List (ℤ × ℤ))
    (hLength : body.length = width) {k : ℕ} (hk : k < width)
    (hBody : body.getD k (0,0) =
      (dottiePairRowBlock (fun n => momentWeightRealTicks n k) a 0 (dottiePairRowSize N a),
       dottiePairRowBlock (fun n => momentWeightImagTicks n k) a 0 (dottiePairRowSize N a))) :
    (dottieMomentTicksAdd (dottieJointMomentRowHead width N a) body).getD k (0,0) =
      (dottiePairedRowSpan N (fun n => momentWeightRealTicks n k) a 1,
       dottiePairedRowSpan N (fun n => momentWeightImagTicks n k) a 1) := by
  have hLeft : k < (dottieJointMomentRowHead width N a).length := by
    simpa only [dottie_joint_moment_row_head_length] using hk
  have hRight : k < body.length := by simpa only [hLength] using hk
  rw [dottie_moment_ticks_add_getD _ _ hLeft hRight, dottie_joint_moment_row_head_getD _ _ _ hk,
    hBody, dottiePairedRowSpan_one, dottiePairedRowSpan_one]

/-- Add the certified tables of two adjacent ranges of complete rows. -/
theorem dottie_joint_moment_span_add (N lo leftLen rightLen : ℕ)
    (left right : List (ℤ × ℤ)) {k : ℕ} (hkLeft : k < left.length) (hkRight : k < right.length)
    (hLeft : left.getD k (0,0) =
      (dottiePairedRowSpan N (fun n => momentWeightRealTicks n k) lo leftLen,
       dottiePairedRowSpan N (fun n => momentWeightImagTicks n k) lo leftLen))
    (hRight : right.getD k (0,0) =
      (dottiePairedRowSpan N (fun n => momentWeightRealTicks n k) (lo+leftLen) rightLen,
       dottiePairedRowSpan N (fun n => momentWeightImagTicks n k) (lo+leftLen) rightLen)) :
    (dottieMomentTicksAdd left right).getD k (0,0) =
      (dottiePairedRowSpan N (fun n => momentWeightRealTicks n k) lo (leftLen+rightLen),
       dottiePairedRowSpan N (fun n => momentWeightImagTicks n k) lo (leftLen+rightLen)) := by
  rw [dottie_moment_ticks_add_getD _ _ hkLeft hkRight, hLeft, hRight,
    dottiePairedRowSpan_add, dottiePairedRowSpan_add]

#print axioms dottie_joint_moment_row_head_getD
#print axioms dottie_joint_moment_row_getD
#print axioms dottie_joint_moment_span_add

end QuarticModel.DottieFixedIntervals
